{-# OPTIONS_GHC -Wno-tabs #-}

module Machine1 where

import Debug.Trace

data Term
	= TVar Int
	| TLam Term
	| TAp Term Term
	| TPlHl String
	| TPrompt String Term
	| TControl String Term
	| TLog Term
	deriving (Show)

data Value
	= VPlHl String [Value]
	| VEnv [Value]
	| VLam [Instr] [Value]
	| VCont [Instr] [Value] [Frame]
	deriving (Show)

data Instr
	= IPlHl String
	| IVar Int
	| ILam [Instr]
	| IDup | ISwap
	| ICall
	| IPrompt String [Instr]
	| IControl String [Instr]
	| ILog
	deriving (Show)

compile :: Term -> [Instr]
compile (TVar v) = [IVar v]
compile (TLam b) = [ILam (compile b)]
compile (TAp f a) = [IDup] ++ compile f ++ [ISwap] ++ compile a ++ [ICall]
compile (TPlHl n) = [IPlHl n]
compile (TPrompt n b) = [IPrompt n (compile b)]
compile (TControl n b) = [IControl n (compile b)]
compile (TLog a) = compile a ++ [ILog]

data Frame = Frame {
	fName :: Maybe String,
	fCode :: [Instr],
	fStack :: [Value]
} deriving (Show)

run :: Applicative m => [Instr] -> [Value] -> [Frame] -> m Value
run c s ks = traceShowM (c, s, ks) *> run' c s ks
run' :: Applicative m => [Instr] -> [Value] -> [Frame] -> m Value
run' [] [v] (f:ks) = run (fCode f) (v:fStack f) ks
run' [] [v] [] = pure v
run' (IPlHl n:c) (VEnv _:s) ks = run c (VPlHl n []:s) ks
run' (IVar v:c) (VEnv vs:s) ks = run c (vs!!v:s) ks
run' (ILam b:c) (VEnv vs:s) ks = run c (VLam b vs:s) ks
run' (IDup:c) (v:s) ks = run c (v:v:s) ks
run' (ISwap:c) (a:b:s) ks = run c (b:a:s) ks
run' (ICall:c) (a:f:s) ks = case f of
	VPlHl n as -> run c (VPlHl n (a:as):s) ks
	VLam b vs -> run (b ++ c) (VEnv (a:vs):s) ks
	VCont c' s' ks' -> let f = Frame {
			fName = Nothing,
			fCode = c,
			fStack = s
		} in run c' (a:s') (ks' ++ [f] ++ ks)
run' (IPrompt n b:c) (VEnv vs:s) ks = run b [VEnv vs] (f:ks)
	where f = Frame {
			fName = Just n,
			fCode = c,
			fStack = s
		}
run' (IControl n b:c) (VEnv vs:s) ks = run (b ++ fCode f) (VEnv (k:vs):fStack f) kso
	where
		(ksi, f:kso) = break ((== Just n) . fName) ks
		k = VCont c s ksi
run' (ILog:c) (v:s) ks = traceShowM v *> run c (v:s) ks

prompt' :: String -> Term -> Term -> Term -> Term
-- either (prompt. Left b) r j
-- (prompt. (λv. λr. λj. r v) <b>) (λv. <r>) (λv. <j>)
prompt' n b r j = TPrompt n b' `TAp` TLam r `TAp` TLam j
	-- (λv. λr. λj. r v) <b>
	where b' = flip TAp b $ TLam $ TLam $ TLam $ TVar 1 `TAp` TVar 2

control' :: String -> Term -> Term
-- control k. Right $ b $ λa. either (k a) id (λv. error "bad")
-- control k. (λv. λr. λj. j v) ((λk'. <b>) (λa. k a (λv. v) (λv. plhl"bad" v)))
control' n b = TControl n $
	TAp (TLam $ TLam $ TLam $ TVar 0 `TAp` TVar 2) $
	TAp (TLam b) $
	TLam $
		TVar 1 `TAp` TVar 0 `TAp` TLam (TVar 0) `TAp` TPlHl "bad"

-- testp = TPrompt "foo" $ TAp (TPlHl "hi") $ TControl "foo" $ TVar 0
testp = prompt' "foo"
	(TAp (TPlHl "hi") $ control' "foo" $ TVar 0)
	(TPlHl "ret" `TAp` TVar 0)
	(TPlHl "jmp" `TAp` TVar 0)

-- VPlHl "jmp" [
-- 	VLam
-- 		[
-- 			IDup,
-- 				IDup,
-- 					IDup,
-- 						IVar 1,
-- 					ISwap,
-- 						IVar 0,
-- 					ICall,
-- 				ISwap,
-- 					ILam [IVar 0],
-- 				ICall,
-- 			ISwap,
-- 				IPlHl "bad",
-- 			ICall
-- 		]
-- 		[
-- 			VCont
-- 				[
-- 						ICall,
-- 					ICall
-- 				]
-- 				[
-- 					VPlHl "hi" [],
-- 					VLam
-- 						[
-- 							ILam [
-- 								ILam [
-- 									IDup,
-- 										IVar 1,
-- 									ISwap,
-- 										IVar 2,
-- 									ICall
-- 								]
-- 							]
-- 						]
-- 						[]
-- 				]
-- 				[]
-- 		]
-- ]
-- plhl"bad" $ λa. (Λa. (λv. λr. λj. r v) (plhl"hi" a)) a id plhl"bad"
