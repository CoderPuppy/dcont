{-# OPTIONS_GHC -Wno-tabs #-}

module Machine2 where

import Numeric.Natural

data Term
	= Var Int
	| Lam Term
	| App Term Term
	| Prompt Term
	| Control Int Term
instance Show Term where
	showsPrec d (Var v) = showString "ʌ" . shows v
	showsPrec d (Lam b) = showParen (d > 0) $ showString "λ. " . shows b
	showsPrec d (App f a) = showParen (d > 10) $ showsPrec 11 f . showString " " . showsPrec 11 a
	showsPrec d (Prompt b) = showParen (d > 0) $ showString "prompt. " . shows b
	showsPrec d (Control i b) = showParen (d > 0) $ showString "control " . shows i . showString ". " . shows b

class Encode a where
	encode :: a -> Term
instance Encode Natural where
	encode n = Lam $ Lam $ go n
		where
			go 0 = Var 1
			go n = App (Var 0) (go (n - 1))
instance Encode a => Encode [a] where
	encode [] = Lam $ Lam $ Var 1
	encode (h:t) = Lam $ Lam $ Var 0 `App` encode h `App` encode t

testp = Prompt $ encode (0 :: Natural) `App` Control 0 (Var 0) `App` Lam (Var 0)

data Value
	= VFun (K -> Value -> Value)
	| VCont K
data KP = KP (K -> Value -> Value)
type K = [KP]

evalkp :: KP -> K -> Value -> Value
evalkp (KP kp) k v = kp k v

evalk :: K -> Value -> Value
evalk (kp:k) v = evalkp kp k v

eval :: Term -> [Value] -> K -> Value
eval (Var v) vs k = evalk k (vs !! v)
eval (Lam b) vs k = evalk k $ VFun $ \k a -> eval b (a:vs) k
eval (App f a) vs (kp:k) =
	eval f vs $ (:k) $ KP $ \k f ->
	eval a vs $ (:k) $ KP $ \k a ->
	case f of
		VFun f -> f (kp:k) a
		VCont k' -> evalk (k' ++ kp:k) a
eval (Prompt b) vs k = eval b vs (KP evalk:k)
eval (Control i b) vs k = eval b (VCont ki:vs) (kp:ko)
	where (ki, kp:ko) = splitAt (i + 1) k

-- defunctionalization
data Value1
	= VFun1 (K1 -> Value1 -> Value1)
	| VCont1 K1
data KP1
	= KP01
	| KPAppF1 Term [Value1] KP1
	| KPAppA1 Value1 KP1
type K1 = [KP1]

evalkp1 :: KP1 -> K1 -> Value1 -> Value1
evalkp1 KP01 [] v = v
evalkp1 KP01 (kp:k) v = evalkp1 kp k v
evalkp1 (KPAppF1 a vs kp) k f = compile1 a vs (KPAppA1 f kp:k)
evalkp1 (KPAppA1 f kp) k a = case f of
	VFun1 f -> f (kp:k) a
	VCont1 k' -> evalk1 (k' ++ kp:k) a

evalk1 :: K1 -> Value1 -> Value1
evalk1 (kp:k) v = evalkp1 kp k v
evalk1 [] _ = error "bad"

compile1 :: Term -> [Value1] -> K1 -> Value1
compile1 (Var v) vs k = evalk1 k (vs !! v)
compile1 (Lam b) vs k = evalk1 k $ VFun1 $ \k a -> compile1 b (a:vs) k
compile1 (App f a) vs (kp:k) = compile1 f vs (KPAppF1 a vs kp:k)
compile1 (Prompt b) vs k = compile1 b vs (KP01:k)
compile1 (Control i b) vs k = compile1 b (VCont1 ki:vs) (kp:ko)
	where (ki, kp:ko) = splitAt (i + 1) k
compile1 _ _ [] = error "bad"

-- linearization
data Value2
	= VFun2 (K2 -> Value2 -> Value2)
	| VCont2 K2
data KPP2
	= KPPAppF2 Term [Value2]
	| KPPAppA2 Value2
type KP2 = [KPP2]
type K2 = [KP2]

evalkp2 :: KP2 -> K2 -> Value2 -> Value2
evalkp2 [] [] v = v
evalkp2 [] (kp:k) v = evalkp2 kp k v
evalkp2 (KPPAppF2 a vs:kp) k f = compile2 a vs ((KPPAppA2 f:kp):k)
evalkp2 (KPPAppA2 f:kp) k a = case f of
	VFun2 f -> f (kp:k) a
	VCont2 k' -> evalk2 (k' ++ kp:k) a

evalk2 :: K2 -> Value2 -> Value2
evalk2 (kp:k) v = evalkp2 kp k v
evalk2 [] _ = error "bad"

compile2 :: Term -> [Value2] -> K2 -> Value2
compile2 (Var v) vs k = evalk2 k (vs !! v)
compile2 (Lam b) vs k = evalk2 k $ VFun2 $ \k a -> compile2 b (a:vs) k
compile2 (App f a) vs (kp:k) = compile2 f vs ((KPPAppF2 a vs:kp):k)
compile2 (Prompt b) vs k = compile2 b vs ([]:k)
compile2 (Control i b) vs k = compile2 b (VCont2 ki:vs) (kp:ko)
	where (ki, kp:ko) = splitAt (i + 1) k
compile2 _ _ [] = error "bad"

-- stack extraction
data Value3
	= VFun3 (K3 -> Value3 -> Value3)
	| VCont3 K3
	| VEnv3 [Value3]
data KPP3
	= KPPAppF3 Term
	| KPPAppA3
data KP3 = KP3 [KPP3] [Value3]
type K3 = [KP3]

evalkp3 :: KP3 -> K3 -> Value3 -> Value3
evalkp3 (KP3 [] _) [] v = v
evalkp3 (KP3 [] s) (kp:k) v = evalkp3 kp k v
evalkp3 (KP3 (KPPAppF3 a:kpps) (VEnv3 vs:s)) k f = compile3 a vs (KP3 (KPPAppA3:kpps) (f:s):k)
evalkp3 (KP3 (KPPAppA3:kpps) (f:s)) k a = case f of
	VFun3 f -> f (KP3 kpps s:k) a
	VCont3 k' -> evalk3 (k' ++ KP3 kpps s:k) a

evalk3 :: K3 -> Value3 -> Value3
evalk3 (kp:k) v = evalkp3 kp k v
evalk3 [] _ = error "bad"

compile3 :: Term -> [Value3] -> K3 -> Value3
compile3 (Var v) vs k = evalk3 k (vs !! v)
compile3 (Lam b) vs k = evalk3 k (VFun3 $ \k a -> compile3 b (a:vs) k)
compile3 (App f a) vs (KP3 kp s:k) = compile3 f vs (KP3 (KPPAppF3 a:kp) (VEnv3 vs:s):k)
compile3 (Prompt b) vs k = compile3 b vs (KP3 [] []:k)
compile3 (Control i b) vs k = compile3 b (VCont3 ki:vs) (kp:ko)
	where (ki, kp:ko) = splitAt (i + 1) k
compile3 _ _ [] = error "bad"

-- delinearization
data Value4
	= VFun4 (K4 -> Value4 -> Value4)
	| VCont4 K4
	| VEnv4 [Value4]
data KPP4
	= KPP04
	| KPPAppF4 Term KPP4
	| KPPAppA4 KPP4
data KP4 = KP4 KPP4 [Value4]
type K4 = [KP4]

evalkp4 :: KP4 -> K4 -> Value4 -> Value4
evalkp4 (KP4 KPP04 _) [] v = v
evalkp4 (KP4 KPP04 s) (kp:k) v = evalkp4 kp k v
evalkp4 (KP4 (KPPAppF4 a kpp) (VEnv4 vs:s)) k f = compile4 a vs (KP4 (KPPAppA4 kpp) (f:s):k)
evalkp4 (KP4 (KPPAppA4 kpp) (f:s)) k a = case f of
	VFun4 f -> f (KP4 kpp s:k) a
	VCont4 k' -> evalk4 (k' ++ KP4 kpp s:k) a

evalk4 :: K4 -> Value4 -> Value4
evalk4 (kp:k) v = evalkp4 kp k v
evalk4 [] _ = error "bad"

compile4 :: Term -> [Value4] -> K4 -> Value4
compile4 (Var v) vs k = evalk4 k (vs !! v)
compile4 (Lam b) vs k = evalk4 k (VFun4 $ \k a -> compile4 b (a:vs) k)
compile4 (App f a) vs (KP4 kpp s:k) = compile4 f vs (KP4 (KPPAppF4 a kpp) (VEnv4 vs:s):k)
compile4 (Prompt b) vs k = compile4 b vs (KP4 KPP04 []:k)
compile4 (Control i b) vs k = compile4 b (VCont4 ki:vs) (kp:ko)
	where (ki, kp:ko) = splitAt (i + 1) k
compile4 _ _ [] = error "bad"

-- refunctionalization
data Value5
	= VFun5 (K5 -> Value5 -> Value5)
	| VCont5 K5
	| VEnv5 [Value5]
data KP5 = KP5 ([Value5] -> K5 -> Value5 -> Value5) [Value5]
type K5 = [KP5]

evalkp5 :: KP5 -> K5 -> Value5 -> Value5
evalkp5 (KP5 kpp s) k v = kpp s k v

evalk5 :: K5 -> Value5 -> Value5
evalk5 (kp:k) v = evalkp5 kp k v
evalk5 [] _ = error "bad"

compile5 :: Term -> [Value5] -> K5 -> Value5
compile5 (Var v) vs k = evalk5 k (vs !! v)
compile5 (Lam b) vs k = evalk5 k (VFun5 $ \k a -> compile5 b (a:vs) k)
compile5 (App f a) vs (KP5 kpp s:k) = compile5 f vs (KP5 kpp' (VEnv5 vs:s):k)
	where
		kpp' (VEnv5 vs:s) k f = compile5 a vs (KP5 kpp'' (f:s):k)
		kpp'' (f:s) k a = case f of
			VFun5 f -> f (KP5 kpp s:k) a
			VCont5 k' -> evalk5 (k' ++ KP5 kpp s:k) a
compile5 (Prompt b) vs k = compile5 b vs (KP5 (\_ (kp:k) v -> evalkp5 kp k v) []:k)
compile5 (Control i b) vs k = compile5 b (VCont5 ki:vs) (kp:ko)
	where (ki, kp:ko) = splitAt (i + 1) k
compile5 _ _ [] = error "bad"

-- combine `vs` into `k/head/stack` in `eval`
data Value6
	= VFun6 (K6 -> Value6)
	| VCont6 K6
	| VEnv6 [Value6]
data KP6 = KP6 ([Value6] -> K6 -> Value6) [Value6]
type K6 = [KP6]

evalkp6 :: KP6 -> K6 -> Value6
evalkp6 (KP6 kpp s) k = kpp s k

evalk6 :: K6 -> Value6
evalk6 (kp:k) = evalkp6 kp k
evalk6 [] = error "bad"

compile6 :: Term -> K6 -> Value6
compile6 (Var v) (KP6 kpp (VEnv6 vs:s):k) = evalkp6 (KP6 kpp (vs !! v:s)) k
compile6 (Lam b) (KP6 kpp (VEnv6 vs:s):k) = evalkp6 (KP6 kpp (v:s)) k
	where v = VFun6 $ \(KP6 kpp (a:s):k) -> compile6 b (KP6 kpp (VEnv6 (a:vs):s):k)
compile6 (App f a) (KP6 kpp (VEnv6 vs:s):k) = compile6 f (KP6 kpp' (VEnv6 vs:VEnv6 vs:s):k)
	where
		kpp' (f:VEnv6 vs:s) k = compile6 a (KP6 kpp'' (VEnv6 vs:f:s):k)
		kpp'' (a:f:s) k = case f of
			VFun6 f -> f (KP6 kpp (a:s):k)
			VCont6 (KP6 kpp' s':k') -> evalk6 (KP6 kpp' (a:s'):k' ++ KP6 kpp s:k)
compile6 (Prompt b) (KP6 kpp (VEnv6 vs:s):k) = compile6 b (KP6 (\[v] (KP6 kpp s:k) -> evalkp6 (KP6 kpp (v:s)) k) [VEnv6 vs]:KP6 kpp s:k)
compile6 (Control i b) (KP6 kpp (VEnv6 vs:s):k) = compile6 b (KP6 kpp' (VEnv6 (VCont6 (KP6 kpp s:ki):vs):s'):ko)
	where (ki, KP6 kpp' s':ko) = splitAt i k
compile6 _ [] = error "bad"

-- split `k/head` out in `eval`
data Value7
	= VFun7 (KPP7 -> [Value7] -> K7 -> Value7)
	| VCont7 K7
	| VEnv7 [Value7]
type KPP7 = [Value7] -> K7 -> Value7
data KP7 = KP7 KPP7 [Value7]
type K7 = [KP7]

evalkp7 :: KP7 -> K7 -> Value7
evalkp7 (KP7 kpp s) k = kpp s k

evalk7 :: K7 -> Value7
evalk7 (kp:k) = evalkp7 kp k
evalk7 [] = error "bad"

compile7 :: Term -> KPP7 -> [Value7] -> K7 -> Value7
compile7 (Var v) kpp (VEnv7 vs:s) k = evalkp7 (KP7 kpp (vs !! v:s)) k
compile7 (Lam b) kpp (VEnv7 vs:s) k = evalkp7 (KP7 kpp (v:s)) k
	where v = VFun7 $ \ kpp (a:s) k -> compile7 b kpp (VEnv7 (a:vs):s) k
compile7 (App f a) kpp (VEnv7 vs:s) k = compile7 f kpp' (VEnv7 vs:VEnv7 vs:s) k
	where
		kpp' (f:VEnv7 vs:s) k = compile7 a kpp'' (VEnv7 vs:f:s) k
		kpp'' (a:f:s) k = case f of
			VFun7 f -> f kpp (a:s) k
			VCont7 (KP7 kpp' s':k') -> evalk7 (KP7 kpp' (a:s'):k' ++ KP7 kpp s:k)
compile7 (Prompt b) kpp (VEnv7 vs:s) k = compile7 b (\[v] (KP7 kpp s:k) -> evalkp7 (KP7 kpp (v:s)) k) [VEnv7 vs] (KP7 kpp s:k)
compile7 (Control i b) kpp (VEnv7 vs:s) k = compile7 b kpp' (VEnv7 (VCont7 (KP7 kpp s:ki):vs):s') ko
	where (ki, KP7 kpp' s':ko) = splitAt i k

-- extract psuedo-instructions
data Value8
	= VFun8 Instr8
	| VCont8 K8
	| VEnv8 [Value8]
type KPP8 = [Value8] -> K8 -> Value8
data KP8 = KP8 KPP8 [Value8]
type K8 = [KP8]
type Instr8 = KPP8 -> KPP8

evalkp8 :: KP8 -> K8 -> Value8
evalkp8 (KP8 kpp s) k = kpp s k

evalk8 :: K8 -> Value8
evalk8 (kp:k) = evalkp8 kp k
evalk8 [] = error "bad"

iVar8 :: Int -> Instr8
iVar8 v kpp (VEnv8 vs:s) k = evalkp8 (KP8 kpp (vs !! v:s)) k

iLam8 :: Instr8 -> Instr8
iLam8 b kpp (VEnv8 vs:s) k = evalkp8 (KP8 kpp (v:s)) k
	where v = VFun8 $ \ kpp (a:s) k -> b kpp (VEnv8 (a:vs):s) k

iApp8 :: Instr8 -> Instr8 -> Instr8
iApp8 f a kpp (VEnv8 vs:s) k = f (iAppF8 a kpp) (VEnv8 vs:VEnv8 vs:s) k

iAppF8 :: Instr8 -> KPP8 -> KPP8
iAppF8 a kpp (f:VEnv8 vs:s) k = a (iAppA8 kpp) (VEnv8 vs:f:s) k

iAppA8 :: KPP8 -> KPP8
iAppA8 kpp (a:f:s) k = case f of
	VFun8 f -> f kpp (a:s) k
	VCont8 (KP8 kpp' s':k') -> evalk8 (KP8 kpp' (a:s'):k' ++ KP8 kpp s:k)

iPrompt8 :: Instr8 -> Instr8
iPrompt8 b kpp (VEnv8 vs:s) k = b (\[v] (KP8 kpp s:k) -> evalkp8 (KP8 kpp (v:s)) k) [VEnv8 vs] (KP8 kpp s:k)

iControl8 :: Int -> Instr8 -> Instr8
iControl8 i b kpp (VEnv8 vs:s) k = b kpp' (VEnv8 (VCont8 (KP8 kpp s:ki):vs):s') ko
	where (ki, KP8 kpp' s':ko) = splitAt i k

compile8 :: Term -> Instr8
compile8 (Var v) = iVar8 v
compile8 (Lam b) = iLam8 (compile8 b)
compile8 (App f a) = iApp8 (compile8 f) (compile8 a)
compile8 (Prompt b) = iPrompt8 (compile8 b)
compile8 (Control i b) = iControl8 i (compile8 b)

-- extract instructions
data Value9
	= VFun9 Instr9
	| VCont9 K9
	| VEnv9 [Value9]
type KPP9 = [Value9] -> K9 -> Value9
data KP9 = KP9 KPP9 [Value9]
type K9 = [KP9]
type Instr9 = KPP9 -> KPP9

evalkp9 :: KP9 -> K9 -> Value9
evalkp9 (KP9 kpp s) k = kpp s k

evalk9 :: K9 -> Value9
evalk9 (kp:k) = evalkp9 kp k
evalk9 [] = error "bad"

iseq9 :: Instr9 -> Instr9 -> Instr9
iseq9 a b kpp = a $ b kpp

iVar9 :: Int -> Instr9
iVar9 v kpp (VEnv9 vs:s) k = evalkp9 (KP9 kpp (vs !! v:s)) k

iLam9 :: Instr9 -> Instr9
iLam9 b kpp (VEnv9 vs:s) k = evalkp9 (KP9 kpp (v:s)) k
	where v = VFun9 $ \kpp (a:s) k -> b kpp (VEnv9 (a:vs):s) k

iDupEnv9 :: Instr9
iDupEnv9 kpp (VEnv9 vs:s) k = kpp (VEnv9 vs:VEnv9 vs:s) k

iApp9 :: Instr9 -> Instr9 -> Instr9
iApp9 f a = iDupEnv9 `iseq9` f `iseq9` iAppF9 a
	-- kpp (VEnv9 vs:s) k = f (iAppF9 a kpp) (VEnv9 vs:VEnv9 vs:s) k

iSwapEnv9 :: Instr9
iSwapEnv9 kpp (v:VEnv9 vs:s) k = kpp (VEnv9 vs:v:s) k

iAppF9 :: Instr9 -> Instr9
iAppF9 a = iSwapEnv9 `iseq9` a `iseq9` iCall9
-- iAppF9 a = iseq9 (iseq9 iSwapEnv9 a) iAppA9
-- iAppF9 a kpp = iseq9 iSwapEnv9 a $ iAppA9 kpp
-- iAppF9 a kpp = iSwapEnv9 $ a $ iAppA9 kpp
-- iAppF9 a kpp (v:VEnv9 vs:s) k = a (iAppA9 kpp) (VEnv9 vs:v:s) k
-- iAppF9 a kpp (f:VEnv9 vs:s) k = a (iAppA9 kpp) (VEnv9 vs:f:s) k

iCall9 :: Instr9
iCall9 kpp (a:f:s) k = case f of
	VFun9 f -> f kpp (a:s) k
	VCont9 (KP9 kpp' s':k') -> evalk9 (KP9 kpp' (a:s'):k' ++ KP9 kpp s:k)

iPrompt9 :: Instr9 -> Instr9
iPrompt9 b kpp (VEnv9 vs:s) k = b (\[v] (KP9 kpp s:k) -> evalkp9 (KP9 kpp (v:s)) k) [VEnv9 vs] (KP9 kpp s:k)

iControl9 :: Int -> Instr9 -> Instr9
iControl9 i b kpp (VEnv9 vs:s) k = b kpp' (VEnv9 (VCont9 (KP9 kpp s:ki):vs):s') ko
	where (ki, KP9 kpp' s':ko) = splitAt i k

compile9 :: Term -> Instr9
compile9 (Var v) = iVar9 v
compile9 (Lam b) = iLam9 (compile9 b)
compile9 (App f a) = iApp9 (compile9 f) (compile9 a)
compile9 (Prompt b) = iPrompt9 (compile9 b)
compile9 (Control i b) = iControl9 i (compile9 b)

-- defunctionalize instructions (and linearize something? maybe continuations?)
data Value10
	= VFun10 ([Instr10] -> [Value10] -> K10 -> Value10)
	| VCont10 K10
	| VEnv10 [Value10]
data KP10 = KP10 [Instr10] [Value10]
type K10 = [KP10]
data Instr10
	= ISeq10 Instr10 Instr10
	| IVar10 Int
	| ILam10 Instr10
	| IDupEnv10
	| ISwapEnv10
	| ICall10
	| IPrompt10 Instr10
	| IControl10 Int Instr10

runkpp10 :: [Instr10] -> [Value10] -> K10 -> Value10
runkpp10 (i:kpp) s k = run10 i kpp s k
runkpp10 [] [v] (KP10 kpp s:k) = runkpp10 kpp (v:s) k
runkpp10 [] [v] [] = v

run10 :: Instr10 -> [Instr10] -> [Value10] -> K10 -> Value10
run10 (ISeq10 a b) kpp s k = run10 a (b:kpp) s k
run10 (IVar10 v) kpp (VEnv10 vs:s) k = runkpp10 kpp (vs !! v:s) k
run10 (ILam10 b) kpp (VEnv10 vs:s) k = runkpp10 kpp (v:s) k
	where v = VFun10 $ \kpp (a:s) k -> run10 b kpp (VEnv10 (a:vs):s) k
run10 IDupEnv10 kpp (VEnv10 vs:s) k = runkpp10 kpp (VEnv10 vs:VEnv10 vs:s) k
run10 ISwapEnv10 kpp (v:VEnv10 vs:s) k = runkpp10 kpp (VEnv10 vs:v:s) k
run10 ICall10 kpp (a:f:s) k = case f of
	VFun10 f -> f kpp (a:s) k
	VCont10 (KP10 kpp' s':k') -> runkpp10 kpp' (a:s') (k' ++ KP10 kpp s:k)
run10 (IPrompt10 b) kpp (VEnv10 vs:s) k = run10 b [] [VEnv10 vs] (KP10 kpp s:k)
run10 (IControl10 i b) kpp (VEnv10 vs:s) k = run10 b kpp' (VEnv10 (VCont10 (KP10 kpp s:ki):vs):s') ko
	where (ki, KP10 kpp' s':ko) = splitAt i k

compile10 :: Term -> Instr10
compile10 (Var v) = IVar10 v
compile10 (Lam b) = ILam10 (compile10 b)
compile10 (App f a) = IDupEnv10 `ISeq10` compile10 f `ISeq10` ISwapEnv10 `ISeq10` compile10 a `ISeq10` ICall10
compile10 (Prompt b) = IPrompt10 (compile10 b)
compile10 (Control i b) = IControl10 i (compile10 b)

-- flatten code
data Value11
	= VFun11 ([Instr11] -> [Value11] -> K11 -> Value11) -- this wasn't defunctionalized (for good reasons)
	| VCont11 K11
	| VEnv11 [Value11]
data KP11 = KP11 [Instr11] [Value11]
type K11 = [KP11]
data Instr11
	= IVar11 Int
	| ILam11 [Instr11]
	| IDupEnv11
	| ISwapEnv11
	| ICall11
	| IPrompt11 [Instr11]
	| IControl11 Int [Instr11]

run11 :: [Instr11] -> [Value11] -> K11 -> Value11
run11 [] [v] [] = v
run11 [] [v] (KP11 kpp s:k) = run11 kpp (v:s) k
run11 (IVar11 v:kpp) (VEnv11 vs:s) k = run11 kpp (vs !! v:s) k
run11 (ILam11 b:kpp) (VEnv11 vs:s) k = run11 kpp (v:s) k
	where v = VFun11 $ \kpp (a:s) k -> run11 (b ++ kpp) (VEnv11 (a:vs):s) k
run11 (IDupEnv11:kpp) (VEnv11 vs:s) k = run11 kpp (VEnv11 vs:VEnv11 vs:s) k
run11 (ISwapEnv11:kpp) (v:VEnv11 vs:s) k = run11 kpp (VEnv11 vs:v:s) k
run11 (ICall11:kpp) (a:f:s) k = case f of
	VFun11 f -> f kpp (a:s) k
	VCont11 (KP11 kpp' s':k') -> run11 kpp' (a:s') (k' ++ KP11 kpp s:k)
run11 (IPrompt11 b:kpp) (VEnv11 vs:s) k = run11 b [VEnv11 vs] (KP11 kpp s:k)
run11 (IControl11 i b:kpp) (VEnv11 vs:s) k = run11 (b ++ kpp') (VEnv11 (v:vs):s') ko
	where
		(ki, KP11 kpp' s':ko) = splitAt i k
		v = VCont11 $ KP11 kpp s:ki

compile11 :: Term -> [Instr11]
compile11 (Var v) = [IVar11 v]
compile11 (Lam b) = [ILam11 (compile11 b)]
compile11 (App f a) = [IDupEnv11] ++ compile11 f ++ [ISwapEnv11] ++ compile11 a ++ [ICall11]
compile11 (Prompt b) = [IPrompt11 (compile11 b)]
compile11 (Control i b) = [IControl11 i (compile11 b)]

-- defunctionalize VFun
data Value12
	= VFun12 [Instr12] [Value12]
	| VCont12 K12
	| VEnv12 [Value12]
	deriving (Show)
data KP12 = KP12 [Instr12] [Value12] deriving (Show)
type K12 = [KP12]
data Instr12
	= IVar12 Int
	| ILam12 [Instr12]
	| IDupEnv12
	| ISwapEnv12
	| ICall12
	| IPrompt12 [Instr12]
	| IControl12 Int [Instr12]
	deriving (Show)

run12 :: [Instr12] -> [Value12] -> K12 -> Value12
run12 [] [v] [] = v
run12 [] [v] (KP12 kpp s:k) = run12 kpp (v:s) k
run12 (IVar12 v:kpp) (VEnv12 vs:s) k = run12 kpp (vs !! v:s) k
run12 (ILam12 b:kpp) (VEnv12 vs:s) k = run12 kpp (VFun12 b vs:s) k
run12 (IDupEnv12:kpp) (VEnv12 vs:s) k = run12 kpp (VEnv12 vs:VEnv12 vs:s) k
run12 (ISwapEnv12:kpp) (v:VEnv12 vs:s) k = run12 kpp (VEnv12 vs:v:s) k
run12 (ICall12:kpp) (a:f:s) k = case f of
	VFun12 b vs -> run12 (b ++ kpp) (VEnv12 (a:vs):s) k
	VCont12 (KP12 kpp' s':k') -> run12 kpp' (a:s') (k' ++ KP12 kpp s:k)
run12 (IPrompt12 b:kpp) (VEnv12 vs:s) k = run12 b [VEnv12 vs] (KP12 kpp s:k)
run12 (IControl12 i b:kpp) (VEnv12 vs:s) k = run12 (b ++ kpp') (VEnv12 (v:vs):s') ko
	where
		(ki, KP12 kpp' s':ko) = splitAt i k
		v = VCont12 $ KP12 kpp s:ki

compile12 :: Term -> [Instr12]
compile12 (Var v) = [IVar12 v]
compile12 (Lam b) = [ILam12 (compile12 b)]
compile12 (App f a) = [IDupEnv12] ++ compile12 f ++ [ISwapEnv12] ++ compile12 a ++ [ICall12]
compile12 (Prompt b) = [IPrompt12 (compile12 b)]
compile12 (Control i b) = [IControl12 i (compile12 b)]

eval12 :: Term -> Value12
eval12 t = run12 (compile12 t) [VEnv12 []] []
