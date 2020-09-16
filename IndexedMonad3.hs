{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE GADTs, PolyKinds, KindSignatures, DataKinds, TypeOperators, RankNTypes, ScopedTypeVariables, FlexibleInstances, RecordWildCards, TypeFamilies, UndecidableInstances #-}

module IndexedMonad3 where

import Data.Kind
import Control.Lens

data Prompt sfd = Prompt sfd Type Type [Type] (Prompts sfd) (Prompts sfd)
type Prompts sfd = [Prompt sfd]

data Cont dfd r (rs :: [Type]) (ps1 :: Prompts sfd) (ps2 :: Prompts sfd) a

instance Functor (Cont dfd r rs ps ps) where
instance Applicative (Cont dfd r rs ps ps) where
instance Monad (Cont dfd r rs ps ps) where

inFrame ::
	dfd ('Prompt sd rt jt rs rps jps) ->
	(rt -> Cont dfd r rs rps ps2 a) ->
	(jt -> Cont dfd r rs jps ps2 a) ->
	Cont dfd r (rt ': rs) ('Prompt sd rt jt rs rps jps ': ps1) rps rt ->
	Cont dfd r        rs                                  ps1  ps2 a
inFrame dd rk jk b = undefined

data PromptRef (p :: Prompt sfd) (psPre :: Prompts sfd) (psPost :: Prompts sfd) (ps :: Prompts sfd) where
	PRHead :: PromptRef p '[] ps (p ': ps)
	PRTail :: PromptRef p psPre psPost ps -> PromptRef p (p' ': psPre) psPost (p' ': ps)

type family RevOnto (rev :: [a]) (tail :: [a]) :: [a] where
	RevOnto '[] tail = tail
	RevOnto (x ': rev) tail = RevOnto rev (x ': tail)

-- forgetPrompt ::
-- 	PromptRef p psPre1 psPost1 ps1 ->
-- 	PromptRef p psPre2 psPost2 ps2 ->
-- 	Cont dfd r rs (RevOnto psPre1 psPost1) (RevOnto psPre2 psPost2) a ->
-- 	Cont dfd r rs ps1 ps2 a
-- forgetPrompt pr1 pr2 b = undefined

jumpOut ::
	PromptRef ('Prompt sd rt jt rs' rps jps) psPre psPost ps1 ->
	(
		(a -> Cont dfd r (rt ': rs') ps2 rps rt) ->
		Cont dfd r rs' psPost jps jt
	) ->
	Cont dfd r rs ps1 ps2 a
jumpOut pr1 f = undefined
