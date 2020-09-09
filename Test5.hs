{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE GADTs, PolyKinds, KindSignatures, DataKinds, TypeOperators, RankNTypes, ScopedTypeVariables, FlexibleInstances, RecordWildCards, TypeFamilies, UndecidableInstances #-}

module Test4 where

import Data.Kind
import Control.Lens hiding (imap)
import Control.Monad.Indexed

type family RevOnto (rev :: [a]) (tail :: [a]) :: [a] where
	RevOnto '[] tail = tail
	RevOnto (x ': rev) tail = RevOnto rev (x ': tail)

data Prompt sfd = Prompt sfd Type Type [Type] (Prompts sfd) (Prompts sfd)
type Prompts sfd = [Prompt sfd]

data Frames dfd r (rs :: [Type]) (ps :: Prompts sfd) where
	FNil :: Frames dfd r '[] '[]
	FConsPrompt ::
		Frames dfd r        rs                                   ps ->
		Frames dfd r (rt ': rs) ('Prompt sd rt jt rs' rps jps ': ps)
	FConsErased ::
		Frames dfd r        rs  ps ->
		Frames dfd r (rt ': rs) ps
data Cont dfd r (rs :: [Type]) (ps1 :: Prompts sfd) (ps2 :: Prompts sfd) a
	= Cont { runCont :: Frames dfd r rs ps1 -> (a -> Frames dfd r rs ps2 -> r) -> r }

fsTail :: Lens
	(Frames dfd r (p ': ps1))
	(Frames dfd r (p ': ps2))
	(Frames dfd r ps1)
	(Frames dfd r ps2)
fsTail i (FCons f fs) = fmap (FCons f) $ i fs

instance IxFunctor (Cont dfd r rs) where
	imap f a = Cont $ \fs k -> runCont a fs $ k . f
instance IxPointed (Cont dfd r rs) where
	ireturn a = Cont $ \fs k -> k a fs
instance IxApplicative (Cont dfd r rs) where
	iap f a = Cont $ \fs k ->
		runCont f fs $ \f fs ->
		runCont a fs $ \a fs ->
		k (f a) fs
instance IxMonad (Cont dfd r rs) where
	ibind f a = Cont $ \fs k ->
		runCont a fs $ \a fs ->
		runCont (f a) fs k
instance Functor (Cont dfd r rs ps ps) where
	fmap = imap
instance Applicative (Cont dfd r rs ps ps) where
	pure = ireturn
	(<*>) = iap
instance Monad (Cont dfd r rs ps ps) where
	(>>=) = flip ibind

inFrame ::
	dfd ('Prompt sd rt jt rs rps jps) ->
	(rt -> Cont dfd r rs rps ps2 a) ->
	(jt -> Cont dfd r rs jps ps2 a) ->
	Cont dfd r (rt ': rs) ('Prompt sd rt jt rs rps jps ': ps1) rps rt ->
	Cont dfd r        rs                                  ps1  ps2 a
inFrame dd rk jk b =
	Cont $ \fs ka -> runCont b
		(FConsPrompt fs)
		(\rv (FConsPrompt fs) -> error "TODO")

data PromptRef (p :: Prompt sfd) (psPre :: Prompts sfd) (psPost :: Prompts sfd) (ps :: Prompts sfd) where
	PRHead :: PromptRef p '[] ps (p ': ps)
	PRTail :: PromptRef p psPre psPost ps -> PromptRef p (p' ': psPre) psPost (p' ': ps)

prPostFs :: PromptRef p psPre psPost ps -> Lens'
	(Frames dfd r ps)
	(Frames dfd r (p ': psPost))
prPostFs PRHead = id
prPostFs (PRTail pr) = fsTail . prPostFs pr

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
jumpOut pr1 f =
	Cont $ \fs ka -> runCont
		(f $ \a -> _)
		(fs^.prPostFs pr1.fsTail)
		_
