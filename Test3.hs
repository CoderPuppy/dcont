{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE GADTs, PolyKinds, KindSignatures, DataKinds, TypeOperators, RankNTypes, ScopedTypeVariables, FlexibleInstances, RecordWildCards #-}

module Test3 where

import Data.Kind
import Control.Lens

data Prompt sfd = Prompt sfd Type Type (Prompts sfd) (Prompts sfd)
type Prompts sfd = [Prompt sfd]

data Frame dfd r (p :: Prompt sfd) where
	Frame :: {
		_fDD :: dfd ('Prompt sd rt jt rps jps),
		_fRet :: rt -> Frames dfd r rps -> r,
		_fJmp :: jt -> Frames dfd r jps -> r
		-- _fEnter :: Cont dfd r ps (),
		-- -- this Bool says if this frame is the target of the jumpOut
		-- _fExit :: Bool -> Cont dfd r ps ()
	} -> Frame dfd r ('Prompt sd rt jt rps jps)
data Frames dfd r (ps :: Prompts sfd) where
	FNil :: Frames dfd r '[]
	FCons ::
		forall dfd r (p :: Prompt sfd) (ps :: Prompts sfd).
		Frame dfd r p -> Frames dfd r ps ->
		Frames dfd r (p ': ps)
newtype Cont dfd r (ps1 :: Prompts sfd) (ps2 :: Prompts sfd) a = Cont {
	runCont :: Frames dfd r ps1 -> (a -> Frames dfd r ps2 -> r) -> r }

fDD :: Lens' (Frame dfd r p) (dfd p)
fDD i (Frame {..}) = fmap (\dd -> Frame { _fDD = dd, .. }) $ i _fDD

fRet :: Lens' (Frame dfd r ('Prompt sd rt jt rps jps)) (rt -> Frames dfd r rps -> r)
fRet i (Frame {..}) = fmap (\ret -> Frame { _fRet = ret, .. }) $ i _fRet

fJmp :: Lens' (Frame dfd r ('Prompt sd rt jt rps jps)) (jt -> Frames dfd r jps -> r)
fJmp i (Frame {..}) = fmap (\jmp -> Frame { _fJmp = jmp, .. }) $ i _fJmp

-- fEnter :: Lens' (Frame dfd r ps sd rt jt) (Cont dfd r ps ())
-- fEnter i f = fmap (\enter -> f { _fEnter = enter }) $ i $ _fEnter f
--
-- fExit :: Lens' (Frame dfd r ps sd rt jt) (Bool -> Cont dfd r ps ())
-- fExit i f = fmap (\exit -> f { _fExit = exit }) $ i $ _fExit f

fsHead :: Lens
	(Frames dfd r (p1 ': ps))
	(Frames dfd r (p2 ': ps))
	(Frame dfd r p1)
	(Frame dfd r p2)
fsHead i (FCons f fs) = fmap (flip FCons fs) $ i f

fsTail :: Lens
	(Frames dfd r (p ': ps1))
	(Frames dfd r (p ': ps2))
	(Frames dfd r ps1)
	(Frames dfd r ps2)
fsTail i (FCons f fs) = fmap (FCons f) $ i fs

instance Functor (Cont dfd r ps ps) where
	fmap f a = Cont $ \fs k -> runCont a fs $ k . f
instance Applicative (Cont dfd r ps ps) where
	pure a = Cont $ \fs k -> k a fs
	f <*> a = Cont $ \fs k ->
		runCont f fs $ \f fs ->
		runCont a fs $ \a fs ->
		k (f a) fs
instance Monad (Cont dfd r ps ps) where
	a >>= f = Cont $ \fs k ->
		runCont a fs $ \a fs ->
		runCont (f a) fs k

inFrame ::
	dfd ('Prompt sd rt jt rps jps) ->
	(rt -> Cont dfd r rps ps2 a) ->
	(jt -> Cont dfd r jps ps2 a) ->
	-- Cont dfd r ps () ->
	-- (Bool -> Cont dfd r ps ()) ->
	Cont dfd r
		('Prompt sd rt jt rps jps ': ps1)
		('Prompt sd rt jt rps jps ': rps)
		rt ->
	Cont dfd r ps1 ps2 a
inFrame dd rk jk b = Cont $ \fs ka -> runCont b
	(flip FCons fs $ Frame {
		_fDD = dd,
		_fRet = \rv fs -> runCont (rk rv) fs ka,
		_fJmp = \jv fs -> runCont (jk jv) fs ka
		-- john sucks drew off-kenny 2020
		-- _fEnter = enter,
		-- _fExit = exit
	})
	(\rv (FCons f fs) -> (f^.fRet) rv fs)

data PromptRef (p :: Prompt sfd) ps' (ps :: Prompts sfd) where
	PRHead :: PromptRef p ps (p ': ps)
	PRTail :: PromptRef p ps' ps -> PromptRef p ps' (p' ': ps)

prPostFs :: PromptRef p pr_ps ps -> Lens'
	(Frames dfd r ps)
	(Frames dfd r (p ': pr_ps))
prPostFs PRHead = id
prPostFs (PRTail pr) = fsTail . prPostFs pr

prTryDecr :: PromptRef p pr_ps ps -> r -> (forall p'. PromptRef p' (p ': pr_ps) ps -> r) -> r
prTryDecr PRHead base rec = base
prTryDecr (PRTail PRHead) base rec = rec PRHead
prTryDecr (PRTail (PRTail pr)) base rec = prTryDecr (PRTail pr) base (rec . PRTail)

jumpOut ::
	forall
		sfd dfd r a
		(ps1 :: Prompts sfd) (ps2 :: Prompts sfd)
		(pr_ps1 :: Prompts sfd) (pr_ps2 :: Prompts sfd)
		(sd :: sfd) rt jt (rps :: Prompts sfd) (jps :: Prompts sfd).
	PromptRef ('Prompt sd rt jt rps jps) pr_ps1 ps1 ->
	PromptRef ('Prompt sd rt jt rps jps) pr_ps2 ps2 ->
	(
		(a -> Cont dfd r ps2 ('Prompt sd rt jt rps jps ': rps) rt) ->
		Cont dfd r pr_ps1 jps jt
	) ->
	Cont dfd r ps1 ps2 a
jumpOut pr1 pr2 f = Cont $ \fs ka -> runCont
	(f $ \a -> Cont $ \fs' rk ->
		ka a $ fs'
			& prPostFs pr2.fsHead %~ \f@(Frame {..}) -> Frame {
				_fRet = \rv fs'' -> rk rv (FCons f fs'')
			, .. })
	(fs^.prPostFs pr1.fsTail)
	(fs^.prPostFs pr1.fsHead.fJmp)
-- jumpOut pr f = Cont $ case pr of
-- 		PRHead -> go_exit PRHead PRHead
-- 		PRTail pr -> go_exit PRHead (PRTail pr)
-- 	where
-- 		go_exit ::
-- 			forall (sd' :: sfd) rt' jt' (spot_ps :: Prompts sfd).
-- 			PromptRef sd' rt' jt' spot_ps ps ->
-- 			PromptRef sd rt jt pr_ps ('(sd', rt', jt') ': spot_ps) ->
-- 			Frames dfd r ps ->
-- 			(a -> Frames dfd r ps -> r) ->
-- 			r
-- 		go_exit spot PRHead fs ka = runCont
-- 			((fs^.prPostFs spot.fsHead.fExit) True)
-- 			(fs^.prPostFs spot.fsTail)
-- 			$ \() fs' -> runCont
-- 				(f $ \a ->
-- 					Cont $ \fs' rk ->
-- 					go_enter spot (ka a) $
-- 						fs
-- 							& prPostFs spot .~ fs'
-- 							& prPostFs spot.fsHead %~ \f -> set fRet (\r fs -> rk r (FCons f fs)) f)
-- 				fs' (fs^.prPostFs spot.fsHead.fJmp)
-- 		go_exit spot (PRTail pr) fs ka = runCont
-- 				((fs^.prPostFs spot.fsHead.fExit) False)
-- 				(fs^.prPostFs spot.fsTail)
-- 				$ \() fs' ->
-- 					go (set (prPostFs spot.fsTail) fs' fs) id spot pr
-- 			where
-- 				go ::
-- 					forall (ps' :: Prompts sfd).
-- 					forall (sd' :: sfd) rt' jt' (spot_ps :: Prompts sfd).
-- 					Frames dfd r ps ->
-- 					(
-- 						forall (sd' :: sfd) rt' jt' (spot_ps :: Prompts sfd).
-- 						PromptRef sd' rt' jt' spot_ps ps' -> PromptRef sd' rt' jt' spot_ps ps
-- 					) ->
-- 					PromptRef sd' rt' jt' spot_ps ps' ->
-- 					PromptRef sd rt jt pr_ps spot_ps ->
-- 					r
-- 				go fs w1 PRHead PRHead = go_exit (w1 $ PRTail PRHead) PRHead fs ka
-- 				go fs w1 PRHead (PRTail pr) = go_exit (w1 $ PRTail PRHead) (PRTail pr) fs ka
-- 				go fs w1 (PRTail spot) pr = go fs (w1 . PRTail) spot pr
--
-- 		go_enter ::
-- 			forall (sd :: sfd) rt jt (spot_ps :: Prompts sfd).
-- 			PromptRef sd rt jt spot_ps ps ->
-- 			(Frames dfd r ps -> r) ->
-- 			Frames dfd r ps -> r
-- 		go_enter spot k fs = prTryDecr spot (k fs) $ \spot ->
-- 			runCont
-- 				(fs^.prPostFs spot.fsHead.fEnter)
-- 				(fs^.prPostFs spot.fsTail)
-- 				$ \() fs' ->
-- 					go_enter spot k $ set (prPostFs spot.fsTail) fs' fs
