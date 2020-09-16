{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE GADTs, PolyKinds, KindSignatures, DataKinds, TypeOperators, RankNTypes, ScopedTypeVariables #-}

module Monad where

import Data.Kind
import Control.Lens

type Prompts sfd = [(sfd, Type, Type)]

data Frame dfd r (ps :: Prompts sfd) (sd :: sfd) rt jt = Frame {
	_fDD :: dfd,
	_fRet :: rt -> Frames dfd r ps -> r,
	_fJmp :: jt -> Frames dfd r ps -> r,
	_fEnter :: Cont dfd r ps (),
	-- this Bool says if this frame is the target of the jumpOut
	_fExit :: Bool -> Cont dfd r ps ()
}
data Frames dfd r (ps :: Prompts sfd) where
	FNil :: Frames dfd r '[]
	FCons ::
		forall dfd r (sd :: sfd) rt jt (ps :: Prompts sfd).
		Frame dfd r ps sd rt jt -> Frames dfd r ps ->
		Frames dfd r ('(sd, rt, jt) ': ps)
newtype Cont dfd r (ps :: Prompts sfd) a = Cont {
	runCont :: Frames dfd r ps -> (a -> Frames dfd r ps -> r) -> r }

fDD :: Lens' (Frame dfd r ps sd rt jt) dfd
fDD i f = fmap (\dd -> f { _fDD = dd }) $ i $ _fDD f

fRet :: Lens' (Frame dfd r ps sd rt jt) (rt -> Frames dfd r ps -> r)
fRet i f = fmap (\ret -> f { _fRet = ret }) $ i $ _fRet f

fJmp :: Lens' (Frame dfd r ps sd rt jt) (jt -> Frames dfd r ps -> r)
fJmp i f = fmap (\jmp -> f { _fJmp = jmp }) $ i $ _fJmp f

fEnter :: Lens' (Frame dfd r ps sd rt jt) (Cont dfd r ps ())
fEnter i f = fmap (\enter -> f { _fEnter = enter }) $ i $ _fEnter f

fExit :: Lens' (Frame dfd r ps sd rt jt) (Bool -> Cont dfd r ps ())
fExit i f = fmap (\exit -> f { _fExit = exit }) $ i $ _fExit f

fsHead :: Lens
	(Frames dfd r ('(sd1, rt1, jt1) ': ps))
	(Frames dfd r ('(sd2, rt2, jt2) ': ps))
	(Frame dfd r ps sd1 rt1 jt1)
	(Frame dfd r ps sd2 rt2 jt2)
fsHead i (FCons f fs) = fmap (flip FCons fs) $ i f

fsTail :: Lens'
	(Frames dfd r ('(sd, rt, jt) ': ps))
	(Frames dfd r ps)
fsTail i (FCons f fs) = fmap (FCons f) $ i fs

instance Functor (Cont dfd r ps) where
	fmap f a = Cont $ \fs k -> runCont a fs $ k . f
instance Applicative (Cont dfd r ps) where
	pure a = Cont $ \fs k -> k a fs
	f <*> a = Cont $ \fs k ->
		runCont f fs $ \f fs ->
		runCont a fs $ \a fs ->
		k (f a) fs
instance Monad (Cont dfd r ps) where
	a >>= f = Cont $ \fs k ->
		runCont a fs $ \a fs ->
		runCont (f a) fs k

inFrame ::
	dfd ->
	(rt -> Cont dfd r ps a) ->
	(jt -> Cont dfd r ps a) ->
	Cont dfd r ps () ->
	(Bool -> Cont dfd r ps ()) ->
	Cont dfd r ('(sd, rt, jt) ': ps) rt ->
	Cont dfd r ps a
inFrame dd rk jk enter exit b = Cont $ \fs ka -> runCont b
	(flip FCons fs $ Frame {
		_fDD = dd,
		_fRet = \rv fs -> runCont (rk rv) fs ka,
		_fJmp = \jv fs -> runCont (jk jv) fs ka,
		-- john sucks drew off-kenny 2020
		_fEnter = enter,
		_fExit = exit
	})
	(\rv (FCons f fs) -> (f^.fRet) rv fs)

data PromptRef (sd :: sfd) rt jt ps' (ps :: [(sfd, Type, Type)]) where
	PRHead :: PromptRef sd rt jt ps ('(sd, rt, jt) ': ps)
	PRTail :: PromptRef sd rt jt ps' ps -> PromptRef sd rt jt ps' ('(sd', rt', jt') ': ps)

prPostFs :: PromptRef sd rt jt pr_ps ps -> Lens'
	(Frames dfd r ps)
	(Frames dfd r ('(sd, rt, jt) ': pr_ps))
prPostFs PRHead = id
prPostFs (PRTail pr) = fsTail . prPostFs pr

prTryDecr :: PromptRef sd rt jt pr_ps ps -> r -> (forall sd' rt' jt'. PromptRef sd' rt' jt' ('(sd, rt, jt) ': pr_ps) ps -> r) -> r
prTryDecr PRHead base rec = base
prTryDecr (PRTail PRHead) base rec = rec PRHead
prTryDecr (PRTail (PRTail pr)) base rec = prTryDecr (PRTail pr) base (rec . PRTail)

jumpOut ::
	forall
		sfd dfd r
		(ps :: Prompts sfd) a
		(sd :: sfd) rt jt (pr_ps :: Prompts sfd).
	PromptRef sd rt jt pr_ps ps ->
	(
		(a -> Cont dfd r ('(sd, rt, jt) ': pr_ps) rt) ->
		Cont dfd r pr_ps jt
	) ->
	Cont dfd r ps a
jumpOut pr f = Cont $ case pr of
		PRHead -> go_exit PRHead PRHead
		PRTail pr -> go_exit PRHead (PRTail pr)
	where
		go_exit ::
			forall (sd' :: sfd) rt' jt' (spot_ps :: Prompts sfd).
			PromptRef sd' rt' jt' spot_ps ps ->
			PromptRef sd rt jt pr_ps ('(sd', rt', jt') ': spot_ps) ->
			Frames dfd r ps ->
			(a -> Frames dfd r ps -> r) ->
			r
		go_exit spot PRHead fs ka = runCont
			((fs^.prPostFs spot.fsHead.fExit) True)
			(fs^.prPostFs spot.fsTail)
			$ \() fs' -> runCont
				(f $ \a ->
					Cont $ \fs' rk ->
					go_enter spot (ka a) $
						fs
							& prPostFs spot .~ fs'
							& prPostFs spot.fsHead %~ \f -> set fRet (\r fs -> rk r (FCons f fs)) f)
				fs' (fs^.prPostFs spot.fsHead.fJmp)
		go_exit spot (PRTail pr) fs ka = runCont
				((fs^.prPostFs spot.fsHead.fExit) False)
				(fs^.prPostFs spot.fsTail)
				$ \() fs' ->
					go (set (prPostFs spot.fsTail) fs' fs) id spot pr
			where
				go ::
					forall (ps' :: Prompts sfd).
					forall (sd' :: sfd) rt' jt' (spot_ps :: Prompts sfd).
					Frames dfd r ps ->
					(
						forall (sd' :: sfd) rt' jt' (spot_ps :: Prompts sfd).
						PromptRef sd' rt' jt' spot_ps ps' -> PromptRef sd' rt' jt' spot_ps ps
					) ->
					PromptRef sd' rt' jt' spot_ps ps' ->
					PromptRef sd rt jt pr_ps spot_ps ->
					r
				go fs w1 PRHead PRHead = go_exit (w1 $ PRTail PRHead) PRHead fs ka
				go fs w1 PRHead (PRTail pr) = go_exit (w1 $ PRTail PRHead) (PRTail pr) fs ka
				go fs w1 (PRTail spot) pr = go fs (w1 . PRTail) spot pr

		go_enter ::
			forall (sd :: sfd) rt jt (spot_ps :: Prompts sfd).
			PromptRef sd rt jt spot_ps ps ->
			(Frames dfd r ps -> r) ->
			Frames dfd r ps -> r
		go_enter spot k fs = prTryDecr spot (k fs) $ \spot ->
			runCont
				(fs^.prPostFs spot.fsHead.fEnter)
				(fs^.prPostFs spot.fsTail)
				$ \() fs' ->
					go_enter spot k $ set (prPostFs spot.fsTail) fs' fs

dynamicWind ::
	dfd ->
	-- True = main (first) entry, False = jump inside
	(Bool -> Cont dfd r ps ()) ->
	-- Left True = jump to this, Left False = jump outside of this, Right v = normal return
	(Either Bool a -> Cont dfd r ps ()) ->
	Cont dfd r ('(sd, a, a) ': ps) a ->
	Cont dfd r ps a
dynamicWind dd enter exit = inFrame dd
	(\v -> do
		exit (Right v)
		pure v)
	(\v -> pure v)
	(enter False)
	(exit . Left)

data SitramPkg dfd r sd rt jt ht ps = SitramPkg {
	sitramV :: jt,
	sitramK :: ht -> SitramK dfd r sd rt jt ht ps
}
type SitramK dfd r sd rt jt ht ps = Cont dfd r ('(sd, rt, SitramPkg dfd r sd rt jt ht ps) ': ps) rt
sitram ::
	dfd ->
	SitramK dfd r sd rt jt ht ps ->
	(jt -> (ht -> SitramK dfd r sd rt jt ht ps) -> Cont dfd r ps rt) ->
	Cont dfd r ps rt
sitram dd b handler = inFrame dd
	pure (\(SitramPkg v k) -> handler v k)
	(pure ()) (const $ pure ())
	b

fcontrol ::
	PromptRef sd rt (SitramPkg dfd r sd rt jt ht pr_ps) pr_ps ps ->
	jt -> Cont dfd r ps ht
fcontrol pr v = jumpOut pr $ \k -> pure $ SitramPkg v k

prompt ::
	dfd ->
	Cont dfd r ('(sd, rt, rt) ': ps) rt ->
	Cont dfd r ps rt
prompt dd = inFrame dd
	pure pure
	(pure ()) (const $ pure ())

control ::
	PromptRef sd rt rt pr_ps ps ->
	(
		(a -> Cont dfd r ('(sd, rt, rt) ': pr_ps) rt) ->
		Cont dfd r ('(sd, rt, rt) ': pr_ps) rt
	) ->
	Cont dfd r ps a
control pr f = jumpOut pr $ \k -> prompt dd $ f k
	where dd = error "TODO"

reset ::
	dfd ->
	Cont dfd r ('(sd, rt, rt) ': ps) rt ->
	Cont dfd r ps rt
reset dd = inFrame dd
	pure pure
	(pure ()) (const $ pure ())

shift ::
	PromptRef sd rt rt pr_ps ps ->
	(
		(a -> Cont dfd r pr_ps rt) ->
		Cont dfd r ('(sd, rt, rt) ': pr_ps) rt
	) ->
	Cont dfd r ps a
shift pr f = jumpOut pr $ \k -> reset dd $ f $ reset dd . k
	where dd = error "TODO"

prompt0 ::
	dfd ->
	Cont dfd r ('(sd, rt, rt) ': ps) rt ->
	Cont dfd r ps rt
prompt0 dd = inFrame dd
	pure pure
	(pure ()) (const $ pure ())

control0 ::
	PromptRef sd rt rt pr_ps ps ->
	(
		(a -> Cont dfd r ('(sd, rt, rt) ': pr_ps) rt) ->
		Cont dfd r pr_ps rt
	) ->
	Cont dfd r ps a
control0 pr f = jumpOut pr $ \k -> f k

reset0 ::
	dfd ->
	Cont dfd r ('(sd, rt, rt) ': ps) rt ->
	Cont dfd r ps rt
reset0 dd = inFrame dd
	pure pure
	(pure ()) (const $ pure ())

shift0 ::
	PromptRef sd rt rt pr_ps ps ->
	(
		(a -> Cont dfd r pr_ps rt) ->
		Cont dfd r pr_ps rt
	) ->
	Cont dfd r ps a
shift0 pr f = jumpOut pr $ \k -> f $ reset dd . k
	where dd = error "TODO"

-- inFrame dd rk jk enter exit (jumpOut PRHead f >>= k)
-- = exit True *> f (\v -> enter *> k) >>= jk
-- where E contains no inFrames
