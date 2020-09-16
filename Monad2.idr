import Control.Lens

mutual
	record Frame sfd dfd r (sd : sfd) (ps : List (sfd, Type, Type)) rt jt where
		constructor MkFrame
		dd : dfd
		ret : rt -> Frames sfd dfd r ps -> r
		jmp : jt -> Frames sfd dfd r ps -> r
		enter : Cont sfd dfd r ps ()
		exit : Bool -> Cont sfd dfd r ps ()
	data Frames : (sfd : Type) -> (dfd : Type) -> (r : Type) -> (ps : List (sfd, Type, Type)) -> Type where
		Nil : Frames sfd dfd r []
		(::) : Frame sfd dfd r sd ps rt jt -> Frames sfd dfd r ps -> Frames sfd dfd r ((sd, rt, jt) :: ps)
	record Cont sfd dfd r (ps : List (sfd, Type, Type)) a where
		constructor MkCont
		runCont : (a -> Frames sfd dfd r ps -> r) -> Frames sfd dfd r ps -> r

fRet : Lens
	(Frame sfd dfd r sd ps rt1 jt)
	(Frame sfd dfd r sd ps rt2 jt)
	(rt1 -> Frames sfd dfd r ps -> r)
	(rt2 -> Frames sfd dfd r ps -> r)
fRet i = Mor $ \(MkFrame dd ret jmp entry exit) => map (\ret' => MkFrame dd ret' jmp entry exit) $ applyMor i ret

Functor (Cont sfd dfd r ps) where
	map f a = MkCont $ \k, fs => runCont a (k . f) fs
Applicative (Cont sfd dfd r ps) where
	pure a = MkCont $ \k, fs => k a fs
	f <*> a = MkCont $ \k, fs => runCont f (\f, fs => runCont a (\a, fs => k (f a) fs) fs) fs
Monad (Cont sfd dfd r ps) where
	a >>= f = MkCont $ \k, fs => runCont a (\a, fs => runCont (f a) k fs) fs

fsHead : Lens
	(Frames sfd dfd r ((sd1, rt1, jt1) :: ps))
	(Frames sfd dfd r ((sd2, rt2, jt2) :: ps))
	(Frame sfd dfd r sd1 ps rt1 jt1)
	(Frame sfd dfd r sd2 ps rt2 jt2)
fsHead i = Mor $ \(f :: fs) => map (\f' => f' :: fs) $ applyMor i f

fsTail : Lens'
	(Frames sfd dfd r ((sd, rt, jt) :: ps))
	(Frames sfd dfd r ps)
fsTail i = Mor $ \(f :: fs) => map (\fs' => f :: fs') $ applyMor i fs

data PromptRef : sfd -> Type -> Type -> List (sfd, Type, Type) -> Type where
	Head : PromptRef sd rt jt ((sd, rt, jt) :: ps)
	Tail : PromptRef sd rt jt ps -> PromptRef sd rt jt ((sd', rt', jt') :: ps)
prPrePs : {sd : sfd} -> PromptRef sd rt jt ps -> List (sfd, Type, Type)
prPrePs Head = []
prPrePs {ps = (sd, rt, jt) :: ps} (Tail pr) = (sd, rt, jt) :: prPrePs pr
prPostPs : {sd : sfd} -> PromptRef sd rt jt ps -> List (sfd, Type, Type)
prPostPs {ps = _ :: ps} Head = ps
prPostPs {ps = _ :: ps} (Tail pr) = prPostPs pr
prPostFs : (pr : PromptRef sd rt jt ps) -> Lens'
	(Frames sfd dfd r ps)
	(Frames sfd dfd r ((sd, rt, jt) :: prPostPs pr))
prPostFs Head = id
prPostFs (Tail pr) = fsTail . prPostFs pr

prMakeHead :
	{sd : sfd} -> PromptRef sd rt jt ps ->
	(	sd' : sfd ** rt' : Type ** jt' : Type **
		pr : PromptRef sd' rt' jt' ps **
		ps = (sd', rt', jt') :: prPostPs pr)
prMakeHead {ps = ((sd, rt, jt) :: ps)} Head = (sd ** rt ** jt ** Head ** Refl)
prMakeHead {ps = ((sd', rt', jt') :: ps)} (Tail pr) = (sd' ** rt' ** jt' ** Head ** Refl)

prIncr :
	{sd', sd : sfd} -> (spot : PromptRef sd' rt' jt' ps) -> (pr : PromptRef sd rt jt (prPostPs spot)) ->
	(
		sd'' : sfd **
		rt'' : Type **
		jt'' : Type **
		spot' : PromptRef sd'' rt'' jt'' ps **
		prPostPs spot = (sd'', rt'', jt'')::prPostPs spot'
	)
prIncr {ps = ((sd', rt', jt') :: ps)} Head pr = let
		(sd'' ** rt'' ** jt'' ** spot' ** prf) = prMakeHead pr
	in (sd'' ** rt'' ** jt'' ** Tail spot' ** prf)
prIncr {ps = ((sd', rt', jt') :: ps)} (Tail spot) pr = let
		(sd'' ** rt'' ** jt'' ** spot' ** prf) = prIncr spot pr
	in (sd'' ** rt'' ** jt'' ** Tail spot' ** prf)

prTryDecr :
	{sd : sfd} -> (pr : PromptRef sd rt jt ps) ->
	Maybe (
		sd' : sfd **
		rt' : Type **
		jt' : Type **
		pr' : PromptRef sd' rt' jt' ps **
		prPostPs pr' = (sd, rt, jt) :: prPostPs pr
	)
prTryDecr {ps = (sd, rt, jt) :: ps} Head = Nothing
prTryDecr {ps = (sd'', rt'', jt'') :: ps} (Tail pr) with (prTryDecr pr)
	prTryDecr {ps = (sd'', rt'', jt'') :: (sd, rt, jt) :: ps} (Tail Head) | Nothing = Just (sd'' ** rt'' ** jt'' ** Head ** Refl)
	prTryDecr {ps = (sd'', rt'', jt'') :: ps} (Tail pr) | (Just (sd' ** rt' ** jt' ** pr' ** prf)) = Just (sd' ** rt' ** jt' ** Tail pr' ** prf)

mutual
	lift_k'frames' :
		(pr : PromptRef sd rt jt ps) ->
		Frames sfd dfd r ps ->
		Frames sfd dfd r (prPrePs pr ++ prPostPs pr)
	lift_k'frames' {ps = ((sd, rt, jt) :: ps)} Head (f :: fs) = fs
	lift_k'frames' {ps = ((sd', rt', jt') :: ps)} (Tail pr) (f :: fs) = lift_k'frame pr rf f :: lift_k'frames' pr fs
		where rf = view (prPostFs pr . fsHead) fs

	lift_k'frame' :
		(pr : PromptRef sd rt jt ps) ->
		Frame sfd dfd r sd' (prPrePs pr ++ prPostPs pr) rt' jt' ->
		Frame sfd dfd r sd' ps rt' jt'
	lift_k'frame' pr (MkFrame dd ret jmp enter exit) = MkFrame dd
		(\rv, fs => ret rv $ lift_k'frames' pr fs)
		(\jv, fs => jmp jv $ lift_k'frames' pr fs)
		(lift_k pr enter)
		(lift_k pr . exit)

	lift_k'frames :
		(pr : PromptRef sd rt jt ps) ->
		Frame sfd dfd r sd (prPostPs pr) rt jt ->
		Frames sfd dfd r (prPrePs pr ++ prPostPs pr) ->
		Frames sfd dfd r ps
	lift_k'frames {ps = ((sd, rt, jt) :: ps)} Head rf fs = rf :: fs
	lift_k'frames {ps = ((sd', rt', jt') :: ps)} (Tail pr) rf (f :: fs) = lift_k'frame' pr f :: lift_k'frames pr rf fs

	lift_k'frame :
		(pr : PromptRef sd rt jt ps) ->
		Frame sfd dfd r sd (prPostPs pr) rt jt ->
		Frame sfd dfd r sd' ps rt' jt' ->
		Frame sfd dfd r sd' (prPrePs pr ++ prPostPs pr) rt' jt'
	lift_k'frame pr rf (MkFrame dd ret jmp enter exit) = MkFrame dd
		(\rv, fs => ret rv $ lift_k'frames pr rf fs)
		(\jv, fs => jmp jv $ lift_k'frames pr rf fs)
		(MkCont $ \k, fs => runCont enter
			(\a, fs => k a $ lift_k'frames' pr fs)
			(lift_k'frames pr rf fs))
		(\final => MkCont $ \k, fs => runCont (exit final)
			(\a, fs => k a $ lift_k'frames' pr fs)
			(lift_k'frames pr rf fs))

	lift_k :
		(pr : PromptRef sd rt jt ps) ->
		Cont sfd dfd r (prPrePs pr ++ prPostPs pr) a ->
		Cont sfd dfd r ps a
	lift_k {ps = ((sd, rt, jt) :: ps)} Head m = MkCont $ \k, (f :: fs) => runCont m (\a, fs => k a (f :: fs)) fs
	lift_k {ps = ((sd', rt', jt') :: ps)} (Tail pr) m = MkCont $ \k, (f :: fs) => runCont
		(lift_k pr $ MkCont $ \k', fs' => runCont m
			(\a, (f :: fs) => k' a fs)
			(lift_k'frame pr (view (prPostFs pr . fsHead) fs) f :: fs'))
		(\a, fs => k a (f :: fs))
		fs

prompt :
	(sd : sfd) -> dfd ->
	(rt -> Cont sfd dfd r ps a) ->
	(jt -> Cont sfd dfd r ps a) ->
	Cont sfd dfd r ps () ->
	(Bool -> Cont sfd dfd r ps ()) ->
	Cont sfd dfd r ((sd, rt, jt) :: ps) rt ->
	Cont sfd dfd r ps a
prompt sd dd rk jk entry exit b =
	MkCont $ \ka, fs => runCont b
		(\rt, (f :: fs') => Frame.ret f rt fs')
		((:: fs) $ MkFrame dd
			(\rt, fs' => runCont (rk rt) ka fs')
			(\jt, fs' => runCont (jk jt) ka fs')
			entry exit
		)

control :
	(pr : PromptRef sd rt jt ps) ->
	(
		(a -> Cont sfd dfd r ((sd, rt, jt) :: prPostPs pr) rt) ->
		Cont sfd dfd r (prPostPs pr) jt
	) ->
	Cont sfd dfd r ps a
control pr f =
	MkCont $ \ka, fs => runCont
		(f $ \a => MkCont $ \rk, fs' => ka a $
			over (prPostFs pr . fsHead) (\f => record { ret = \r, fs => rk r (f :: fs) } f) $
			set (prPostFs pr) fs' fs)
		(Frame.jmp $ view (prPostFs pr . fsHead) fs)
		(view (prPostFs pr . fsTail) fs)

mutual
	control2_go_enter :
		{sd : sfd} -> (spot : PromptRef sd rt jt ps) ->
		(Frames sfd dfd r ps -> r) ->
		Frames sfd dfd r ps -> r
	control2_go_enter spot k fs = runCont
		(Frame.enter $ view (prPostFs spot . fsHead) fs)
		(\(), fs' => control2_go_enter_cont spot k $ set (prPostFs spot . fsTail) fs' fs)
		(view (prPostFs spot . fsTail) fs)

	control2_go_enter_cont :
		{sd : sfd} -> (spot : PromptRef sd rt jt ps) ->
		(Frames sfd dfd r ps -> r) ->
		Frames sfd dfd r ps -> r
	control2_go_enter_cont spot k fs = case prTryDecr spot of
			Nothing => k fs
			Just (sd' ** rt' ** jt' ** spot' ** prf) => control2_go_enter spot' k fs

control2_go_exit :
	(spot : PromptRef sd' rt' jt' ps) ->
	(pr : PromptRef sd rt jt ((sd', rt', jt') :: prPostPs spot)) ->
	(
		(a -> Cont sfd dfd r ((sd, rt, jt) :: prPostPs pr) rt) ->
		Cont sfd dfd r (prPostPs pr) jt
	) ->
	(a -> Frames sfd dfd r ps -> r) ->
	Frames sfd dfd r ps -> r
control2_go_exit spot Head f ka fs = runCont
	(Frame.exit (view (prPostFs spot . fsHead) fs) True)
	(\(), fs' => runCont
		(f $ \a => MkCont $ \rk, fs' =>
			control2_go_enter_cont spot (ka a) $
				over (prPostFs spot . fsHead) (\f => record { ret = \r, fs => rk r (f :: fs) } f) $
				set (prPostFs spot) fs' fs
		)
		(Frame.jmp $ view (prPostFs spot . fsHead) fs)
		fs')
	(view (prPostFs spot . fsTail) fs)
control2_go_exit {sfd} {dfd} {sd} {rt} {jt} {ps} {a} spot (Tail pr) f ka fs = runCont
	(Frame.exit (view (prPostFs spot . fsHead) fs) False)
	(\(), fs' => let
			(sd'' ** rt'' ** jt'' ** spot' ** prf) = prIncr spot pr
		in replace
			{P=\i =>
				(pr : PromptRef sd rt jt i) ->
				(
					(a -> Cont sfd dfd r ((sd, rt, jt) :: prPostPs {ps = i} pr) rt) ->
					Cont sfd dfd r (prPostPs {ps = i} pr) jt
				) ->
				(a -> Frames sfd dfd r ps -> r) ->
				Frames sfd dfd r ps -> r
			}
			(sym prf)
			(control2_go_exit spot')
			pr f ka
			(set (prPostFs spot . fsTail) fs' fs)
	)
	(view (prPostFs spot . fsTail) fs)

control2 :
	(pr : PromptRef sd rt jt ps) ->
	(
		(a -> Cont sfd dfd r ((sd, rt, jt) :: prPostPs pr) rt) ->
		Cont sfd dfd r (prPostPs pr) jt
	) ->
	Cont sfd dfd r ps a
control2 Head f = MkCont $ control2_go_exit Head Head f
control2 {ps = (sd', rt', jt') :: ps} (Tail pr) f = MkCont $ control2_go_exit Head (Tail pr) f

namespace contt
	record ContT sfd dfd r (ps : List (sfd, Type, Type)) (m : Type -> Type) a where
		constructor MkContT
		runContT : Cont sfd dfd (m r) ps a

	Functor (ContT sfd dfd r ps m) where
		map f a = MkContT $ map f $ runContT a
	Applicative (ContT sfd dfd r ps m) where
		pure a = MkContT $ pure a
		f <*> a = MkContT $ runContT f <*> runContT a
	Monad (ContT sfd dfd r ps m) where
		a >>= f = MkContT $ runContT a >>= runContT . f

	lift : Monad m => m a -> ContT sfd dfd r ps m a
	lift o = MkContT $ MkCont $ \k, fs => o >>= flip k fs

test : ContT () () () [] IO ()
test = do
	Left a_k <- MkContT $ prompt
		{rt = Int}
		{jt = Int -> ContT () () () [] IO Int}
		() ()
		(\r => runContT $ do
			lift $ printLn ("a.ret", r)
			pure $ Right r)
		(\j => runContT $ do
			lift $ printLn "a.jmp"
			pure $ Left j)
		(runContT $ lift $ printLn "a.ent")
		(\final => runContT $ lift $ printLn ("a.ext", final))
		(runContT $ do
			lift $ printLn ("a.1")
			a <- MkContT $ control2 Head $ \k => do
				pure $ \a => do
					Right b <- MkContT $ prompt
						{rt = Int}
						{jt = Int -> ContT () () () [] IO Int}
						() ()
						(\r => runContT $ do
							lift $ printLn ("a'.ret", r)
							pure $ Right r)
						(\j => runContT $ do
							lift $ printLn "a'.jmp"
							pure $ Left j)
						(runContT $ lift $ printLn "a'.ent")
						(\final => runContT $ lift $ printLn ("a'.ext", final))
						(k a)
					pure b
			lift $ printLn ("a.2")
			pure $ a + 1
		)
	MkContT $ prompt
		() ()
		(\r => runContT $ do
			lift $ printLn ("b.ret", r)
			pure r)
		(\j => runContT $ do
			lift $ printLn "b.jmp"
			pure j)
		(runContT $ lift $ printLn "b.ent")
		(\final => runContT $ lift $ printLn ("b.ext", final))
		(runContT $ do
			lift $ printLn ("b.1")
			b <- MkContT $ lift_k Head $ runContT $ a_k 1
			lift $ printLn ("b.2", b)
		)
	pure ()
-- -}
