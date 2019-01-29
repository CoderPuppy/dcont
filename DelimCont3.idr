import Control.Lens

mutual
	record Frame sfd dfd r (sd : sfd) (ps : List (sfd, Type, Type)) rt jt where
		constructor MkFrame
		dd : dfd
		ret : rt -> Frames sfd dfd r ps -> r
		jmp : jt -> Frames sfd dfd r ps -> r
	data Frames : (sfd : Type) -> (dfd : Type) -> (r : Type) -> (ps : List (sfd, Type, Type)) -> Type where
		Nil : Frames sfd dfd r []
		(::) : Frame sfd dfd r sd ps rt jt -> Frames sfd dfd r ps -> Frames sfd dfd r ((sd, rt, jt) :: ps)
record Cont sfd dfd r (ps : List (sfd, Type, Type)) a where
	constructor MkCont
	runCont : (a -> Frames sfd dfd r ps -> r) -> Frames sfd dfd r ps -> r
record ContT sfd dfd r (ps : List (sfd, Type, Type)) (m : Type -> Type) a where
	constructor MkContT
	runContT : Cont sfd dfd (m r) ps a

Functor (Cont sfd dfd r ps) where
	map f a = MkCont $ \k, fs => runCont a (k . f) fs
Applicative (Cont sfd dfd r ps) where
	pure a = MkCont $ \k, fs => k a fs
	f <*> a = MkCont $ \k, fs => runCont f (\f, fs => runCont a (\a, fs => k (f a) fs) fs) fs
Monad (Cont sfd dfd r ps) where
	a >>= f = MkCont $ \k, fs => runCont a (\a, fs => runCont (f a) k fs) fs

Functor (ContT sfd dfd r ps m) where
	map f a = MkContT $ map f $ runContT a
Applicative (ContT sfd dfd r ps m) where
	pure a = MkContT $ pure a
	f <*> a = MkContT $ runContT f <*> runContT a
Monad (ContT sfd dfd r ps m) where
	a >>= f = MkContT $ runContT a >>= runContT . f

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
prPostPs : {sd : sfd} -> PromptRef sd rt jt ps -> List (sfd, Type, Type)
prPostPs {ps = _ :: ps} Head = ps
prPostPs {ps = _ :: ps} (Tail fs) = prPostPs fs
prPostFs : (pr : PromptRef sd rt jt ps) -> Lens'
	(Frames sfd dfd r ps)
	(Frames sfd dfd r ((sd, rt, jt) :: prPostPs pr))
prPostFs Head = id
prPostFs (Tail pr) = fsTail . prPostFs pr

prompt :
	(sd : sfd) -> dfd ->
	(rt -> Cont sfd dfd r ps a) ->
	(jt -> Cont sfd dfd r ps a) ->
	Cont sfd dfd r ((sd, rt, jt) :: ps) rt ->
	Cont sfd dfd r ps a
prompt sd dd rk jk b =
	MkCont $ \ka, fs => runCont b
		(\rt, (f :: fs') => Frame.ret f rt fs')
		((:: fs) $ MkFrame dd
			(\rt, fs' => runCont (rk rt) ka fs')
			(\jt, fs' => runCont (jk jt) ka fs')
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
		(f $ \a => MkCont $ \rk, fs' => ka a $ set (prPostFs pr) fs' fs)
		(Frame.jmp $ view (prPostFs pr . fsHead) fs)
		(view (prPostFs pr . fsTail) fs)
