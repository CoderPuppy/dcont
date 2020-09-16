module IndexedMonad1

import Control.Monad.Identity

namespace lens
	export
	Lens : Type -> Type -> Type -> Type -> Type
	Lens s t a b = {0 f : Type -> Type} -> Functor f => (a -> f b) -> s -> f t
	
	export
	record Const (a : Type) (b : k) where
		constructor MkConst
		getConst : a

	Functor (Const a) where
		map f (MkConst a) = MkConst a

	view : ((a -> Const a b) -> s -> Const a t) -> s -> a
	view l = getConst . l MkConst

	set : ((a -> Identity b) -> s -> Identity t) -> b -> s -> t
	set l b = runIdentity . l (const $ Id b)

	over : ((a -> Identity b) -> s -> Identity t) -> (a -> b) -> s -> t
	over l f = runIdentity . l (Id . f)

record Prompt sdt where
	constructor MkPrompt
	sd : sdt
	rt : Type
	jt : Type
	rst : Type
	jst : Type

StackTLens : (Type -> Type) -> Type
StackTLens stt = {0 st1, st2 : Type} -> Lens (stt st1) (stt st2) st1 st2

namespace frames
	export
	interface Frame fr where
		frameR : Type
		frameRT : Type
		frameRST : Type
		frameRK : {0 st : Type} -> fr st -> frameRT -> frameRST -> frameR
		frameTail : Lens (fr st1) (fr st2) st1 st2
	export
	record FPrompt (sdt : Type) (ddt : Prompt sdt -> Type) (r : Type) (p : Prompt sdt) (st : Type) where
		constructor MkFPrompt
		dd : ddt p
		rk : p.rt -> p.rst -> r
		jk : p.jt -> p.jst -> r
		tail : st
	export
	Frame (FPrompt sdt ddt r p) where
		frameTail i fr = map (\i => record { tail = i } fr) $ i $ fr.tail
	export
	record FErased (r, rst, rt, st : Type) where
		constructor MkFErased
		rk : rt -> rst -> r
		tail : st
	export
	Frame (FErased r rst rt) where
		frameTail i fr = map (\i => record { tail = i } fr) $ i $ fr.tail
	export
	data FFix : (stt : Type -> Type) -> (st : Type) -> Type where
		Z :                     st  -> FFix stt st
		S : stt (FFix stt st) -> FFix stt st
	export
	Frame stt => Frame (FFix stt) where
		frameTail i (Z s) = map Z $ i s
		frameTail i (S s) = map S $ frameTail (frameTail i) s

record Cont (r : Type) (st1, st2 : Type) (a : Type) where
	constructor MkCont
	runCont : st1 -> (a -> st2 -> r) -> r

(<*>) : Cont r st1 st2 (a -> b) -> Cont r st2 st3 a -> Cont r st1 st3 b
f <*> a = MkCont $ \s1, k =>
	runCont f s1 $ \f, s2 =>
	runCont a s2 $ k . f
(>>=) : Cont r st1 st2 a -> (a -> Cont r st2 st3 b) -> Cont r st1 st3 b
a >>= f = MkCont $ \s1, k =>
	runCont a s1 $ \a, s2 =>
	runCont (f a) s2 k
Functor (Cont r st1 st2) where
	map f k = MkCont $ \s1, kb => runCont k s1 $ kb . f
Applicative (Cont r st st) where
	pure a = MkCont $ \s, k => k a s
	(<*>) = IndexedMonad1.(<*>)
Monad (Cont r st st) where
	(>>=) = IndexedMonad1.(>>=)
	join = (>>= id)

-- idea: erasing a frame and adding an erased frame are always fine
-- idea: don't interpret stack descriptors, just make them types

inFrame :
	(sd : sdt) ->
	ddt (MkPrompt sd rt jt rst jst) ->
	(rt -> Cont r rst st2 a) ->
	(jt -> Cont r jst st2 a) ->
	Cont r
		(FPrompt sdt ddt r (MkPrompt sd rt jt rst jst) st1)
		(FErased r rst rt rst) rt ->
	Cont r st1 st2 a
inFrame sd dd rk jk b = MkCont $ \s1, ka => runCont b
	(MkFPrompt dd
		(\rv, rs => runCont (rk rv) rs ka)
		(\jv, js => runCont (jk jv) js ka)
		s1)
	(\rv, (MkFErased rk tail) => rk rv tail)

jumpOut :
	{0 stt : Type -> Type} ->
	Lens
		(stt (FPrompt sdt ddt r p st1))
		(stt (FErased r (p.rst) (p.rt) st2))
		(FPrompt sdt ddt r p st1)
		(FErased r (p.rst) (p.rt) st2) ->
	(
		(a -> Cont r st2 (p.rst) (p.rt)) ->
		Cont r st1 (p.jst) (p.jt)
	) ->
	Cont r
		(stt (FPrompt sdt ddt r p st1))
		(stt (FErased r (p.rst) (p.rt) st2))
		a
jumpOut l f = MkCont $ \s1', ka => runCont
	(f $ \a => MkCont $ \s2_, kr =>
		ka a $ set l (MkFErased kr s2_) s1')
	(getConst $ l (MkConst . FPrompt.tail) s1')
	((view l s1').jk)

erase :
	{0 stt : Type -> Type} ->
	StackTLens stt ->
	Cont r
		(stt (FPrompt sdt ddt r p st))
		(stt (FErased r (p.rst) (p.rt) st))
		()
erase l = MkCont $ \s', k => k () $ over l (\f => MkFErased (f.rk) (f.tail)) s'

introErasedBelow :
	{0 stt : Type -> Type} ->
	Frame ft =>
	StackTLens stt ->
	Cont (frameR {fr = ft})
		(stt (ft st))
		(stt (ft (FErased
			(frameR {fr = ft})
			(frameRST {fr = ft})
			(frameRT {fr = ft})
			st)))
		()
introErasedBelow l = MkCont $ \s', k => k () $
	over l (\f => over frameTail (MkFErased $ frameRK f) f) s'

introErasedAbove :
	{0 stt : Type -> Type} ->
	Frame ft =>
	StackTLens stt ->
	Cont (frameR {fr = ft})
		(stt (ft st))
		(stt (FErased
			(frameR {fr = ft})
			(frameRST {fr = ft})
			(frameRT {fr = ft})
			(ft st)))
		()
introErasedAbove l = MkCont $ \s', k => k () $
	over l (\f => MkFErased (frameRK f) f) s'

liftIO : IO a -> Cont (IO r) st st a
liftIO m = MkCont $ \s, k => m >>= flip k s

execCont : Cont a () () a -> a
execCont m = runCont m () $ \a, () => a

execContIO : Applicative m => Cont (m a) () () a -> m a
execContIO = execCont . map pure

interface StackShow st where
	stackShow : st -> List String
(Show (ddt p), StackShow st) => StackShow (FPrompt sdt ddt r p st) where
	stackShow f = show (f.dd) :: stackShow (f.tail)
StackShow () where
	stackShow () = []

record PlainShow where
	constructor MkPlainShow
	getPlainShow : String
Show PlainShow where
	show = getPlainShow

debug : StackShow st => String -> Cont (IO r) st st ()
debug l = MkCont $ \s, k => putStrLn (l ++ " " ++ show (map MkPlainShow $ stackShow s)) *> k () s

test : Cont (IO ()) () () ()
test = do
	liftIO $ putStrLn "hello world"
	debug "1" -- []
	inFrame
		{r=IO ()}
		{rt=()} {jt=()}
		{sdt=String} {ddt=const String}
		{rst=FErased (IO ()) () () ()} {jst=()}
		{st1=()} {st2=()}
		"a" "a" pure pure $ do
		debug "2" -- [pa]
		jumpOut
			{r=IO ()} {a=()}
			{sdt=String} {ddt=const String}
			{p=MkPrompt "a" () () (FErased (IO ()) () () ()) ()}
			{st1=()}
			{st2=FPrompt String (const String) (IO ()) (MkPrompt "b" () () () ()) ()}
			{stt=id} id $ \ka => do
			debug "3" -- []
			inFrame
				{r=IO ()}
				{rt=()} {jt=()}
				{sdt=String} {ddt=const String}
				{rst=()} {jst=()}
				{st1=()} {st2=()}
				"b" "b" pure pure $ do
				debug "4" -- [pb]
				ka ()
				debug "5" -- [eb]
			debug "6" -- []
		debug "7" -- [ea, pb]
		jumpOut
			{r=IO ()} {a=()}
			{sdt=String} {ddt=const String}
			{p=MkPrompt "b" () () () ()}
			{st1=()} {st2=()}
			{stt=FErased (IO ()) (FErased (IO ()) () () ()) ()} ?t
			$ \kb => do
				debug "8" -- []
				kb ()
				debug "9" -- []
		debug "10" -- [ea, eb]
	debug "11" -- []
