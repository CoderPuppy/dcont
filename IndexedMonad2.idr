module IndexedMonad2

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
	st : Type

StackTLens : (Type -> Type) -> Type
StackTLens stt = {0 st1, st2 : Type} -> Lens (stt st1) (stt st2) st1 st2

namespace frames
	export
	interface Frame fr where
		frameR : Type
		frameRT : Type
		frameST : Type
		frameK : {0 st : Type} -> fr st -> frameRT -> frameST -> frameR
		frameTail : Lens (fr st1) (fr st2) st1 st2
	export
	record FPrompt (sdt : Type) (ddt : Prompt sdt -> Type) (r : Type) (p : Prompt sdt) (st : Type) where
		constructor MkFPrompt
		dd : ddt p
		rk : p.rt -> Prompt.st p -> r
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
	(<*>) = IndexedMonad2.(<*>)
Monad (Cont r st st) where
	(>>=) = IndexedMonad2.(>>=)
	join = (>>= id)

-- idea: erasing a frame and adding an erased frame are always fine
-- idea: don't interpret stack descriptors, just make them types

inFrame :
	(sd : sdt) ->
	ddt (MkPrompt sd rt st2) ->
	Cont r
		(FPrompt sdt ddt r (MkPrompt sd rt st2) st1)
		(FPrompt sdt ddt r (MkPrompt sd rt st2) st2) rt ->
	Cont r st1 st2 rt
inFrame sd dd b = MkCont $ \s1, k => runCont b
	(MkFPrompt dd k s1)
	(\rv, (MkFPrompt dd rk tail) => rk rv tail)

jumpOut :
	{0 stt : Type -> Type} ->
	Lens
		(stt (FPrompt sdt ddt r p st1))
		(stt (FPrompt sdt ddt r p st2))
		(FPrompt sdt ddt r p st1)
		(FPrompt sdt ddt r p st2) ->
	(
		(a -> Cont r st2 (p.st) (p.rt)) ->
		Cont r st1 (p.st) (p.rt)
	) ->
	Cont r
		(stt (FPrompt sdt ddt r p st1))
		(stt (FPrompt sdt ddt r p st2))
		a
jumpOut l f = MkCont $ \s1', ka => runCont
	(f $ \a => MkCont $ \s2_, kr =>
		ka a $ set (l . frameTail) s2_ s1')
	(getConst $ l (MkConst . FPrompt.tail) s1')
	((view l s1').rk)
