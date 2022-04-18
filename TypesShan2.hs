{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE BlockArguments, LambdaCase, GADTs, PolyKinds, DataKinds, TypeOperators, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, RankNTypes #-}

module TypesShan2 where

import Control.Monad.Indexed
import Data.Kind

-- takes the type system from this paper
-- A Functional Abstraction of Typed Trails
-- by Kenichi Asai, Youyou Cong, Chiaki Ishio
-- but implement it on top of the type system from this paper
-- A Functional Abstraction of Typed Contexts
-- by Olivier Danvy, Andrzej Filinski
-- but a bit hacky, using (∀α. CPS α α τ) ↔ τ

newtype CPS β α τ = CPS { runCPS :: (τ -> α) -> β }
instance IxFunctor CPS where
	imap f (CPS a) = CPS \k -> a (k . f)
instance IxPointed CPS where
	ireturn v = CPS \k -> k v
instance IxApplicative CPS where
	iap (CPS f) (CPS a) = CPS \k -> f \f -> a \a -> k (f a)
instance IxMonad CPS where
	ibind f (CPS a) = CPS \k -> a \a -> runCPS (f a) k
reset :: CPS τ σ σ -> CPS α α τ
reset (CPS e) = CPS \k -> k (e id)
shift :: ((forall δ. τ -> CPS δ δ α) -> CPS β σ σ) -> CPS β α τ
shift f = CPS \k -> runCPS (f \x -> ireturn (k x)) id
tester :: forall δ. CPS δ δ ()
tester = ireturn ()

data Trail (μ :: [(Type, Type)]) where
	TNull :: Trail '[]
	TCons :: K τ₁ τ₂ μ -> Trail ('(τ₁, τ₂):μ)
type K τ₁ τ₂ μ = τ₁ -> Trail μ -> τ₂
class KId τ₁ τ₂ μ | μ τ₁ -> τ₂, μ τ₂ -> τ₁ where
	kId :: K τ₁ τ₂ μ
instance KId a a '[] where
	kId v TNull = v
instance KId τ₁ τ₂ '[ '(τ₁, τ₂)] where
	kId v (TCons k) = k v TNull
class Cons μ₁ μ₂ μ₃ where
	cons :: Trail μ₁ -> Trail μ₂ -> Trail μ₃
instance Cons μ '[] μ where
	cons k TNull = k
instance
	Cons ('(τ₁, τ₂):μ₂) μ₃ μ₁ =>
	Cons ('(a, r):μ₁) ('(τ₁, τ₂):μ₂) ('(a, r):μ₃) where
	cons (TCons k) k' = TCons \v t' -> k v (cons k' t')
instance Cons '[] μ μ where
	-- this actually comes from append
	cons TNull t = t
unwrap :: (forall α. CPS α α a) -> a
unwrap e = runCPS e id
prompt ::
	forall μid β β' τ α.
	KId β β' μid =>
	CPS (Trail '[] -> τ) (Trail μid -> β') β ->
	CPS α α τ
-- prompt e = CPS \k t -> k (runCPS e kId TNull) t
prompt e = shift \k -> reset (imap kId e) >>>= (k . ($ TNull))
-- (KId γ γ' μid, Cons μβ μ₀ μα, Cons ('(τ1, τ₂2) : μ₁) μ₂ μ₀) =>
--      ((τ2 -> CPS (Trail μ₂ -> CPS k1 k1 α) (Trail μ₁ -> τ₂2) τ1)
--            -> CPS (Trail '[] -> CPS j k3 b2) (Trail μid -> γ') γ)
--                 -> CPS (Trail μβ -> CPS j k3 b2) (Trail μα -> α) τ2
control ::
	forall
		μ₀
		μid μα
		γ' γ -- μid
		μ₂ μ₁ τ₂ τ₁
		μβ β {- μα -} α τ.
	(
		KId γ γ' μid,
		Cons ('(τ₁, τ₂):μ₁) μ₂ μ₀,
		Cons μβ μ₀ μα
	) =>
	(
		(τ -> CPS (Trail μ₂ -> α) (Trail μ₁ -> τ₂) τ₁) ->
		CPS (Trail '[] -> β) (Trail μid -> γ') γ
	) ->
	CPS (Trail μβ -> β) (Trail μα -> α) τ
-- control e = CPS \k t -> runCPS
--   (e \x -> CPS \k' t' -> k x $ cons t $ cons (TCons k') t')
--   kId TNull
control e = shift \k -> ireturn \t ->
	runCPS (imap kId $ e \x ->
		shift \k' -> ireturn \t' ->
			unwrap (k x) $
				cons @μβ @μ₀ @μα t $
				cons @('(τ₁, τ₂):μ₁) @μ₂ @μ₀ (TCons (\y -> unwrap (k' y))) t'
	) id TNull

wrapper e = reset (imap kId e) >>>= ($ TNull)
run e = runCPS (imap kId e) id TNull

test :: forall t. CPS (Trail '[] -> t) (Trail '[] -> t) String
test = --run $
	tester @(Trail '[] -> t) >>>= \_ ->
	prompt (
		tester @(Trail '[] -> String) >>>= \_ ->
		control
			@['(Int, String), '(Bool, String)]
			@'[ '(Bool, String)]
			@['(Int, String), '(Bool, String)]
			(\f ->
				tester @(Trail '[] -> String) >>>= \_ ->
				f (5 :: Int) >>>= \(v :: Int) ->
				-- imap (== (0 :: Int)) $ f (5 :: Int)
				tester @(Trail '[ '(Bool, String)] -> String) >>>= \_ ->
				ireturn (v == 0)
				)
			>>>= \(a :: Int) ->
		tester @(Trail '[ '(Int, String), '(Bool, String)] -> String) >>>= \_ ->
		control
			@'[ '(Bool, String)]
			@'[]
			@'[ '(Int, String)]
			(\f ->
				tester @(Trail '[] -> String) >>>= \_ ->
				f (8 :: Int) >>>= \(v :: Bool) ->
				-- imap (show :: Bool -> String) $ f (8 :: Int)
				tester @(Trail '[] -> String) >>>= \_ ->
				ireturn (show v)
				)
			>>>= \(b :: Int) ->
		tester @(Trail '[ '(Int, String)] -> String) >>>= \_ ->
		ireturn (a + b)
	) >>>= \v ->
	tester @(Trail '[] -> t) >>>= \_ ->
	ireturn v
