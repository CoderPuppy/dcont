{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE BlockArguments, LambdaCase, GADTs, PolyKinds, DataKinds, TypeOperators, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, RankNTypes #-}

module Types3 where

import Control.Monad.Indexed
import Data.Kind

-- takes the type system from this paper
-- A Functional Abstraction of Typed Trails
-- by Kenichi Asai, Youyou Cong, Chiaki Ishio
-- but implement it on top of the type system from this paper
-- A Functional Abstraction of Typed Contexts
-- by Olivier Danvy, Andrzej Filinski
-- properly this time using shift/reset
-- so more akin to these papers
-- Shift to Control by Chung-chieh Shan
-- A static simulation of dynamic delimited control by Chung-chieh Shan

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

data Trail (μ :: [(Type, Type)]) where
	TNull :: Trail '[]
	TCons :: K τ₁ τ₂ μ -> Trail ('(τ₁, τ₂):μ)
newtype Trailed τ₂ μ = Trailed { runTrailed :: forall α. Trail μ -> CPS α α τ₂ }
newtype K τ₁ τ₂ μ = K { runK :: forall α. τ₁ -> CPS α α (Trailed τ₂ μ) }
class KId τ₁ τ₂ μ | μ τ₁ -> τ₂, μ τ₂ -> τ₁ where
	kId :: K τ₁ τ₂ μ
instance KId a a '[] where
	kId = K \v -> ireturn $ Trailed \TNull -> ireturn v
instance KId τ₁ τ₂ '[ '(τ₁, τ₂)] where
	kId = K \v -> ireturn $ Trailed \(TCons k) -> runK k v >>>= flip runTrailed TNull
class Cons μ₁ μ₂ μ₃ where
	cons :: Trail μ₁ -> Trail μ₂ -> Trail μ₃
instance Cons μ '[] μ where
	cons k TNull = k
instance
	Cons ('(τ₁, τ₂):μ₂) μ₃ μ₁ =>
	Cons ('(a, r):μ₁) ('(τ₁, τ₂):μ₂) ('(a, r):μ₃) where
	cons (TCons k) k' = TCons $ K \v -> ireturn $ Trailed \t' -> runK k v >>>= flip runTrailed (cons k' t')
instance Cons '[] μ μ where
	-- this actually comes from append
	cons TNull t = t
prompt ::
  forall μid β β' τ α.
  KId β β' μid =>
  CPS (Trailed τ '[]) (Trailed β' μid) β ->
  CPS α α τ
prompt e = reset (e >>>= runK kId) >>>= flip runTrailed TNull
control ::
	forall
		μ₀
		μid μα
    γ' γ -- μid
		μ₂ μ₁ τ₂ τ
		μβ β {- μα -} α τ.
  (
    KId γ γ' μid,
    Cons ('(τ₁, τ₂):μ₁) μ₂ μ₀,
    Cons μβ μ₀ μα
  ) =>
  (
    (τ -> CPS (Trailed α μ₂) (Trailed τ₂ μ₁) τ₁) ->
    CPS (Trailed β '[]) (Trailed γ' μid) γ
  ) ->
  CPS (Trailed β μβ) (Trailed α μα) τ
control e = shift \k -> ireturn $ Trailed \t ->
  reset (
    e (\x ->
      shift \k' -> ireturn $ Trailed \t' ->
        k x >>>= flip runTrailed (
          cons @μβ @μ₀ @μα t $
          cons @('(τ₁, τ₂):μ₁) @μ₂ @μ₀ (TCons $ K k') t'
        )
    ) >>>= runK kId
  ) >>>= flip runTrailed TNull

wrapper e = reset (e >>>= runK kId) >>>= flip runTrailed TNull
run e = runCPS (wrapper e) id

test = run $
  prompt (
		control
      @['(Int, String), '(Bool, String)]
      @'[ '(Bool, String)]
      @['(Int, String), '(Bool, String)]
      (\f -> imap (== (0 :: Int)) $ f (5 :: Int))
      >>>= \(a :: Int) ->
    control
      @'[ '(Bool, String)]
      @'[]
      @'[ '(Int, String)]
      (\f -> imap (show :: Bool -> String) $ f (8 :: Int))
      >>>= \(b :: Int) ->
    ireturn (a + b)
	)
