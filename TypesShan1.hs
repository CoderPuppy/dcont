{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE BlockArguments, LambdaCase, GADTs, PolyKinds, DataKinds, TypeOperators, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts, ScopedTypeVariables, TypeApplications, UndecidableInstances, AllowAmbiguousTypes #-}

module TypesShan1 where

import Data.Kind

-- direct implementation of a paper
-- A Functional Abstraction of Typed Trails
-- by Kenichi Asai, Youyou Cong, Chiaki Ishio

data Trail (μ :: [(Type, Type)]) where
	TNull :: Trail '[]
	TCons :: (τ₁ -> Trail μ -> τ₂) -> Trail ('(τ₁, τ₂):μ)
runTCons :: Trail ('(τ₁, τ₂):μ) -> τ₁ -> Trail μ -> τ₂
runTCons (TCons k) = k
type K τ₁ μ τ₂ = τ₁ -> Trail μ -> τ₂
type CPS μβ β μα α τ = K (K τ μα α) μβ β

class KId (μ :: [(Type, Type)]) τ₁ τ₂ | μ τ₁ -> τ₂ where
	kId :: K τ₁ μ τ₂
instance KId '[] a a where
	kId v TNull = v
instance KId '[ '(τ₁, τ₂)] τ₁ τ₂ where
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

prompt ::
	KId μid β β' =>
	CPS '[] τ μid β' β ->
	-- (
	--   (β -> Trail μid -> β') ->
	--   Trail '[] -> τ
	-- ) ->
	CPS μα α μα α τ
	-- (τ -> Trail μα -> α) ->
	-- Trail μα -> α
prompt e = \k t -> k (e kId TNull) t
control ::
	forall
		μ₀
		μ₂ μ₁ τ₂ τ₁
		μid γ' γ
		μβ β μα α τ.
	(
		KId μid γ γ',
		Cons ('(τ₁, τ₂):μ₁) μ₂ μ₀,
		Cons μβ μ₀ μα
		-- Cons ('(τ, α):μα) μβ ('(τ, α):μ₀),
		-- Cons ('(τ₁, τ₂):μ₁) μ₂ μ₀
	) =>
	(
		(τ -> CPS μ₂ α μ₁ τ₂ τ₁) ->
		-- (
		--   τ ->
		--   (τ₁ -> Trail μ₁ -> τ₂) ->
		--   Trail μ₂ -> α
		-- ) ->
		CPS '[] β μid γ' γ
		-- (γ -> Trail μid -> γ') ->
		-- Trail '[] -> β
	) ->
	CPS μβ β μα α τ
	-- (τ -> Trail μα -> α) ->
	-- Trail μβ -> β
control e = \k t -> e
	(\x k' t' -> k x $
		cons @μβ @μ₀ @μα t $
		cons @('(τ₁, τ₂):μ₁) @μ₂ @μ₀ (TCons k') t')
	-- (\x k' t' ->
	-- 	runTCons
	-- 		(cons @('(τ, α):μα) @μβ @('(τ, α):μ₀) (TCons k) t)
	-- 		x
	-- 		(cons @('(τ₁, τ₂):μ₁) @μ₂ @μ₀ (TCons k') t')
	-- )
	kId TNull

test = prompt
	(\(k :: K Int '[ '(Int, String)] String) (t :: Trail '[]) ->
		control @['(Int, String), '(Bool, String)]
			(\f (k :: K Bool '[ '(Bool, String)] String) (t :: Trail '[]) ->
				f (5 :: Int)
					(\(v :: Int) (t :: Trail '[ '(Bool, String)]) ->
						k (v == 0) t
					)
					t
			)
			(\(a :: Int) (t :: Trail '[ '(Int, String), '(Bool, String) ]) ->
				control @'[ '(Bool, String)]
					(\f (k :: K String '[] String) (t :: Trail '[]) ->
						f (8 :: Int)
							(\(v :: Bool) (t :: Trail '[]) ->
								k (show v) t
							)
							t
					)
					(\(b :: Int) (t :: Trail '[ '(Int, String) ]) ->
						k (a + b) t
					)
					t
			)
			t
	)
	kId
	TNull
