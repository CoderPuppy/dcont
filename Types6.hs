{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE BlockArguments, LambdaCase, GADTs, PolyKinds, DataKinds, TypeOperators, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, RankNTypes #-}

module Types6 where

import Control.Monad.Indexed
import Data.Kind
import Data.Proxy

-- start with the type system from
-- A Functional Abstraction of Typed Contexts
-- by Olivier Danvy, Andrzej Filinski
-- and implement dynamic continuation operators using
-- How to remove a dynamic prompt: static and dynamic delimited continuation operators are equally expressible
-- by Oleg Kiselyov
-- hiding types to be instantiated at shifts vs resets

infixr 1 >>=>>, <<=<<
(>>=>>) :: IxMonad m => (a -> m i j b) -> (b -> m j k c) -> a -> m i k c
(f >>=>> g) x = f x >>>= g
(<<=<<) :: IxMonad m => (b -> m j k c) -> (a -> m i j b) -> a -> m i k c
(f <<=<< g) x = g x >>>= f

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

class InterpH strat c β α τ where
	interpH :: c -> CPS β α τ
data H strat β α τ where
	HV :: τ -> H strat α α τ
	H :: InterpH strat c β α τ => c -> H strat β α τ
interp :: forall strat β α τ. H strat β α τ -> CPS β α τ
interp (HV v) = ireturn v
interp (H c) = interpH @strat c

data Stop = Stop
instance
	(τ' ~ τ, δ' ~ δ, σ' ~ σ, β' ~ β, α' ~ α, a' ~ a, r' ~ r, β ~ α) =>
	InterpH 'Stop ((a' -> CPS δ' δ a) -> CPS (H 'Stop β' α' r') (H strat σ' σ τ') τ) β α r
	where
		interpH f = reset' @'Stop (f ireturn)
data Propogate = PropReset | PropShift
instance
	(a' ~ a, δ' ~ δ, β' ~ β, α' ~ α, τ' ~ τ) =>
	InterpH 'PropReset ((a' -> CPS δ' δ a) -> CPS β' α' τ') β α τ
	where
		interpH f = f ireturn
instance
	(
		InterpH strat ((τ2 -> CPS δ α a) -> f) β'' α'' τ3,
		τ' ~ τ, β' ~ β
	) =>
	InterpH 'PropShift
		((τ' -> CPS β α a) -> f)
		(H strat β'' α'' τ3)
		(H 'PropShift β' δ τ2)
		τ
	where
		interpH f = shift \k' -> ireturn $ H $ f . (<<=<< (interp @'PropShift <<=<< k'))

reset' ::
	forall stratβ stratα β α δ τ r.
	CPS (H stratβ β α r) (H stratα δ δ τ) τ ->
	CPS β α r
reset' e = reset (imap HV e) >>>= interp @stratβ
shift' ::
	forall stratα stratβ β δ α β' α' a b f τ τ'.
	InterpH stratβ ((b -> CPS δ α a) -> f) β' α' τ' =>
	((τ -> CPS β α a) -> f) ->
	CPS (H stratβ β' α' τ') (H stratα β δ b) τ
shift' f = shift \k -> ireturn $ H $ f . (<<=<< (interp @stratα <<=<< k))

-- {-
test :: forall α. CPS α α String
test =
	tester @α >>>= \_ ->
	reset'
		@'Stop
		(
			tester @(H 'Stop α α String) >>>= \_ ->
			shift' @'PropShift
				(\f ->
					tester @(H 'Stop α α String) >>>= \_ ->
					f (5 :: Int) >>>= \(v :: Int) ->
					-- imap (== (0 :: Int)) $ f (5 :: Int)
					tester @(H 'PropShift (H 'Stop α α String) (H 'Stop α α String) Bool) >>>= \_ ->
					ireturn @CPS (v == 0)
					)
				>>>= \(a :: Int) ->
			tester @(H 'PropShift (H 'Stop α α String) (H 'PropShift (H 'Stop α α String) (H 'Stop α α String) Bool) Int) >>>= \_ ->
			shift' @'PropShift
				(\f ->
					tester @(H 'Stop α α String) >>>= \_ ->
					f (8 :: Int) >>>= \(v :: Bool) ->
					-- imap (show :: Bool -> String) $ f (8 :: Int)
					tester @(H 'Stop α α String) >>>= \_ ->
					ireturn @CPS (show v)
					)
				>>>= \(b :: Int) ->
			tester @(H 'PropShift (H 'Stop α α String) (H 'Stop α α String) Int) >>>= \_ ->
			ireturn @CPS (a + b)
		)
		>>>= \v ->
	tester @α >>>= \_ ->
	ireturn v
-- -}

test2 ::
	forall strat1 strat2 t0 t1 t2 t3 t4 t5 t7 t8 t9 t10 t11 t12.
	(
		InterpH strat1
			(
				(Int -> CPS (H 'PropShift t0 t7 Bool) (H 'PropShift t1 t2 Bool) Int) ->
				CPS (H strat2 t9 t10 t11) (H 'PropShift t1 t2 Bool) Bool)
			t3 t4 t5,
		InterpH strat2
			((Bool -> CPS t7 t12 Bool) -> CPS t8 t12 String)
			t9 t10 t11
	) =>
	CPS (H strat1 t3 t4 t5) (H 'PropShift t8 t0 Int) Int
test2 =
			tester @(H strat1 t3 t4 t5) >>>= \_ ->
			shift' @'PropShift
				(\f ->
					tester @(H strat2 t9 t10 t11) >>>= \_ ->
					f (5 :: Int) >>>= \(v :: Int) ->
					-- imap (== (0 :: Int)) $ f (5 :: Int)
					tester @(H 'PropShift t1 t2 Bool) >>>= \_ ->
					ireturn @CPS (v == 0)
					)
				>>>= \(a :: Int) ->
			tester @(H 'PropShift (H strat2 t9 t10 t11) (H 'PropShift t0 t7 Bool) Int) >>>= \_ ->
			shift' @'PropShift
				(\f ->
					tester @t8 >>>= \_ ->
					f (8 :: Int) >>>= \(v :: Bool) ->
					-- imap (show :: Bool -> String) $ f (8 :: Int)
					tester @t12 >>>= \_ ->
					ireturn @CPS (show v)
					)
				>>>= \(b :: Int) ->
			tester @(H 'PropShift t8 t0 Int) >>>= \_ ->
			ireturn @CPS (a + b)
