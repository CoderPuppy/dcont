{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE BlockArguments, LambdaCase, GADTs, PolyKinds, DataKinds, TypeOperators, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, RankNTypes #-}

module TypesKiselyov2 where

import Control.Monad.Indexed
import Data.Kind
import Data.Proxy

-- start with the type system from
-- A Functional Abstraction of Typed Contexts
-- by Olivier Danvy, Andrzej Filinski
-- and implement dynamic continuation operators using
-- How to remove a dynamic prompt: static and dynamic delimited continuation operators are equally expressible
-- by Oleg Kiselyov
-- hiding more types by using functions

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

class Interp strat h β α where
	type InterpV strat h β α :: Type
	interp :: h -> CPS β α (InterpV strat h β α)
data HV a = HV a
data H f = H f

data Stop = Stop
instance β ~ α => Interp 'Stop (HV τ) β α where
	type InterpV 'Stop (HV τ) β α = τ
	interp (HV v) = ireturn v
instance
	(
		Interp 'Stop h β α,
		τ' ~ τ, β ~ α, δ' ~ δ
	) =>
	Interp 'Stop (H ((a -> CPS δ' δ a) -> CPS h (HV τ') τ)) β α
	where
		type InterpV 'Stop (H ((a -> CPS δ' δ a) -> CPS h (HV τ') τ)) β α = InterpV 'Stop h β α
		interp (H f) = reset' @'Stop (f ireturn)

data Propogate = PropReset | PropShift
instance β ~ α => Interp 'PropReset (HV τ) β α where
	type InterpV 'PropReset (HV τ) β α = τ
	interp (HV v) = ireturn v
instance (β' ~ β, α' ~ α, δ' ~ δ) => Interp 'PropReset (H ((a -> CPS δ' δ a) -> CPS β' α' τ)) β α where
	type InterpV 'PropReset (H ((a -> CPS δ' δ a) -> CPS β' α' τ)) β α = τ
	interp (H f) = f ireturn
instance β ~ α => Interp 'PropShift (HV τ) β α where
	type InterpV 'PropShift (HV τ) β α = τ
	interp (HV v) = ireturn v
instance
	(
		Interp 'PropShift h β δ,
		InterpV 'PropShift h β δ ~ r,
		a' ~ a, f' ~ f, α' ~ α
	) =>
	Interp 'PropShift
		(H ((τ -> CPS β α a) -> f))
		(H ((r -> CPS δ α' a') -> f'))
		h
	where
		type InterpV 'PropShift
			(H ((τ -> CPS β α a) -> f))
			(H ((r -> CPS δ α' a') -> f'))
			h
			= τ
		interp (H f) = shift \k' -> ireturn $
			H $ f . (<<=<< (interp @'PropShift <<=<< k'))

reset' ::
	forall strat h β α τ.
	Interp strat h β α =>
	CPS h (HV τ) τ ->
	CPS β α (InterpV strat h β α)
reset' e = reset (imap HV e) >>>= interp @strat
shift' ::
	forall strat h β α δ τ a f.
	Interp strat h β α =>
	((τ -> CPS β δ a) -> f) ->
	CPS (H ((InterpV strat h β α -> CPS α δ a) -> f)) h τ
shift' f = shift \k -> ireturn $ H $ f . (<<=<< (interp @strat <<=<< k))

-- {-
test :: forall α. CPS α α String
test =
	-- tester @() >>>= \_ ->
	tester @α >>>= \_ ->
	reset'
		@'Stop
		@(H (
			(Int -> CPS (HV Bool) (HV Bool) Int) ->
			CPS
				(H (
					(Bool -> CPS (HV String) (HV String) Bool) ->
					CPS (HV String) (HV String) String
				))
				(HV Bool) Bool
		))
		(
			tester @(H ((Int -> CPS (HV Bool) (HV Bool) Int) -> CPS (H ((Bool -> CPS (HV String) (HV String) Bool) -> CPS (HV String) (HV String) String)) (HV Bool) Bool)) >>>= \_ ->
			shift' @'PropShift
				(\f ->
					tester @(H ((Bool -> CPS (HV String) (HV String) Bool) -> CPS (HV String) (HV String) String)) >>>= \_ ->
					f (5 :: Int) >>>= \(v :: Int) ->
					-- imap (== (0 :: Int)) $ f (5 :: Int)
					tester @(HV Bool) >>>= \_ ->
					ireturn @CPS (v == 0)
					)
				>>>= \(a :: Int) ->
			shift' @'PropShift
				(\f ->
					tester @(HV String) >>>= \_ ->
					f (8 :: Int) >>>= \(v :: Bool) ->
					-- imap (show :: Bool -> String) $ f (8 :: Int)
					tester @(HV String) >>>= \_ ->
					ireturn @CPS (show v)
					)
				>>>= \(b :: Int) ->
			tester @(HV Int) >>>= \_ ->
			ireturn @CPS (a + b)
		)
		>>>= \v ->
	tester @α >>>= \_ ->
	ireturn v
-- -}
