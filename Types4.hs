{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE BlockArguments, LambdaCase, GADTs, PolyKinds, DataKinds, TypeOperators, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, RankNTypes #-}

module Types4 where

import Control.Monad.Indexed
import Data.Kind
import Data.Proxy

-- start with the type system from
-- A Functional Abstraction of Typed Contexts
-- by Olivier Danvy, Andrzej Filinski
-- and implement dynamic continuation operators using
-- How to remove a dynamic prompt: static and dynamic delimited continuation operators are equally expressible
-- by Oleg Kiselyov

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
data H k f = H k f

data Stop = Stop
instance β ~ α => Interp 'Stop (HV τ) β α where
	type InterpV 'Stop (HV τ) β α = τ
	interp (HV v) = ireturn v
instance
	(
		Interp 'Stop h β α,
		k' ~ k, τ' ~ τ, β ~ α
	) =>
	Interp 'Stop (H k (k' -> CPS h (HV τ') τ)) β α
	where
		type InterpV 'Stop (H k (k' -> CPS h (HV τ') τ)) β α = InterpV 'Stop h β α
		interp (H k f) = reset' @'Stop (f k)

data Propogate = PropReset | PropShift
instance β ~ α => Interp 'PropReset (HV τ) β α where
	type InterpV 'PropReset (HV τ) β α = τ
	interp (HV v) = ireturn v
instance (k' ~ k, β' ~ β, α' ~ α) => Interp 'PropReset (H k (k' -> CPS β' α' τ)) β α where
	type InterpV 'PropReset (H k (k' -> CPS β' α' τ)) β α = τ
	interp (H k f) = f k
instance β ~ α => Interp 'PropShift (HV τ) β α where
	type InterpV 'PropShift (HV τ) β α = τ
	interp (HV v) = ireturn v
instance
	(
		Interp 'PropShift h j k,
		InterpV 'PropShift h j k ~ r,
		i' ~ i, a' ~ a, f' ~ f
	) =>
	Interp 'PropShift
		(H (a -> CPS i j τ) f)
		(H (a' -> CPS i' k r) f')
		h
	where
		type InterpV 'PropShift
			(H (a -> CPS i j τ) f)
			(H (a' -> CPS i' k r) f')
			h
			= τ
		interp (H k f) = shift \k' -> ireturn $
			H (interp @'PropShift <<=<< k' <<=<< k) f

reset' ::
	forall strat h β α τ.
	Interp strat h β α =>
	CPS h (HV τ) τ ->
	CPS β α (InterpV strat h β α)
reset' e = reset (imap HV e) >>>= interp @strat
shift' ::
	forall strat h β α f τ.
	Interp strat h β α =>
	f -> CPS (H (τ -> CPS β α (InterpV strat h β α)) f) h τ
shift' f = shift \k -> ireturn $ H (interp @strat <<=<< k) f

-- this is more complicated than I thought
class DynamicWind h i k where
	type DynamicWindA h i k :: Type
	type DynamicWindV h i k :: Type
	dynamicWind ::
		CPS i j b ->
		CPS h (HV τ) τ ->
		CPS j k a ->
		CPS i (DynamicWindA h i k) (DynamicWindV h i k)
instance DynamicWind (HV τ) i k where
	type DynamicWindA (HV τ) i k = k
	type DynamicWindV (HV τ) i k = τ
	dynamicWind before body after =
		before >>>= \_ ->
		reset (imap HV body) >>>= \(HV res) ->
		after >>>= \_ ->
		ireturn res
instance
	(
		DynamicWind h i k,
		DynamicWindA h i k ~ a
	) =>
	DynamicWind
		(H
			(τ -> CPS h (HV τ') τ')
			((τ -> CPS i a k') -> CPS k σ σ))
		i k
	where
		type DynamicWindA
			(H
				(τ -> CPS h (HV τ') τ')
				((τ -> CPS i a k') -> CPS k σ σ))
			i k
			= k'
		type DynamicWindV
			(H
				(τ -> CPS h (HV τ') τ')
				((τ -> CPS i a k') -> CPS k σ σ))
			i k
			= DynamicWindV h i k
		dynamicWind before body after =
			before >>>= \_ ->
			reset (imap HV body) >>>= \(H k f) ->
			after >>>= \_ ->
			shift \k' -> f \x ->
				dynamicWind before (k x) after >>>= \y ->
				k' y

-- {-
test :: forall α. CPS α α String
test =
	tester @α >>>= \_ ->
	reset'
		@'Stop
		-- @(H _ (_ -> CPS (H _ ((_ -> CPS _ _ _) -> CPS _ (HV _) _)) (HV _) _))
		@(H
			(Int -> CPS
				(H
					(Int -> CPS (HV String) (HV String) Bool)
					(
						(Int -> CPS (HV String) (HV String) Bool) ->
						CPS (HV String) (HV String) String
					))
				(HV Bool) Int)
			(
				(Int -> CPS
					(H
						(Int -> CPS (HV String) (HV String) Bool)
						(
							(Int -> CPS (HV String) (HV String) Bool) ->
							CPS (HV String) (HV String) String
						))
					(HV Bool) Int) ->
				CPS
					(H
						(Int -> CPS (HV String) (HV String) Bool)
						(
							(Int -> CPS (HV String) (HV String) Bool) ->
							CPS (HV String) (HV String) String))
					(HV Bool) Bool
			))
		(
			tester @(H (Int -> CPS (H (Int -> CPS (HV String) (HV String) Bool) ((Int -> CPS (HV String) (HV String) Bool) -> CPS (HV String) (HV String) String)) (HV Bool) Int) ((Int -> CPS (H (Int -> CPS (HV String) (HV String) Bool) ((Int -> CPS (HV String) (HV String) Bool) -> CPS (HV String) (HV String) String)) (HV Bool) Int) -> CPS (H (Int -> CPS (HV String) (HV String) Bool) ((Int -> CPS (HV String) (HV String) Bool) -> CPS (HV String) (HV String) String)) (HV Bool) Bool)) >>>= \_ ->
			shift' @'PropShift
				(\f ->
					tester @(H (Int -> CPS (HV String) (HV String) Bool) ((Int -> CPS (HV String) (HV String) Bool) -> CPS (HV String) (HV String) String)) >>>= \_ ->
					f (5 :: Int) >>>= \(v :: Int) ->
					-- imap (== (0 :: Int)) $ f (5 :: Int)
					tester @(HV Bool) >>>= \_ ->
					ireturn (v == 0)
					)
				>>>= \(a :: Int) ->
			tester @(H (Int -> CPS (HV String) (HV String) Int) ((Int -> CPS (HV String) (HV String) Bool) -> CPS (HV String) (HV String) String)) >>>= \_ ->
			shift' @'PropShift
				(\f ->
					tester @(HV String) >>>= \_ ->
					f (8 :: Int) >>>= \(v :: Bool) ->
					-- imap (show :: Bool -> String) $ f (8 :: Int)
					tester @(HV String) >>>= \_ ->
					ireturn (show v)
					)
				>>>= \(b :: Int) ->
			tester @(HV Int) >>>= \_ ->
			ireturn @CPS (a + b)
		)
		>>>= \v ->
	tester @α >>>= \_ ->
	ireturn v

test2 :: forall α. CPS α α (Int, Int)
test2 =
	reset' @'PropReset
		@(H
			(Int -> CPS α α Int)
			(
				(Int -> CPS α α Int) ->
				CPS α α (Int, Int)
			))
		(
			reset'
				@'PropReset
				@(H
					(Int -> CPS α α Int)
					(
						(Int -> CPS α α Int) ->
						CPS
							(H
								(Int -> CPS α α Int)
								(
									(Int -> CPS α α Int) ->
									CPS α α (Int, Int)
								))
							(HV Int)
							Int
					))
				(
					shift' @'Stop
						(\k1 -> shift' @'Stop \k2 ->
							k1 (3 :: Int) >>>= \(a :: Int) ->
							k2 (4 :: Int) >>>= \(b :: Int) ->
							ireturn @CPS (a, b))
						>>>= \(b :: Int) -> ireturn @CPS (b * 100)
				)
				>>>= \(a :: Int) -> ireturn @CPS (a * 10)
		)
-- -}
