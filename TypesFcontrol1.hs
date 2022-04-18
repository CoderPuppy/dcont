{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE BlockArguments, LambdaCase, GADTs, PolyKinds, DataKinds, TypeOperators, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, RankNTypes #-}

module TypesFcontrol1 where

import Control.Monad.Indexed
import Data.Kind
import Data.Proxy

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

data H f t where
  Normal :: v -> H f (CPS δ δ v)
  FControl :: v -> (τ -> CPS δ δ r) -> H (v -> (τ -> CPS δ δ r) -> f) f

fcontrol :: v -> CPS (H (v -> (τ -> CPS δ δ r) -> f) f) r τ
fcontrol v = shift \k -> ireturn $ FControl v k

handle ::
  (a -> (ka -> CPS kβ kα r) -> CPS fβ fα fτ) ->
  CPS
    (H
      (a -> (ka -> CPS kβ kα r) -> CPS fβ fα fτ)
      (CPS β α τ))
    (H f' (CPS δ δ r))
    r ->
  CPS β α τ
handle f b = reset (imap Normal b) >>>= \case
  Normal v -> ireturn v
  FControl v k -> f v k
