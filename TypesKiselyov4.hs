{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE BlockArguments, LambdaCase, GADTs, PolyKinds, DataKinds, TypeOperators, TypeFamilies, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, RankNTypes #-}

module TypesKiselyov4 where

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

class H h f where
	h :: f -> h
class HV h where
	hv :: r -> h r

data HStop r
	= HVStop r
	| forall a τ h. HV h => HStop ((forall δ. a -> CPS δ δ a) -> CPS (HStop r) (h τ) τ)
instance HV HStop where
	hv = HVStop
instance HV h => H (HStop r) ((a -> CPS δ δ a) -> CPS (HStop r) (h τ) τ) where
	h = HStop

interpHStop :: HStop r -> CPS δ δ r
interpHStop (HVStop v) = ireturn v
interpHStop (HStop f) = resetStop (f ireturn)

resetStop :: HV h => CPS (HStop r) (h τ) τ -> CPS δ δ r
resetStop e = reset (imap hv e) >>>= interpHStop
shiftStop ::
	HV h =>
	((forall α. τ -> CPS α α a) -> CPS (HStop r) (h τ') τ') ->
	CPS (HStop r) (HStop a) τ
shiftStop f = shift \k -> ireturn $ HStop \k' ->
	f $ k' <<=<< interpHStop <<=<< k

data HPropShift β α r where
	HVPropShift :: r -> HPropShift δ δ r
	HPropShift ::
		H h ((τ2 -> CPS δ α a) -> f) =>
		((τ -> CPS β α a) -> f) ->
		HPropShift h (HPropShift β δ τ2) τ
instance HV (HPropShift δ δ) where
	hv = HVPropShift
instance
	H h ((τ2 -> CPS δ α a) -> f) =>
	H (HPropShift h (HPropShift β δ τ2) τ) ((τ -> CPS β α a) -> f)
	where h = HPropShift

interpHPropShift :: HPropShift β α τ -> CPS β α τ
interpHPropShift (HVPropShift v) = ireturn v
interpHPropShift (HPropShift f) = shift \k' -> ireturn $ h $ f . (<<=<< (interpHPropShift <<=<< k'))

shiftProp ::
	H h ((b -> CPS δ α a) -> f) =>
	((τ -> CPS β α a) -> f) ->
	CPS h (HPropShift β δ b) τ
shiftProp f = shift \k -> ireturn $ h $ f . (<<=<< (interpHPropShift <<=<< k))
