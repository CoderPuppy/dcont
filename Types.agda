{-# OPTIONS --type-in-type #-}

module Types where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; _∷_; lookup)
import Data.Fin as Fin

module sr where
  data Type : Set where
    arr : Type → Type → Type → Type → Type
  data Term : (n : ℕ) → Vec Type n → Type -> Type -> Type -> Set where
    var : ∀{n ρ δ} → (i : Fin n) → Term n ρ δ (lookup ρ i) δ
    reset : ∀{n ρ σ α τ} → Term n ρ σ σ τ -> Term n ρ α τ α
    shift : ∀{n ρ δ σ α β τ} → Term (suc n) (arr τ δ α δ ∷ ρ) σ σ β → Term n ρ α τ β
    fn : ∀{n ρ σ α τ β δ} → Term (suc n) (σ ∷ ρ) α τ β → Term n ρ δ (arr σ α τ β) δ
    app : ∀{n ρ δ σ α τ ε β} → Term n ρ δ (arr σ α τ ε) β → Term n ρ ε σ δ → Term n ρ α τ β

  postulate
    incr : ∀{n ρ α τ β τ'} → Term n ρ α τ β → Term (suc n) (τ' ∷ ρ) α τ β

  module pc where
    postulate
      Inter : Type → Type → Type → Type
      H :
        ∀{n ρ δ α β τ₁ τ₂ τ₃} →
        Term n ρ β τ₁ δ →
        Term n ρ δ τ₂ α →
        Term n ρ β (Inter τ₁ τ₂ τ₃) α
      HV :
        ∀{n ρ α β τ₁ τ₂ τ₃} →
        Term n ρ β τ₃ α →
        Term n ρ β (Inter τ₁ τ₂ τ₃) α
      Inter-case :
        ∀{n ρ α β δ τ₁ τ₂ τ₃ τ} →
        Term n ρ δ (Inter τ₁ τ₂ τ₃) α →
        Term (suc (suc n)) (τ₂ ∷ τ₁ ∷ ρ) β τ δ →
        Term (suc n) (τ₃ ∷ ρ) β τ δ →
        Term n ρ β τ α
    w2 : Type -> Type -> Type → Type
    w2 τ₁ τ₂ τ = Inter τ₁ τ₂ τ
    {-# TERMINATING #-}
    w1 : Type -> Type -> Type -> Type → Type
    w1 τ₁ τ₂ β τ = Inter β (arr β (w2 τ₁ τ₂ τ) τ (w1 τ₁ τ₂ β τ)) τ
    {-# TERMINATING #-}
    prompt :
      ∀{n ρ α τ β τ₁ τ₂} →
      Term n ρ (w2 τ₁ τ₂ τ) τ (w1 τ₁ τ₂ β τ) →
      Term n ρ α τ α
    prompt e = Inter-case
      (reset (HV e))
      (prompt (app (var Fin.zero) (var (Fin.suc Fin.zero))))
      (var Fin.zero)
    {-# TERMINATING #-}
    w3 : Type → Type → Type → Type → Type
    w3 τ₁ τ₂ τ₃ τ = Inter (arr τ₁ (w3 τ₁ τ₂ τ₃ τ) τ τ₂) τ₃ τ
    {-# TERMINATING #-}
    h' :
      ∀{n ρ τ τ₁ τ₂ τ₃ α β} →
      Term n ρ
        (Inter (arr ? (w3 τ₁ τ₂ τ₃ τ) τ ?) ? τ)
        (Inter (arr ? (w3 τ₁ τ₂ τ₃ τ) τ ?) ? τ)
        ? →
      Term n ρ
        (Inter (arr ? (Inter (arr ? (Inter ? ? ?) τ ?) ? τ) τ ?) ? τ)
        τ
        ?
    h' e = Inter-case e
      (shift (H
        (fn (h'
          (app (var (Fin.suc Fin.zero))
            (app (var (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
              (var Fin.zero)))))
        (var (Fin.suc Fin.zero))))
      (var Fin.zero)
    control :
      ∀{n ρ} →
      Term (suc n) (? ∷ ρ) ? ? ? →
      Term n ρ ? ? ?
    control e = shift (H
      (fn (h' (app (var (Fin.suc Fin.zero)) (var Fin.zero))))
      (incr (fn e)))
