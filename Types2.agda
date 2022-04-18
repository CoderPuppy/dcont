{-# OPTIONS --type-in-type #-}

module Types2 where

-- attempting to prove equivalence of all my type experiments

data ⊤ : Set where
  unit : ⊤

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data Fin : ℕ → Set where
  fzero : (n : ℕ) → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)

data List (A : Set) : Set where
  [l] : List A
  _∷l_ : A → List A → List A

data Vec (A : Set) : ℕ → Set where
  [v] : Vec A zero
  _∷v_ : {n : ℕ} → A → Vec A n → Vec A (succ n)
lookup : ∀{n A} → Fin n → Vec A n → A
lookup (fzero _) (x ∷v _) = x
lookup (fsucc i) (_ ∷v xs) = lookup i xs

record _×_ (τ₁ τ₂ : Set) : Set where
  constructor _,_
  field
    proj₁ : τ₁
    proj₂ : τ₂

data Type : Set where
  Lift : {A : Set} → A → Type
  Arr : Type → Type → Type → Type → Type

data Operator : Set where
  prompt control : Operator

data Expr (v : ℕ) : Set where
  var : Fin v → Expr v
  lam : Expr (succ v) → Expr v
  app : Expr v → Expr v → Expr v
  lift : {A : Set} → A → Expr v

module TypeJudge (⊢_∷_ : {A : Set} → A → Type → Set) where
  data _⊢_∷_[_⇒_] {v : ℕ} (Γ : Vec Type v) : Expr v → Type → Type → Type → Set where
    I-var : ∀{γ i} → Γ ⊢ var i ∷ lookup i Γ [ γ ⇒ γ ]
    I-lam : ∀{τ₁ τ₂ α β γ e} →
      (τ₁ ∷v Γ) ⊢ e ∷ τ₂ [ α ⇒ β ] →
      Γ ⊢ lam e ∷ Arr τ₁ τ₂ α β [ γ ⇒ γ ]
    I-app : ∀{f a τ₁ τ₂ α β γ δ} →
      Γ ⊢ f ∷ Arr τ₁ τ₂ α β [ γ ⇒ δ ] →
      Γ ⊢ a ∷ τ₁ [ β ⇒ γ ] →
      Γ ⊢ app f a ∷ τ₂ [ α ⇒ δ ]
    I-lift : ∀{A τ γ} {x : A} →
      ⊢ x ∷ τ →
      Γ ⊢ lift x ∷ τ [ γ ⇒ γ ]

module Shan3 where
  data Trailed : Type → List (Type × Type) → Set where

  data ⊢kId : Type → Type → List (Type × Type) → Set where
    I-kId0 : ∀{τ} → ⊢kId τ τ [l]
    I-kId1 : ∀{τ τ'} → ⊢kId τ τ' ((τ , τ') ∷l [l])

  data ⊢cons : List (Type × Type) → List (Type × Type) → List (Type × Type) → Set where
    I-consX0 : ∀{μ} → ⊢cons μ [l] μ
    I-cons0X : ∀{μ} → ⊢cons [l] μ μ
    I-consCons : ∀{a r τ₁ τ₂ μ₁ μ₂ μ₃} →
      ⊢cons ((τ₁ , τ₂) ∷l μ₂) μ₃ μ₁ →
      ⊢cons ((a , r) ∷l μ₁) ((τ₁ , τ₂) ∷l μ₂) ((a , r) ∷l μ₃)

  data ⊢_∷_ : {A : Set} → A → Type → Set where
    I-lift : {A : Set} → (v : A) → ⊢ v ∷ Lift A
    I-prompt : ∀{β β' τ α μid} →
      ⊢kId β β' μid →
      ⊢ prompt ∷ Arr
        (Arr
          (Lift ⊤) β
          (Lift (Trailed τ [l]))
          (Lift (Trailed β' μid)))
        τ α α
    I-control : ∀{τ τ₁ τ₂ α β γ γ' μid μ₀ μ₁ μ₂ μα μβ} →
      ⊢kId γ γ' μid →
      ⊢cons ((τ₁ , τ₂) ∷l μ₁) μ₂ μ₀ →
      ⊢cons μβ μ₀ μα →
      ⊢ control ∷ Arr
        (Arr
          (Arr
            τ τ₁
            (Lift (Trailed α μ₂))
            (Lift (Trailed τ₂ μ₁)))
          γ
          (Lift (Trailed β [l]))
          (Lift (Trailed γ' μid)))
        τ
        (Lift (Trailed β μβ))
        (Lift (Trailed α μα))

  open TypeJudge (⊢_∷_)

module Kiselyov2 where
  data Hw : Set where
    H : Type → Hw
    HV : Type → Hw

  data ⊢stop : Hw → Type → Type → Type → Set where
    I-stopHV : ∀{τ α} → ⊢stop (HV τ) α α τ
    I-stopH : ∀{a τ δ α h r} →
      ⊢stop h α α r →
      ⊢stop (H (Arr
        (Arr a a δ δ)
        τ (Lift h) (Lift (HV τ)))) α α r

  data ⊢propShift : Hw → Type → Type → Type → Set where
    I-propShiftHV : ∀{τ α} → ⊢propShift (HV τ) α α τ
    I-propShiftH : ∀{h τ a f r α β α' β' δ} →
      ⊢propShift h β δ r →
      ⊢propShift
        (H (Arr
          (Arr τ a β α)
          f β' α'))
        (Lift (H (Arr
          (Arr r a δ α)
          f β' α')))
        (Lift h) τ

  data ⊢_∷_ : {A : Set} → A → Type → Set where
    I-lift : {A : Set} → (v : A) → ⊢ v ∷ Lift A
    I-prompt : ∀{τ r β α h} →
      ⊢stop h β α r →
      ⊢ prompt ∷ Arr
        (Arr
          (Lift ⊤) τ
          (Lift h)
          (Lift (HV τ)))
        r β α
    I-control : ∀{h τ a f r α β α' β' δ} →
      ⊢propShift h β α r →
      ⊢ control ∷ Arr
        (Arr
          (Arr τ a β α)
          f β' α')
        τ
        (Lift (H (Arr
          (Arr r a α δ)
          f β' α')))
        (Lift h)

  open TypeJudge (⊢_∷_)

module Kiselyov3 where
  data Strat : Set where
    Stop PropShift : Strat

  data Hw : Set where
    H : Strat → Type → Type → Type → Hw

  data ⊢interp : Strat → Type → Type → Type → Type → Set where
    I-interpStop : ∀{strat a τ α β δ σ r} →
      ⊢interp Stop
        (Arr
          (Arr a a δ δ)
          τ
          (Lift (H Stop β α r))
          (Lift (H strat σ σ τ)))
        α α r
    I-interpPropShift : ∀{strat τ τ2 τ3 a f α β α' β' α'' β'' δ} →
      ⊢interp strat
        (Arr
          (Arr τ2 a δ α)
          f β' α')
        β'' α'' τ3 →
      ⊢interp PropShift
        (Arr
          (Arr τ a β α)
          f β' α')
        (Lift (H strat β'' α'' τ3))
        (Lift (H PropShift β δ τ2))
        τ

  data ⊢_∷_ : {A : Set} → A → Type → Set where
    I-lift : {A : Set} → (v : A) → ⊢ v ∷ Lift A
    I-prompt : ∀{strat τ r α β δ} →
      ⊢ prompt ∷ Arr
        (Arr
          (Lift ⊤) τ
          (Lift (H Stop β α r))
          (Lift (H strat δ δ τ)))
        r β α
    I-control : ∀{strat τ τ' a b f α β α' β' α'' β'' δ} →
      ⊢interp strat
        (Arr
          (Arr b a δ α)
          f β'' α'')
        β' α' τ' →
      ⊢ control ∷ Arr
        (Arr
          (Arr τ a β α)
          f β'' α'')
        τ
        (Lift (H strat β' α' τ'))
        (Lift (H PropShift β δ b))

  open TypeJudge (⊢_∷_)

module Kiselyov4 where
  data Strat : Set where
    Stop PropShift : Strat

  data H : Set where
    HStop : Type → H
    HPropShift : Type → Type → Type → H

  data ⊢hv : (Type → H) → Set where
    I-hvStop : ⊢hv HStop
    I-hvPropShift : ∀{δ} → ⊢hv (HPropShift δ δ)
  data ⊢h : H → Type → Set where
    I-hStop : ∀{h a r τ δ} →
      ⊢hv h →
      ⊢h (HStop r)
        (Arr
          (Arr a a δ δ)
          τ
          (Lift (HStop r))
          (Lift (h τ)))
    I-hPropShift : ∀{h a τ τ2 f α β α' β' δ} →
      ⊢h h (Arr (Arr τ2 a δ α) f β' α') →
      ⊢h
        (HPropShift
          (Lift h)
          (Lift (HPropShift β δ τ2))
          τ)
        (Arr
          (Arr τ a β α)
          f β' α')

  data ⊢_∷_ : {A : Set} → A → Type → Set where
    I-lift : {A : Set} → (v : A) → ⊢ v ∷ Lift A
    I-prompt : ∀{h τ r δ} →
      ⊢hv h →
      ⊢ prompt ∷ Arr
        (Arr
          (Lift ⊤) τ
          (Lift (HStop r))
          (Lift (h τ)))
        r δ δ
    I-control : ∀{h τ a b f α β α' β' δ} →
      ⊢h h (Arr (Arr b δ α a) f β' α') →
      ⊢ control ∷ Arr
        (Arr
          (Arr τ a β α)
          f β' α')
        τ
        (Lift h)
        (Lift (HPropShift β δ b))

  open TypeJudge (⊢_∷_)
