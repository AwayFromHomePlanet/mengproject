module StrongNorm where

open import Definitions
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_; length; reverse; map; foldr; downFrom)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data SN (M : Term) : Set where
  sn : (∀ {M' : Term} → M ⟶ M' → SN M')
    ----------------
    → SN M

infixl 6 _∙'_
_∙'_ : Term → List Term → Term
M ∙' []       = M
M ∙' (N ∷ Ns) = (M · N) ∙' Ns

-- _+:_ : ∀ {A : Set} → List A → 
lem1 : ∀ {M N : Term} {Ns : List Term} → M ∙' (Ns ∷ʳ N) ≡ (M ∙' Ns) · N
lem1 {Ns = []} = refl
lem1 {Ns = (x ∷ xs)} = {!   !}

postulate
  prop1 : ∀ {Ms : List Term} (x : Id) → (SNs : All SN Ms) → SN (` x ∙' Ms)
  prop2 : ∀ (x : Id) (M : Term) → SN (M · ` x) → SN M

  propla : ∀ {M : Term} (x : Id) → SN M → SN (ƛ x ⇒ M)
  propnu : ∀ {M : Term} (x : Id) → SN M → SN (ν x ⇒ M)
  propmu : ∀ {M : Term} (α : Name) → SN M → SN (μ α ⇒ M)

  propβ : ∀ {x : Id} {M N : Term} {Ps : List Term}
    → SN (M [ N / x ]β ∙' Ps)
    → SN N
    ----------------
    → SN ((ƛ x ⇒ M) · N ∙' Ps)

  propν : ∀ {x : Id} {M N : Term} {Ps : List Term}
    → SN (M [ N / x ]β ∙' Ps)
    → SN N
    ----------------
    → SN (⁅ ν x ⇒ M ⁆ N ∙' Ps)

  propμ : ∀ {α γ : Name} {M N : Term} {Ps : List Term}
    → SN (M [ N ∙ γ / α ]r ∙' Ps)
    → SN N
    ----------------
    → SN ((μ α ⇒ M) · N ∙' Ps)

  propδ : ∀ {α : Name} {M N : Term} {Ps : List Term}
    → SN (M [ N / α ]δ ∙' Ps)
    → SN N
    ---------------- 
    → SN (⁅ μ α ⇒ M ⁆ N ∙' Ps)


data Type : Set where
  φ   : Type
  _⇒_ : Type → Type → Type

Red : Term → Type → Set
Red M φ       = SN M
Red M (A ⇒ B) = ∀ (N : Term) → Red N A → Red (M · N) B

red-sn : ∀ (M : Term) (A : Type) → Red M A → SN M
red-var' : ∀ (x : Id) (Ns : List Term) (A : Type) → All SN Ns → Red (` x ∙' Ns) A

red-var : ∀ (x : Id) (A : Type) → Red (` x) A
red-var x A = red-var' x [] A All.[]


red-sn _ φ       sn' = sn'
red-sn M (A ⇒ B) sn' = prop2 1 M (red-sn (M · ` 1) B (sn' (` 1) (red-var 1 A)))

red-var' x Ns φ       SNs = prop1 x SNs
red-var' x Ns (A ⇒ B) SNs = λ N redna → {! red-var' x (Ns ∷ʳ N) B ?  !}

RedF : Term → Type → Type → Set
RedF M A B = ∀ (Ns : List Term) → All (λ n → Red n A) Ns → Red (M ∙' Ns) B

-- lem66 : 