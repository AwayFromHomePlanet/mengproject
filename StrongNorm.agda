module StrongNorm where

open import LDefinitions
open import Data.List using (List; []; _∷_; _++_; length; reverse; map; foldr; downFrom)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)

data SN (M : Term) : Set where
  sn : (∀ {M' : Term} → M ⟶ M' → SN M')
    ----------------
    → SN M

infixl 6 _∙'_
_∙'_ : Term → List Term → Term
M ∙' []       = M
M ∙' (N ∷ Ns) = (M · N) ∙' Ns

postulate
  prop1 : ∀ {Ms : List Term} (x : Id) → (SNs : All SN Ms) → SN (` x ∙' Ms)

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
Red M (A ⇒ B) = ∀ {N : Term} → Red N A → Red (M · N) B
