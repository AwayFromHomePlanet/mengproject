module Confluence where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- STUFF ABOUT RELATIONS

diamond : ∀ {A : Set} → (_⇒_ : A → A → Set) → Set
diamond {A} _⇒_ = ∀ {t u v : A}
    → t ⇒ u
    → t ⇒ v
      --------------
    → ∃[ w ](u ⇒ w × v ⇒ w)

-- reflexive, transitive closure
data rtc {A : Set} (⇒ : A → A → Set) : A → A → Set where

  reflx : ∀ {M : A}
    --------
    → rtc ⇒ M M
    
  trans : ∀ {M N P : A}
    → rtc ⇒ M N
    → ⇒ N P
    --------
    → rtc ⇒ M P

-- If t => u and t ===> v, then there exists w such that u ===> w and v => w
parallelogram-lemma : ∀ {A : Set} (⇒ : A → A → Set) → diamond ⇒
  → ∀ {t u v : A}
  → ⇒ t u
  → rtc ⇒ t v
  ------------
  → ∃[ w ](rtc ⇒ u w × ⇒ v w)

parallelogram-lemma ⇒ dia {u = u} tu reflx = ⟨ u , ⟨ reflx , tu ⟩ ⟩
parallelogram-lemma ⇒ dia tu (trans tx xv)
  with parallelogram-lemma ⇒ dia tu tx
...  | ⟨ y , ⟨ uy , xy ⟩ ⟩
    with dia xy xv
...    | ⟨ w , ⟨ yw , vw ⟩ ⟩ = ⟨ w , ⟨ (trans uy yw) , vw ⟩ ⟩

-- if a relation satisfies the diamond property, so does its reflexive transitive closure
rtc-diamond : ∀ {A : Set} (⇒ : A → A → Set) → diamond ⇒ → diamond (rtc ⇒)

rtc-diamond ⇒ dia {v = v} reflx tv = ⟨ v , ⟨ tv , reflx ⟩ ⟩
rtc-diamond ⇒ dia {u = u} tu reflx = ⟨ u , ⟨ reflx , tu ⟩ ⟩
rtc-diamond ⇒ dia tu (trans tx xv)
  with rtc-diamond ⇒ dia tu tx
...  | ⟨ y , ⟨ uy , xy ⟩ ⟩
    with parallelogram-lemma ⇒ dia xv xy
...    | ⟨ w , ⟨ vw , yw ⟩ ⟩ = ⟨ w , ⟨ (trans uy yw) , vw ⟩ ⟩


-- LAMBDA MU SYNTAX
Id : Set
Id = String
Name : Set
Name = String

infix 5 ƛ_⇒_
--infix 5 μ_⇒_
--infix 6 [_]_
infix 5 μ_[_]_
infixl 7 _·_
infix 9 `_

data Term : Set
--data Command : Set

data Term where
  `_   : Id → Term
  ƛ_⇒_ : Id → Term → Term
  _·_  : Term → Term → Term
  μ_[_]_ : Name → Name → Term → Term

{-data Command where
  [_]_ : Name → Term → Command-}

myterm : Term
myterm = ƛ "x" ⇒ μ "a" [ "a" ] ` "x" · ` "y"

-- LAMBDA MU CBV REDUCTION
-- data Value : Set where
--   var : ∀ {x : Id} → ` x → Value

-- define Value as a predicate on terms, or as a datatype itself? here it's a predicate:
data Value : Term → Set where
  Vx : ∀ {x : Id}            → Value (` x)
  Vƛ : ∀ {x : Id} {M : Term} → Value (ƛ x ⇒ M)

-- simple term substitution
_[_/_]β : Term → Term → Id → Term
(` y) [ N / x ]β with x ≟ y
...                | yes _ = N
...                | no  _ = ` y

(ƛ y ⇒ M) [ N / x ]β with x ≟ y
...                 | yes _ = ƛ y ⇒ M
...                 | no  _ = ƛ y ⇒ M [ N / x ]β

(M · P) [ N / x ]β = M [ N / x ]β · P [ N / x ]β

(μ α [ β ] M) [ N / x ]β = μ α [ β ] M [ N / x ]β

-- simple name substitution
_[_/_]ρ : Term → Name → Name → Term
(` x) [ α / β ]ρ = ` x

(ƛ x ⇒ M) [ α / β ]ρ = ƛ x ⇒ M [ α / β ]ρ

(M · N) [ α / β ]ρ =  M [ α / β ]ρ · N [ α / β ]ρ

(μ γ [ δ ] M) [ α / β ]ρ with β ≟ δ
...                           | yes _ = μ γ [ α ] M [ α / β ]ρ
...                           | no  _ = μ γ [ δ ] M [ α / β ]ρ

_[_/_]ᵨ : Name → Name → Name → Name
α [ β / γ ]ᵨ with α ≟ γ
...             | yes _ = β
...             | no  _ = α

-- right structural substitution
_[_∙_/_]r : Term → Term → Name → Name → Term
(` x) [ N ∙ γ / α ]r = ` x

(ƛ x ⇒ M) [ N ∙ γ / α ]r = ƛ x ⇒ M [ N ∙ γ / α ]r

(M · P) [ N ∙ γ / α ]r = M [ N ∙ γ / α ]r · P [ N ∙ γ / α ]r

(μ β [ δ ] M ) [ N ∙ γ / α ]r with α ≟ δ
...                               | yes _ = μ β [ γ ] M [ N ∙ γ / α ]r · N
...                               | no  _ = μ β [ δ ] M [ N ∙ γ / α ]r

-- left structural substitution
_[_∙_/_]l : Term → Term → Name → Name → Term
(` x) [ N ∙ γ / α ]l = ` x

(ƛ x ⇒ M) [ N ∙ γ / α ]l = ƛ x ⇒ M [ N ∙ γ / α ]l

(M · P) [ N ∙ γ / α ]l = M [ N ∙ γ / α ]l · P [ N ∙ γ / α ]l

(μ β [ δ ] M ) [ N ∙ γ / α ]l with α ≟ δ
...                               | yes _ = μ β [ γ ] N · M [ N ∙ γ / α ]l
...                               | no  _ = μ β [ δ ] M [ N ∙ γ / α ]l
{-_[_∙_/_]l : Command → Term → Name → Name → Command
[ β ] M [ N ∙ γ / α ]l with α ≟ β
...                       | yes _ = [ γ ] N · M [ N ∙ γ / α ]l
...                       | no  _ = [ β ] M [ N ∙ γ / α ]l-}

-- lmuv single step reduction
infixr 4 _⟶_
data _⟶_ : Term → Term → Set where
  β : ∀ {x : Id} {M V : Term}
    → Value V
    --------
    → (ƛ x ⇒ M) · V ⟶ M [ V / x ]β
    
  ρ : ∀ {α β γ δ : Name} {M : Term}
    --------
    → μ α [ β ] μ γ [ δ ] M ⟶ μ α [ δ [ β / γ ]ᵨ ] M [ β / γ ]ρ

  μr : ∀ {α β γ : Name} {M N : Term}
    --------
    → (μ α [ β ] M) · N ⟶ (μ γ [ β ] M) [ N ∙ γ / α ]r

  μl : ∀ {α β γ : Name} {M V : Term}
    → Value V
    --------
    → V · (μ α [ β ] M) ⟶ (μ γ [ β ] M) [ V ∙ γ / α ]l

_⟶*_ : Term → Term → Set
_⟶*_ = rtc _⟶_

    
