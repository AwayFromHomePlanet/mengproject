module Definitionsold where

-- open import Data.Bool using (Bool; true; false; T; not)
-- open import Data.Empty using (⊥; ⊥-elim)
-- open import Data.List using (List; _∷_; [])
-- open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
-- open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
-- open import Relation.Nullary.Decidable using (False; toWitnessFalse)
-- open import Relation.Nullary.Negation using (¬?)
-- open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

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

trans-rtc : {A : Set} {⇒ : A → A → Set} {M N P : A} 
  → rtc ⇒ M N 
  → rtc ⇒ N P 
  ----------------
  → rtc ⇒ M P
trans-rtc mn reflx = mn
trans-rtc mn (trans nq qp) = trans (trans-rtc mn nq) qp

lift-rtc : {A : Set} {⇒ : A → A → Set} {M N : A}
  → ⇒ M N
  ----------------
  → rtc ⇒ M N
lift-rtc mn = trans reflx mn

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

-- If a relation satisfies the diamond property, so does its reflexive transitive closure
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

infixr 5 ƛ_⇒_
infixr 5 μ_[_]_
infixl 7 _·_
infix 9 `_

data Term : Set

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
(` y)         [ N / x ]β with x ≟ y
...                         | yes _ = N
...                         | no  _ = ` y

(ƛ y ⇒ M)     [ N / x ]β with x ≟ y
...                         | yes _ = ƛ y ⇒ M
...                         | no  _ = ƛ y ⇒ M [ N / x ]β

(M · P)       [ N / x ]β            = M [ N / x ]β · P [ N / x ]β

(μ α [ β ] M) [ N / x ]β            = μ α [ β ] M [ N / x ]β

-- simple name substitution
_[_/_]ρ : Term → Name → Name → Term
(` x)         [ α / β ]ρ            = ` x

(ƛ x ⇒ M)     [ α / β ]ρ            = ƛ x ⇒ M [ α / β ]ρ

(M · N)       [ α / β ]ρ            =  M [ α / β ]ρ · N [ α / β ]ρ

(μ γ [ δ ] M) [ α / β ]ρ with β ≟ δ
...                         | yes _ = μ γ [ α ] M [ α / β ]ρ
...                         | no  _ = μ γ [ δ ] M [ α / β ]ρ

-- _[_/_]ᵨ : Name → Name → Name → Name
-- α [ β / γ ]ᵨ with α ≟ γ
-- ...             | yes _ = β
-- ...             | no  _ = α

-- right structural substitution
_[_∙_/_]r : Term → Term → Name → Name → Term
(` x)          [ N ∙ γ / α ]r            = ` x

(ƛ x ⇒ M)      [ N ∙ γ / α ]r            = ƛ x ⇒ M [ N ∙ γ / α ]r

(M · P)        [ N ∙ γ / α ]r            = M [ N ∙ γ / α ]r · P [ N ∙ γ / α ]r

(μ β [ δ ] M ) [ N ∙ γ / α ]r with α ≟ δ
...                              | yes _ = μ β [ γ ] M [ N ∙ γ / α ]r · N
...                              | no  _ = μ β [ δ ] M [ N ∙ γ / α ]r

-- left structural substitution
_[_∙_/_]l : Term → Term → Name → Name → Term
(` x)          [ N ∙ γ / α ]l            = ` x

(ƛ x ⇒ M)      [ N ∙ γ / α ]l            = ƛ x ⇒ M [ N ∙ γ / α ]l

(M · P)        [ N ∙ γ / α ]l            = M [ N ∙ γ / α ]l · P [ N ∙ γ / α ]l

(μ β [ δ ] M ) [ N ∙ γ / α ]l with α ≟ δ
...                              | yes _ = μ β [ γ ] N · M [ N ∙ γ / α ]l
...                              | no  _ = μ β [ δ ] M [ N ∙ γ / α ]l


-- lmuv single step reduction
infixr 4 _⟶_
data _⟶_ : Term → Term → Set where
  [β] : ∀ {x : Id} {M V : Term}
    → Value V
    ----------------
    → (ƛ x ⇒ M) · V ⟶ M [ V / x ]β
    
  [ρ] : ∀ {α β γ δ : Name} {M : Term}
    ----------------
    → μ α [ β ] μ γ [ δ ] M ⟶ (μ α [ δ ] M) [ β / γ ]ρ

  [μr] : ∀ {α β γ : Name} {M N : Term}
    ----------------
    → (μ α [ β ] M) · N ⟶ (μ γ [ β ] M) [ N ∙ γ / α ]r

  [μl] : ∀ {α β γ : Name} {M V : Term}
    → Value V
    ----------------
    → V · (μ α [ β ] M) ⟶ (μ γ [ β ] M) [ V ∙ γ / α ]l

  [c1] : ∀ {M M' N : Term}
    → M ⟶ M'
    ----------------
    → M · N ⟶ M' · N

  [c2] : ∀ {M N N' : Term}
    → N ⟶ N'
    ----------------
    → M · N ⟶ M · N'

  [c3] : ∀ {x : Id} {M M' : Term}
    → M ⟶ M'
    ----------------
    → ƛ x ⇒ M ⟶ ƛ x ⇒ M'

  [c4] : ∀ {α β : Name} {M M' : Term}
    → M ⟶ M'
    ----------------
    → μ α [ β ] M ⟶ μ α [ β ] M'

infixr 4 _⟶*_
_⟶*_ : Term → Term → Set
_⟶*_ = rtc _⟶_

cong1 : ∀ {M M' N : Term}
  → M ⟶* M'
  ----------------
  → M · N ⟶* M' · N
cong1 reflx = reflx
cong1 (trans mp pm') = trans (cong1 mp) ([c1] pm')
  
cong2 : ∀ {M N N' : Term}
  → N ⟶* N'
  ----------------
  → M · N ⟶* M · N'
cong2 reflx = reflx
cong2 (trans np pn') = trans (cong2 np) ([c2] pn')

cong3 : ∀ {x : Id} {M M' : Term}
  → M ⟶* M'
  ----------------
  → ƛ x ⇒ M ⟶* ƛ x ⇒ M'
cong3 reflx = reflx
cong3 (trans mn nm') = trans (cong3 mn) ([c3] nm')

cong4 : ∀ {α β : Name} {M M' : Term}
  → M ⟶* M'
  ----------------
  → μ α [ β ] M ⟶* μ α [ β ] M'
cong4 reflx = reflx
cong4 (trans mn nm') = trans (cong4 mn) ([c4] nm')

-- β* : ∀ {x : Id} {M V : Term}
--   → Value V
--   ----------------
--   → (ƛ x ⇒ M) · V ⟶* M [ V / x ]β
-- β* val

cong-app : ∀ {M M' N N' : Term}
  → M ⟶* M'
  → N ⟶* N'
  ----------------
  → M · N ⟶* M' · N'
cong-app mm' nn' = trans-rtc (cong1 mm') (cong2 nn')

-- LMUV PARALLEL REDUCTION
infixr 4 _==>_
data _==>_ : Term → Term → Set where
  [1] : ∀ {x : Id}
    ----------------
    → ` x ==> ` x

  [2] : ∀ {x : Id} {M M' : Term}
    → M ==> M'
    ----------------
    → ƛ x ⇒ M ==> ƛ x ⇒ M'

  [3] : ∀ {α β : Name} {M M' : Term}
    → M ==> M'
    ----------------
    → μ α [ β ] M ==> μ α [ β ] M'
    
  [4] : ∀ {M N M' N' : Term}
    → M ==> M'
    → N ==> N'
    ----------------
    → M · N ==> M' · N'

  [5] : ∀ {α β γ δ : Name} {M M' : Term}
    → M ==> μ γ [ δ ] M'
    ----------------
    → μ α [ β ] M ==> (μ α [ δ ] M') [ β / γ ]ρ

  [6] : ∀ {x : Id} {M M' N V : Term}
    → Value V
    → M ==> ƛ x ⇒ M'
    → N ==> V
    ----------------
    → M · N ==> M' [ V / x ]β

  [7] : ∀ {α β γ : Name} {M M' N N' : Term}
    → M ==> μ α [ β ] M'
    → N ==> N'
    ----------------
    → M · N ==> (μ γ [ β ] M') [ N' ∙ γ / α ]r

  [8] : ∀ {α β γ : Name} {M V N N' : Term}
    → Value V
    → M ==> V
    → N ==> μ α [ β ] N'
    ----------------
    → M · N ==> (μ γ [ β ] N') [ V ∙ γ / α ]l

infixr 4 _==>*_
_==>*_ : Term → Term → Set
_==>*_ = rtc _==>_

-- any term parallel reduces to itself
par-refl : ∀ {M : Term} → M ==> M
par-refl {` x}         = [1]
par-refl {ƛ x ⇒ M}     = [2] par-refl
par-refl {M · N}       = [4] par-refl par-refl
par-refl {μ α [ β ] M} = [3] par-refl

-- SINGLE STEP AND PARALLEL REDUCTION HAVE THE SAME REFLEXIVE TRANSITIVE CLOSURE
-- postulate ==>*=⟶* : ∀ {M N : Term} → M ==>* N ⇔ M ⟶* N

sin-par : ∀ {M N : Term} → M ⟶ N → M ==> N
sin-par ([β] val)  = [6] val par-refl par-refl
sin-par [ρ]        = [5] par-refl
sin-par [μr]       = [7] par-refl par-refl
sin-par ([μl] val) = [8] val par-refl par-refl
sin-par ([c1] mm') = [4] (sin-par mm') par-refl
sin-par ([c2] nn') = [4] par-refl (sin-par nn')
sin-par ([c3] mm') = [2] (sin-par mm')
sin-par ([c4] mm') = [3] (sin-par mm')

sins-pars : ∀ {M N : Term} → M ⟶* N → M ==>* N
sins-pars reflx         = reflx
sins-pars (trans mp pn) = trans (sins-pars mp) (sin-par pn)

par-sins : ∀ {M N : Term} → M ==> N → M ⟶* N
par-sins [1]             = reflx
par-sins ([2] mm')       = cong3 (par-sins mm')
par-sins ([3] mm')       = cong4 (par-sins mm')
par-sins ([4] mm' nn')   = cong-app (par-sins mm') (par-sins nn')
par-sins ([5] mμ)        = trans (cong4 (par-sins mμ)) [ρ]
par-sins ([6] val mλ nv) = trans (cong-app (par-sins mλ) (par-sins nv)) ([β] val)
par-sins ([7] mμ nn')    = trans (cong-app (par-sins mμ) (par-sins nn')) [μr]
par-sins ([8] val mv mμ) = trans (cong-app (par-sins mv) (par-sins mμ)) ([μl] val)

pars-sins : ∀ {M N : Term} → M ==>* N → M ⟶* N
pars-sins reflx         = reflx
pars-sins (trans mp pn) = trans-rtc (pars-sins mp) (par-sins pn)

