module LDefinitions where

open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat using (ℕ; zero; suc; _+_; _≟_; _⊓_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)

---------------- PROPERTIES ABOUT RELATIONS ----------------
-- Reflexive transitive closure
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

-- Diamond and Church-Rosser properties
diamond : ∀ {A : Set} → (_⇒_ : A → A → Set) → Set
diamond {A} _⇒_ = ∀ {t u v : A}
    → t ⇒ u
    → t ⇒ v
      --------------
    → ∃[ w ](u ⇒ w × v ⇒ w)

confluent : ∀ {A : Set} → (_⇒_ : A → A → Set) → Set
confluent ⇒ = diamond (rtc ⇒)

-- If t => u and t =>* v, then there exists w such that u =>* w and v => w
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


---------------- LAMBDA MU WITH NEGATION SYNTAX ----------------
Id : Set
Id = ℕ
Name : Set
Name = ℕ

infixr 5 ƛ_⇒_
infixr 5 μ_⇒_
infixr 5 ν_⇒_
infix 5 [_]_
infixl 7 _·_
infix 7 ⁅_⁆_
infix 9 `_

data Term : Set where
  `_   : Id   → Term
  ƛ_⇒_ : Id   → Term → Term
  _·_  : Term → Term → Term
  ν_⇒_ : Id   → Term → Term
  ⁅_⁆_ : Term → Term → Term 
  μ_⇒_ : Name → Term → Term
  [_]_ : Name → Term → Term

data Value : Term → Set where
  Vx : ∀ {x : Id}            → Value (` x)
  Vƛ : ∀ {x : Id} {M : Term} → Value (ƛ x ⇒ M)


---------------- FRESH NAMES ----------------
-- α ∉ M means α does not occur (free or bound) in M
infix 4 _∉_
_∉_ : Name → Term → Set
α ∉ (` x)                = ⊤
α ∉ (ƛ x ⇒ M)            = α ∉ M
α ∉ (M · N)              = α ∉ M × α ∉ N
α ∉ (ν x ⇒ M)            = α ∉ M
α ∉ (⁅ M ⁆ N)            = α ∉ M × α ∉ N
α ∉ (μ β ⇒ M) with α ≟ β
...              | yes _ = ⊥
...              | no  _ = α ∉ M
α ∉ ([ β ] M) with α ≟ β
...              | yes _ = ⊥
...              | no  _ = α ∉ M

max : Term → Name
max (` x)     = zero
max (ƛ x ⇒ M) = max M
max (M · N)   = max M ⊓ max N
max (ν x ⇒ M) = max M
max (⁅ M ⁆ N) = max M ⊓ max N
max (μ α ⇒ M) = α ⊓ max M
max ([ α ] M) = α ⊓ max M

postulate fresh-max : ∀ (M : Term) → suc (max  M) ∉  M
-- fresh-max' : ∀ (C : Command) → suc (max' C) ∉' C
-- fresh-max  (` x) = tt
-- fresh-max  (ƛ x ⇒ M) = fresh-max M
-- fresh-max  (μ α ⇒ C) with suc (α ⊓ max' C) ≟ α
-- ... | yes _ = {!   !}
-- ... | no  _ = {!   !}
-- fresh-max  (M · N) = ⟨ {!   !} , {!   !} ⟩
-- fresh-max' ([ α ] M) = {!   !}

fresh : ∀ (M : Term) → ∃[ α ] α ∉ M
fresh M = ⟨ suc (max M) , fresh-max M ⟩

---------------- LAMBDA MU TERM SUBSTITUTION ----------------
-- Simple term substitution
_[_/_]β : Term → Term → Id → Term
(` y)     [ N / x ]β with x ≟ y
...                     | yes _ = N
...                     | no  _ = ` y
(ƛ y ⇒ M) [ N / x ]β with x ≟ y
...                     | yes _ = ƛ y ⇒ M
...                     | no  _ = ƛ y ⇒ M [ N / x ]β
(M · P)   [ N / x ]β            = M [ N / x ]β · P [ N / x ]β
(ν y ⇒ M) [ N / x ]β with x ≟ y
...                     | yes _ = ν y ⇒ M
...                     | no  _ = ν y ⇒ M [ N / x ]β
(⁅ M ⁆ P) [ N / x ]β            = ⁅ M [ N / x ]β ⁆ P [ N / x ]β
(μ α ⇒ M) [ N / x ]β            = μ α ⇒ M [ N / x ]β
([ α ] M) [ N / x ]β            = [ α ] M [ N / x ]β

-- Simple name substitution
_[_/_]ρ : Term → Name → Name → Term
(` x)     [ α / β ]ρ             = ` x
(ƛ x ⇒ M) [ α / β ]ρ             = ƛ x ⇒ M [ α / β ]ρ
(M · N)   [ α / β ]ρ             = M [ α / β ]ρ · N [ α / β ]ρ
(ν x ⇒ M) [ α / β ]ρ             = ν x ⇒ M [ α / β ]ρ
(⁅ M ⁆ N) [ α / β ]ρ             = ⁅ M [ α / β ]ρ ⁆ N [ α / β ]ρ
(μ γ ⇒ M) [ α / β ]ρ             = μ γ ⇒ M [ α / β ]ρ
([ γ ] M) [ α / β ]ρ with β ≟ γ
...                      | yes _ = [ α ] M [ α / β ]ρ
...                      | no  _ = [ γ ] M [ α / β ]ρ

-- Right structural substitution
_[_∙_/_]r : Term → Term → Name → Name → Term
(` x)     [ N ∙ γ / α ]r             = ` x
(ƛ x ⇒ M) [ N ∙ γ / α ]r             = ƛ x ⇒ M [ N ∙ γ / α ]r
(M · P)   [ N ∙ γ / α ]r             = M [ N ∙ γ / α ]r · P [ N ∙ γ / α ]r
(ν x ⇒ M) [ N ∙ γ / α ]r             = ν x ⇒ M [ N ∙ γ / α ]r
(⁅ M ⁆ P) [ N ∙ γ / α ]r             = ⁅ M [ N ∙ γ / α ]r ⁆ P [ N ∙ γ / α ]r
(μ β ⇒ C) [ N ∙ γ / α ]r             = μ β ⇒ C [ N ∙ γ / α ]r
([ β ] M) [ N ∙ γ / α ]r with α ≟ β
...                          | yes _ = [ γ ] M [ N ∙ γ / α ]r · N
...                          | no  _ = [ β ] M [ N ∙ γ / α ]r

-- Left structural substitution
_[_∙_/_]l : Term → Term → Name → Name → Term
(` x)     [ N ∙ γ / α ]l             = ` x
(ƛ x ⇒ M) [ N ∙ γ / α ]l             = ƛ x ⇒ M [ N ∙ γ / α ]l
(M · P)   [ N ∙ γ / α ]l             = M [ N ∙ γ / α ]l · P [ N ∙ γ / α ]l
(ν x ⇒ M) [ N ∙ γ / α ]l             = ν x ⇒ M [ N ∙ γ / α ]l
(⁅ M ⁆ P) [ N ∙ γ / α ]l             = ⁅ M [ N ∙ γ / α ]l ⁆ P [ N ∙ γ / α ]l
(μ β ⇒ C) [ N ∙ γ / α ]l             = μ β ⇒ C [ N ∙ γ / α ]l
([ β ] M) [ N ∙ γ / α ]l with α ≟ β
...                          | yes _ = [ γ ] N · M [ N ∙ γ / α ]l
...                          | no  _ = [ β ] M [ N ∙ γ / α ]l

-- Insertion
_[_/_]δ : Term → Term → Name → Term
(` x) [ N / α ]δ                = ` x
(ƛ x ⇒ M) [ N / α ]δ            = ƛ x ⇒ M [ N / α ]δ
(M · P) [ N / α ]δ              = M [ N / α ]δ · P [ N / α ]δ
(ν x ⇒ M) [ N / α ]δ            = ν x ⇒ M [ N / α ]δ
(⁅ M ⁆ P) [ N / α ]δ            = ⁅ M [ N / α ]δ ⁆ P [ N / α ]δ
(μ β ⇒ M) [ N / α ]δ with α ≟ β
...                     | yes _ = μ β ⇒ M
...                     | no  _ = μ β ⇒ M [ N / α ]δ
([ β ] M) [ N / α ]δ with α ≟ β
...                     | yes _ = ⁅ M ⁆ N
...                     | no  _ = [ β ] M [ N / α ]δ

---------------- LMUV SINGLE STEP REDUCTION ----------------

infixl 7 _·l_
infixl 7 _·r_
infix 7 ⁅_⁆l_
infix 7 ⁅_⁆r_

data Ctxt : Set where
  ∙     : Ctxt
  ƛ_⇒_  : Id   → Ctxt → Ctxt
  _·l_  : Ctxt → Term → Ctxt
  _·r_  : Term → Ctxt → Ctxt
  ν_⇒_  : Id   → Ctxt → Ctxt
  ⁅_⁆l_ : Ctxt → Term → Ctxt
  ⁅_⁆r_ : Term → Ctxt → Ctxt
  μ_⇒_  : Name → Ctxt → Ctxt
  [_]_  : Name → Ctxt → Ctxt

_⌜_⌟ : Ctxt → Term → Term
∙          ⌜ M ⌟ = M
(ƛ x ⇒ C)  ⌜ M ⌟ = ƛ x ⇒ C ⌜ M ⌟
(C ·l N)   ⌜ M ⌟ = C ⌜ M ⌟ · N
(N ·r C)   ⌜ M ⌟ = N · C ⌜ M ⌟
(ν x ⇒ C)  ⌜ M ⌟ = ν x ⇒ C ⌜ M ⌟
(⁅ C ⁆l N) ⌜ M ⌟ = ⁅ C ⌜ M ⌟ ⁆ N
(⁅ N ⁆r C) ⌜ M ⌟ = ⁅ N ⁆ C ⌜ M ⌟
(μ α ⇒ C)  ⌜ M ⌟ = μ α ⇒ C ⌜ M ⌟
([ α ] C)  ⌜ M ⌟ = [ α ] C ⌜ M ⌟

infixr 4 _⟶_
data _⟶_  : Term    → Term    → Set

data _⟶_ where
  [β] : ∀ {x : Id} {M V : Term}
    → Value V
    ----------------
    → (ƛ x ⇒ M) · V ⟶ M [ V / x ]β

  [ν] : ∀ {x : Id} {M N : Term}
    ----------------
    → ⁅ ν x ⇒ M ⁆ N ⟶ M [ N / x ]β

  [μr] : ∀ {α γ : Name} {M N : Term}
    → γ ∉ ((μ α ⇒ M) · N)
    ----------------
    → (μ α ⇒ M) · N ⟶ μ γ ⇒ M [ N ∙ γ / α ]r

  [μl] : ∀ {α γ : Name} {M V : Term}
    → γ ∉ (V · (μ α ⇒ M))
    → Value V
    ----------------
    → V · (μ α ⇒ M) ⟶ μ γ ⇒ M [ V ∙ γ / α ]l

  [δ] : ∀ {α : Name} {M N : Term}
    ----------------
    → ⁅ μ α ⇒ M ⁆ N ⟶ M [ N / α ]δ

  [ρ] : ∀ {α β : Name} {M : Term}
    ----------------
    → [ α ] μ β ⇒ M ⟶ M [ α / β ]ρ
  
  [ctxt] : ∀ {M M' : Term} {C : Ctxt}
    → M ⟶ M'
    ----------------
    → C ⌜ M ⌟ ⟶ C ⌜ M' ⌟


-- Reflexive transitive closure of lmuv single step reduction
infixr 4 _⟶*_
_⟶*_  : Term    → Term    → Set
_⟶*_  = rtc _⟶_

ctxt* : ∀ {M M' : Term} (C : Ctxt)
  → M ⟶* M'
  ----------------
  → C ⌜ M ⌟ ⟶* C ⌜ M' ⌟
ctxt* _ reflx = reflx
ctxt* c (trans mn np) = trans (ctxt* c mn) ([ctxt] np)

app* : ∀ {M M' N N' : Term}
  → M ⟶* M'
  → N ⟶* N'
  ----------------
  → M · N ⟶* M' · N'
app* {M} {M'} {N} {N'} mm' nn' = trans-rtc (ctxt* (∙ ·l N) mm') (ctxt* (M' ·r ∙) nn')

neg* : ∀ {M M' N N' : Term}
  → M ⟶* M'
  → N ⟶* N'
  ----------------
  → ⁅ M ⁆ N ⟶* ⁅ M' ⁆ N'
neg* {M} {M'} {N} {N'} mm' nn' = trans-rtc (ctxt* (⁅ ∙ ⁆l N) mm') (ctxt* (⁅ M' ⁆r ∙) nn')

---------------- LMUV PARALLEL REDUCTION ----------------
infixr 4 _==>_
data _==>_  : Term    → Term    → Set
  
data _==>_ where
  [1] : ∀ {x : Id}
    ----------------
    → ` x ==> ` x

  [2] : ∀ {x : Id} {M M' : Term}
    → M ==> M'
    ----------------
    → ƛ x ⇒ M ==> ƛ x ⇒ M'

  [3] : ∀ {x : Id} {M M' : Term}
    → M ==> M'
    ----------------
    → ν x ⇒ M ==> ν x ⇒ M'

  [4] : ∀ {α : Name} {M M' : Term}
    → M ==> M'
    ----------------
    → μ α ⇒ M ==> μ α ⇒ M'
    
  [5] : ∀ {M N M' N' : Term}
    → M ==> M'
    → N ==> N'
    ----------------
    → M · N ==> M' · N'

  [6] : ∀ {M N M' N' : Term}
    → M ==> M'
    → N ==> N'
    ----------------
    → ⁅ M ⁆ N ==> ⁅ M' ⁆ N'

  [7] : ∀ {α : Name} {M M' : Term}
    → M ==> M'
    ----------------
    → [ α ] M ==> [ α ] M'

  [8] : ∀ {α β : Name} {M M' : Term}
    → M ==> μ β ⇒ M'
    ----------------
    → [ α ] M ==> M' [ α / β ]ρ

  [9] : ∀ {x : Id} {M M' N V : Term}
    → Value V
    → M ==> ƛ x ⇒ M'
    → N ==> V
    ----------------
    → M · N ==> M' [ V / x ]β

  [10] : ∀ {x : Id} {M M' N N' : Term}
    → M ==> ν x ⇒ M'
    → N ==> N'
    ----------------
    → ⁅ M ⁆ N ==> M' [ N' / x ]β

  [11] : ∀ {α γ : Name} {M M' N N' : Term}
    → γ ∉ ((μ α ⇒ M') · N')
    → M ==> μ α ⇒ M'
    → N ==> N'
    ----------------
    → M · N ==> μ γ ⇒ M' [ N' ∙ γ / α ]r

  [12] : ∀ {α γ : Name} {M V N N' : Term}
    → γ ∉ (V · (μ α ⇒ N'))
    → Value V
    → M ==> V
    → N ==> μ α ⇒ N'
    ----------------
    → M · N ==> μ γ ⇒ N' [ V ∙ γ / α ]l

  [13] : ∀ {α : Name} {M M' N N' : Term}
    → M ==> μ α ⇒ M'
    → N ==> N'
    ----------------
    → ⁅ M ⁆ N ==> M' [ N' / α ]δ


-- Reflexive transitive closure of lmuv parallel reduction
infixr 4 _==>*_
_==>*_  : Term    → Term    → Set
_==>*_  = rtc _==>_

-- any term parallel reduces to itself
par-refl  : ∀ {M : Term}    → M ==> M
par-refl {` x}      = [1]
par-refl {ƛ x ⇒ M}  = [2] par-refl
par-refl {M · N}    = [5] par-refl par-refl
par-refl {ν x ⇒ M}  = [3] par-refl
par-refl {⁅ M ⁆ N}  = [6] par-refl par-refl
par-refl {μ α ⇒ M}  = [4] par-refl
par-refl {[ α ] M}  = [7] par-refl


---------------- ⟶* = ==>* ----------------
-- Forward direction
sin-par : ∀ {M N : Term} → M ⟶ N → M ==> N
sin-par ([β] val)                  = [9] val par-refl par-refl
sin-par [ν]                        = [10] par-refl par-refl
sin-par ([μr] new)                 = [11] new par-refl par-refl
sin-par ([μl] new val)             = [12] new val par-refl par-refl
sin-par [δ]                        = [13] par-refl par-refl
sin-par [ρ]                        = [8] par-refl
sin-par ([ctxt] {C = ∙} mn)        = sin-par mn
sin-par ([ctxt] {C = ƛ x ⇒ C} mn)  = [2] (sin-par ([ctxt] mn))
sin-par ([ctxt] {C = C ·l P} mn)   = [5] (sin-par ([ctxt] mn)) par-refl
sin-par ([ctxt] {C = P ·r C} mn)   = [5] par-refl (sin-par ([ctxt] mn))
sin-par ([ctxt] {C = ν x ⇒ C} mn)  = [3] (sin-par ([ctxt] mn))
sin-par ([ctxt] {C = ⁅ C ⁆l P} mn) = [6] (sin-par ([ctxt] mn)) par-refl
sin-par ([ctxt] {C = ⁅ P ⁆r C} mn) = [6] par-refl (sin-par ([ctxt] mn))
sin-par ([ctxt] {C = μ α ⇒ C} mn)  = [4] (sin-par ([ctxt] mn))
sin-par ([ctxt] {C = [ α ] C} mn)  = [7] (sin-par ([ctxt] mn))

sins-pars : ∀ {M N : Term} → M ⟶* N → M ==>* N
sins-pars reflx         = reflx
sins-pars (trans mp pn) = trans (sins-pars mp) (sin-par pn)

-- Backward direction
par-sins : ∀ {M N : Term} → M ==> N → M ⟶* N
par-sins [1]                  = reflx
par-sins ([2] {x} mm')        = ctxt* (ƛ x ⇒ ∙) (par-sins mm')
par-sins ([3] {x} mm')        = ctxt* (ν x ⇒ ∙) (par-sins mm')
par-sins ([4] {α} mm')        = ctxt* (μ α ⇒ ∙) (par-sins mm')
par-sins ([5] mm' nn')        = app* (par-sins mm') (par-sins nn')
par-sins ([6] mm' nn')        = neg* (par-sins mm') (par-sins nn')
par-sins ([7] {α} mm')        = ctxt* ([ α ] ∙) (par-sins mm')
par-sins ([8] {α} mμ)         = trans (ctxt* ([ α ] ∙) (par-sins mμ)) [ρ]
par-sins ([9] val mλ nv)      = trans (app* (par-sins mλ) (par-sins nv)) ([β] val)
par-sins ([10] mλ nv)         = trans (neg* (par-sins mλ) (par-sins nv)) [ν]
par-sins ([11] new mμ nn')    = trans (app* (par-sins mμ) (par-sins nn')) ([μr] new)
par-sins ([12] new val mv nμ) = trans (app* (par-sins mv) (par-sins nμ)) ([μl] new val)
par-sins ([13] mμ nn')        = trans (neg* (par-sins mμ) (par-sins nn')) [δ]

pars-sins : ∀ {M N : Term} → M ==>* N → M ⟶* N
pars-sins reflx         = reflx
pars-sins (trans mp pn) = trans-rtc (pars-sins mp) (par-sins pn)

-- Both reductions are equal by extensionality
postulate
  extensionality : ∀ {A : Set} {_R_ _S_ : A → A → Set}
    → (∀ (x y : A) → ((x R y → x S y) × (x S y → x R y)))
      -----------------------
    → _R_ ≡ _S_  

same-rtc : _⟶*_ ≡ _==>*_
same-rtc = extensionality (λ M N → ⟨ (λ M⟶*N → sins-pars M⟶*N) , (λ M==>*N → pars-sins M==>*N) ⟩)