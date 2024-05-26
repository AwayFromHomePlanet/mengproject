module Definitions where

open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)

---------------- PROPERTIES ABOUT RELATIONS ----------------
diamond : ∀ {A : Set} → (_⇒_ : A → A → Set) → (_=α_ : A → A → Set) → Set
diamond {A} _⇒_ _=α_ = ∀ {t u v : A}
    → t ⇒ u
    → t ⇒ v
      --------------
    → ∃[ w ] ∃[ x ](w =α x  ×  u ⇒ w  ×  v ⇒ x)

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

-- If t => u and t ===> v, then there exists w such that u ===> w and v => w
{-parallelogram-lemma : ∀ {A : Set} (⇒ : A → A → Set) → diamond ⇒
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
...    | ⟨ w , ⟨ vw , yw ⟩ ⟩ = ⟨ w , ⟨ (trans uy yw) , vw ⟩ ⟩-}


---------------- LAMBDA MU SYNTAX ----------------
Id : Set
Id = String
Name : Set
Name = String

infixr 5 ƛ_⇒_
infixr 5 μ_⇒_
infix 5 [_]_
infixl 7 _·_
infix 9 `_

data Term : Set
data Command : Set

data Term where
  `_   : Id → Term
  ƛ_⇒_ : Id → Term → Term
  μ_⇒_ : Name → Command → Term
  _·_  : Term → Term → Term

data Command where
  [_]_ : Name → Term → Command

myterm : Term
myterm = ƛ "x" ⇒ μ "a" ⇒ [ "a" ] ` "x" · ` "y"

data Value : Term → Set where
  Vx : ∀ {x : Id}            → Value (` x)
  Vƛ : ∀ {x : Id} {M : Term} → Value (ƛ x ⇒ M)

_∈ᵥ_  : Id → Term    → Bool
_∈ᵥ'_ : Id → Command → Bool

x ∈ᵥ  (` y) with x ≟ y
...           | yes _     = true
...           | no  _     = false

x ∈ᵥ  (ƛ y ⇒ M) with x ≟ y
...               | yes _ = false
...               | no  _ = x ∈ᵥ M

x ∈ᵥ  (M · N)              = x ∈ᵥ M ∧ x ∈ᵥ N

x ∈ᵥ  (μ α ⇒ C)            = x ∈ᵥ' C

x ∈ᵥ' ([ α ] M)            = x ∈ᵥ M

_∈ₙ_  : Name → Term    → Bool
_∈ₙ'_ : Name → Command → Bool

α ∈ₙ  (` x) = false

α ∈ₙ  (ƛ x ⇒ M) = α ∈ₙ M

α ∈ₙ  (M · N)              = α ∈ₙ M ∧ α ∈ₙ N

α ∈ₙ  (μ β ⇒ C) with α ≟ β
... | yes _ = false       
... | no _ = α ∈ₙ' C

α ∈ₙ' ([ β ] M)  with α ≟ β
... | yes _ = true      
... | no _ = α ∈ₙ M

_∉ᵥ_  : Id → Term    → Set
_∉ᵥ'_ : Id → Command → Set
_∉ₙ_  : Name → Term    → Set
_∉ₙ'_ : Name → Command → Set
_ ∉ᵥ _ = T (not (_ ∈ᵥ _))
_ ∉ᵥ' _ = T (not (_ ∈ᵥ' _))
_ ∉ₙ _ = T (not (_ ∈ₙ _))
_ ∉ₙ' _ = T (not (_ ∈ₙ' _))


---------------- LAMBDA MU TERM SUBSTITUTION ----------------
-- Simple term substitution
_[_/_]β  : Term    → Term → Id → Term
_[_/_]β' : Command → Term → Id → Command

(` y)     [ N / x ]β with x ≟ y
...                     | yes _ = N
...                     | no  _ = ` y

(ƛ y ⇒ M) [ N / x ]β with x ≟ y
...                     | yes _ = ƛ y ⇒ M
...                     | no  _ = ƛ y ⇒ M [ N / x ]β

(M · P)   [ N / x ]β            = M [ N / x ]β · P [ N / x ]β

(μ α ⇒ C) [ N / x ]β            = μ α ⇒ C [ N / x ]β'

([ α ] M) [ N / x ]β'           = [ α ] M [ N / x ]β

-- Simple name substitution
_[_/_]ρ  : Term    → Name → Name → Term
_[_/_]ρ' : Command → Name → Name → Command

(` x)     [ α / β ]ρ             = ` x

(ƛ x ⇒ M) [ α / β ]ρ             = ƛ x ⇒ M [ α / β ]ρ

(M · N)   [ α / β ]ρ             =  M [ α / β ]ρ · N [ α / β ]ρ

(μ γ ⇒ C) [ α / β ]ρ             = μ γ ⇒ C [ α / β ]ρ'

([ γ ] M) [ α / β ]ρ' with β ≟ γ
...                      | yes _ = [ α ] M [ α / β ]ρ
...                      | no  _ = [ γ ] M [ α / β ]ρ

-- Right structural substitution
_[_∙_/_]r  : Term    → Term → Name → Name → Term
_[_∙_/_]r' : Command → Term → Name → Name → Command
(` x)     [ N ∙ γ / α ]r             = ` x

(ƛ x ⇒ M) [ N ∙ γ / α ]r             = ƛ x ⇒ M [ N ∙ γ / α ]r

(M · P)   [ N ∙ γ / α ]r             = M [ N ∙ γ / α ]r · P [ N ∙ γ / α ]r

(μ β ⇒ C) [ N ∙ γ / α ]r             = μ β ⇒ C [ N ∙ γ / α ]r'

([ β ] M) [ N ∙ γ / α ]r' with α ≟ β
...                          | yes _ = [ γ ] M [ N ∙ γ / α ]r · N
...                          | no  _ = [ β ] M [ N ∙ γ / α ]r

-- Left structural substitution
_[_∙_/_]l  : Term    → Term → Name → Name → Term
_[_∙_/_]l' : Command → Term → Name → Name → Command
(` x)     [ N ∙ γ / α ]l             = ` x

(ƛ x ⇒ M) [ N ∙ γ / α ]l             = ƛ x ⇒ M [ N ∙ γ / α ]l

(M · P)   [ N ∙ γ / α ]l             = M [ N ∙ γ / α ]l · P [ N ∙ γ / α ]l

(μ β ⇒ C) [ N ∙ γ / α ]l             = μ β ⇒ C [ N ∙ γ / α ]l'

([ β ] M) [ N ∙ γ / α ]l' with α ≟ β
...                          | yes _ = [ γ ] N · M [ N ∙ γ / α ]l
...                          | no  _ = [ β ] M [ N ∙ γ / α ]l


---------------- α-EQUIVALENCE ----------------
infixr 4 _=α_
infixr 4 _=α'_
data _=α_  : Term    → Term    → Set
data _=α'_ : Command → Command → Set

data _=α_ where
  [α-var] : ∀ {x : Id}
    ----------------
    → ` x =α ` x

  [α-λ] : ∀ {x y : Id} {M M' : Term}
    → y ∉ᵥ M'
    → M =α M'
    ----------------
    → ƛ x ⇒ M =α ƛ y ⇒ M' [ ` y / x ]β

  [α-μ] : ∀ {α β : Name} {C C' : Command}
    → β ∉ₙ' C'
    → C =α' C'
    ----------------
    → μ α ⇒ C =α μ β ⇒ C' [ β / α ]ρ'

  [α-abs] : ∀ {x : Id} {M M' : Term}
    → M =α M'
    ----------------
    → ƛ x ⇒ M =α ƛ x ⇒ M'

  [α-app] : ∀ {M M' N N' : Term}
    → M =α M'
    → N =α N'
    ----------------
    → M · N =α M' · N'

  [α-mu] : ∀ {β : Name} {C C' : Command}
    → C =α' C'
    ----------------
    → μ β ⇒ C =α μ β ⇒ C'

data _=α'_ where
  [α-name] : ∀ {β : Name} {M M' : Term}
    → M =α M'
    ----------------
    → [ β ] M =α' [ β ] M'


---------------- LMUV SINGLE STEP REDUCTION ----------------
infixr 4 _⟶_
infixr 4 _⟶'_
data _⟶_  : Term    → Term    → Set
data _⟶'_ : Command → Command → Set

data _⟶_ where
  [β] : ∀ {x : Id} {M V : Term}
    → Value V
    ----------------
    → (ƛ x ⇒ M) · V ⟶ M [ V / x ]β

  [μr] : ∀ {α γ : Name} {N : Term} {C : Command}
    → γ ∉ₙ ((μ α ⇒ C) · N)
    ----------------
    → (μ α ⇒ C) · N ⟶ μ γ ⇒ C [ N ∙ γ / α ]r'

  [μl] : ∀ {α γ : Name} {V : Term} {C : Command}
    → γ ∉ₙ (V · (μ α ⇒ C))
    → Value V
    ----------------
    → V · (μ α ⇒ C) ⟶ μ γ ⇒ C [ V ∙ γ / α ]l'

  [app-l] : ∀ {M M' N : Term}
    → M ⟶ M'
    ----------------
    → M · N ⟶ M' · N

  [app-r] : ∀ {M N N' : Term}
    → N ⟶ N'
    ----------------
    → M · N ⟶ M · N'

  [abs] : ∀ {x : Id} {M M' : Term}
    → M ⟶ M'
    ----------------
    → ƛ x ⇒ M ⟶ ƛ x ⇒ M'

  [mu] : ∀ {α : Name} {C C' : Command}
    → C ⟶' C'
    ----------------
    → μ α ⇒ C ⟶ μ α ⇒ C'

data _⟶'_ where
  [ρ] : ∀ {α β : Name} {C : Command}
    ----------------
    → [ α ] μ β ⇒ C ⟶' C [ α / β ]ρ'

  [name] : ∀ {α : Name} {M M' : Term}
    → M ⟶ M'
    ----------------
    → [ α ] M ⟶' [ α ] M'

-- Reflexive transitive closure of lmuv single step reduction
infixr 4 _⟶*_
infixr 4 _⟶*'_
_⟶*_  : Term    → Term    → Set
_⟶*'_ : Command → Command → Set
_⟶*_  = rtc _⟶_
_⟶*'_ = rtc _⟶'_

app-l* : ∀ {M M' N : Term}
  → M ⟶* M'
  ----------------
  → M · N ⟶* M' · N
app-l* reflx = reflx
app-l* (trans mp pm') = trans (app-l* mp) ([app-l] pm')
  
app-r* : ∀ {M N N' : Term}
  → N ⟶* N'
  ----------------
  → M · N ⟶* M · N'
app-r* reflx = reflx
app-r* (trans np pn') = trans (app-r* np) ([app-r] pn')

abs* : ∀ {x : Id} {M M' : Term}
  → M ⟶* M'
  ----------------
  → ƛ x ⇒ M ⟶* ƛ x ⇒ M'
abs* reflx = reflx
abs* (trans mn nm') = trans (abs* mn) ([abs] nm')

mu* : ∀ {α : Name} {C C' : Command}
  → C ⟶*' C'
  ----------------
  → μ α ⇒ C ⟶* μ α ⇒ C'
mu* reflx = reflx
mu* (trans cd dc') = trans (mu* cd) ([mu] dc')

name* : ∀ {α : Name} {M M' : Term}
  → M ⟶* M'
  ----------------
  → [ α ] M ⟶*' [ α ] M'
name* reflx = reflx
name* (trans mn nm') = trans (name* mn) ([name] nm')


app* : ∀ {M M' N N' : Term}
  → M ⟶* M'
  → N ⟶* N'
  ----------------
  → M · N ⟶* M' · N'
app* mm' nn' = trans-rtc (app-l* mm') (app-r* nn')


---------------- LMUV PARALLEL REDUCTION ----------------
infixr 4 _==>_
infixr 4 _==>'_
data _==>_  : Term    → Term    → Set
data _==>'_ : Command → Command → Set 
  
data _==>_ where
  [1] : ∀ {x : Id}
    ----------------
    → ` x ==> ` x

  [2] : ∀ {x : Id} {M M' : Term}
    → M ==> M'
    ----------------
    → ƛ x ⇒ M ==> ƛ x ⇒ M'

  [3] : ∀ {α : Name} {C C' : Command}
    → C ==>' C'
    ----------------
    → μ α ⇒ C ==> μ α ⇒ C'
    
  [4] : ∀ {M N M' N' : Term}
    → M ==> M'
    → N ==> N'
    ----------------
    → M · N ==> M' · N'

  [7] : ∀ {x : Id} {M M' N V : Term}
    → Value V
    → M ==> ƛ x ⇒ M'
    → N ==> V
    ----------------
    → M · N ==> M' [ V / x ]β

  [8] : ∀ {α γ : Name} {M N N' : Term} {C : Command}
    → γ ∉ₙ ((μ α ⇒ C) · N')
    → M ==> μ α ⇒ C
    → N ==> N'
    ----------------
    → M · N ==> μ γ ⇒ C [ N' ∙ γ / α ]r'

  [9] : ∀ {α γ : Name} {M V N : Term} {C : Command}
    → γ ∉ₙ (V · (μ α ⇒ C))
    → Value V
    → M ==> V
    → N ==> μ α ⇒ C
    ----------------
    → M · N ==> μ γ ⇒ C [ V ∙ γ / α ]l'

data _==>'_ where
  [5] : ∀ {α : Name} {M M' : Term}
    → M ==> M'
    ----------------
    → [ α ] M ==>' [ α ] M'

  [6] : ∀ {α β : Name} {M : Term} {C : Command}
    → M ==> μ β ⇒ C
    ----------------
    → [ α ] M ==>' C [ α / β ]ρ'

-- Reflexive transitive closure of lmuv parallel reduction
infixr 4 _==>*_
infixr 4 _==>*'_
_==>*_  : Term    → Term    → Set
_==>*'_ : Command → Command → Set
_==>*_  = rtc _==>_
_==>*'_ = rtc _==>'_

-- any term parallel reduces to itself
par-refl  : ∀ {M : Term}    → M ==> M
par-refl' : ∀ {C : Command} → C ==>' C

par-refl  {` x}     = [1]
par-refl  {ƛ x ⇒ M} = [2] par-refl
par-refl  {M · N}   = [4] par-refl par-refl
par-refl  {μ α ⇒ C} = [3] par-refl'
par-refl' {[ α ] M} = [5] par-refl


---------------- ⟶* = ==>* ----------------
-- Forward direction
sin-par  : ∀ {M N : Term}    → M ⟶ N  → M ==> N
sin-par' : ∀ {C D : Command} → C ⟶' D → C ==>' D
sin-par  ([β] val)      = [7] val par-refl par-refl
sin-par  ([μr] new)     = [8] new par-refl par-refl
sin-par  ([μl] new val) = [9] new val par-refl par-refl
sin-par  ([app-l] mm')  = [4] (sin-par mm') par-refl
sin-par  ([app-r] nn')  = [4] par-refl (sin-par nn')
sin-par  ([abs] mm')    = [2] (sin-par mm')
sin-par  ([mu] cc')     = [3] (sin-par' cc')
sin-par'  [ρ]           = [6] par-refl
sin-par' ([name] mm')   = [5] (sin-par mm')

sins-pars : ∀ {M N : Term} → M ⟶* N → M ==>* N
sins-pars reflx         = reflx
sins-pars (trans mp pn) = trans (sins-pars mp) (sin-par pn)

-- Backward direction
par-sins  : ∀ {M N : Term}    → M ==> N  → M ⟶* N
par-sins' : ∀ {C D : Command} → C ==>' D → C ⟶*' D
par-sins   [1]                = reflx
par-sins  ([2] mm')           = abs* (par-sins mm')
par-sins  ([3] cc')           = mu* (par-sins' cc')
par-sins  ([4] mm' nn')       = app* (par-sins mm') (par-sins nn')
par-sins  ([7] val mλ nv)     = trans (app* (par-sins mλ) (par-sins nv)) ([β] val)
par-sins  ([8] new mμ nn')    = trans (app* (par-sins mμ) (par-sins nn')) ([μr] new)
par-sins  ([9] new val mv mμ) = trans (app* (par-sins mv) (par-sins mμ)) ([μl] new val)
par-sins' ([5] mm')           = name* (par-sins mm')
par-sins' ([6] mμ)            = trans (name* (par-sins mμ)) [ρ]

pars-sins : ∀ {M N : Term} → M ==>* N → M ⟶* N
pars-sins reflx         = reflx
pars-sins (trans mp pn) = trans-rtc (pars-sins mp) (par-sins pn)