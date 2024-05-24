module Confluence where

open import Definitions
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _⊓_; _>_) renaming (_≟_ to _≟n_)
open import Relation.Nullary using (Dec; yes; no; ¬_)

-- The substitution lemmas
postulate β-subst-lemma : ∀ {z : Id} {P P' Q Q' : Term}      → P ==> P' → Q ==> Q  → P [ Q / z ]β     ==> P' [ Q' / z ]β
postulate ρ-subst-lemma : ∀ {α β : Name} {P P' : Term}       → P ==> P'            → P [ α / β ]ρ     ==> P' [ α / β ]ρ
postulate μr-subst-lemma : ∀ {α γ : Name} {P P' Q Q' : Term} → P ==> P' → Q ==> Q' → P [ Q ∙ γ / α ]r ==> P' [ Q' ∙ γ / α ]r
postulate μl-subst-lemma : ∀ {α γ : Name} {P P' Q Q' : Term} → P ==> P' → Q ==> Q' → P [ Q ∙ γ / α ]l ==> P' [ Q' ∙ γ / α ]l

postulate β-subst-lemma' : ∀ {z : Id} {C C' : Command} {Q Q' : Term}      → C ==>' C' → Q ==> Q  → C [ Q / z ]β'     ==>' C' [ Q' / z ]β'
postulate ρ-subst-lemma' : ∀ {α β : Name} {C C' : Command}                → C ==>' C'            → C [ α / β ]ρ'     ==>' C' [ α / β ]ρ'
postulate μr-subst-lemma' : ∀ {α γ : Name} {C C' : Command} {Q Q' : Term} → C ==>' C' → Q ==> Q' → C [ Q ∙ γ / α ]r' ==>' C' [ Q' ∙ γ / α ]r'
postulate μl-subst-lemma' : ∀ {α γ : Name} {C C' : Command} {Q Q' : Term} → C ==>' C' → Q ==> Q' → C [ Q ∙ γ / α ]l' ==>' C' [ Q' ∙ γ / α ]l'

-- lem : ∀ {α β : Name} (P : Term) → β > max P → P [ α / β ]ρ ≡ P
-- lem' : ∀ {α β : Name} (C : Command) → β > max' C → C [ α / β ]ρ' ≡ C
-- lem (` x) fresh = refl
-- lem {α} {β} (ƛ x ⇒ M) fresh rewrite lem {α} {β} M fresh = refl
-- lem (μ x ⇒ x₁) fresh = {!   !}
-- lem (M · N) fresh = {!   !}
-- lem' ([ x ] x₁) fresh = {!   !}

postulate fresh-subst-lemma :  ∀ {α γ δ : Name} {M N : Term} → γ > max (M · N) → δ > max (M · N) → (M [ N ∙ γ / α ]r) [ δ / γ ]ρ ≡ M [ N ∙ δ / α ]r

postulate fresh-subst-lemma' : ∀ {α γ δ : Name} {C : Command} {N : Term} → γ > max ((μ α ⇒ C) · N) → δ > max ((μ α ⇒ C) · N) → (C [ N ∙ γ / α ]r') [ δ / γ ]ρ' ≡ C [ N ∙ δ / α ]r'

-- fresh-subst-lemma :  ∀ {α γ δ : Name} {M N : Term}
--   → γ > max (M · N)
--   → δ > max (M · N)
--   ----------------
--   → (M [ N ∙ γ / α ]r) [ δ / γ ]ρ ≡ M [ N ∙ δ / α ]r

-- fresh-subst-lemma' : ∀ {α γ δ : Name} {C : Command} {N : Term} 
--   → γ > max ((μ α ⇒ C) · N) 
--   → δ > max ((μ α ⇒ C) · N) 
--   ----------------
--   → (C [ N ∙ γ / α ]r') [ δ / γ ]ρ' ≡ C [ N ∙ δ / α ]r'

-- fresh-subst-lemma {M = ` x} freshγ freshδ = refl
-- fresh-subst-lemma {α} {γ} {δ} {ƛ x ⇒ M} {N} freshγ freshδ rewrite 
--   fresh-subst-lemma {α} {γ} {δ} {M} {N} freshγ freshδ = refl
-- fresh-subst-lemma {M = μ x ⇒ C} freshγ freshδ = {!   !}
-- fresh-subst-lemma {α} {γ} {δ} {M = P · Q} {N} freshγ freshδ {-rewrite 
--   fresh-subst-lemma {α} {γ} {δ} {P} {N} freshγ freshδ |
--   fresh-subst-lemma {α} {γ} {δ} {Q} {N} freshγ freshδ-} = {!   !}

-- fresh-subst-lemma' {α} {γ} {δ} {C = [ β ] M} {N} freshγ freshδ with α ≟n β
-- ... | yes p with γ ≟n γ
-- ...   | yes refl rewrite = {!   !}
-- ...   | no r = {! r !}
-- fresh-subst-lemma' {α} {γ} {δ} {C = [ β ] M} {N} freshγ freshδ
--     | no ¬p = {!   !}

-- Values only reduce to values
val-red-val : ∀ {V V' : Term} → V ==> V' → Value V → Value V'
val-red-val [1] Vx = Vx
val-red-val ([2] vv') Vƛ = Vƛ

-- The main theorem: If P0 ==> P1 and P0 ==> P2, there exists some P3 such that P1 ==> P3 and P2 ==> P3
==>-diamond  : diamond _==>_
==>-diamond' : diamond _==>'_

==>-diamond ([1] {x}) [1] = ⟨ (` x) , ⟨ [1] , [1] ⟩ ⟩


==>-diamond ([2] {x} m0m1) ([2] m0m2) with ==>-diamond m0m1 m0m2
...                              | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ = ⟨ ƛ x ⇒ m3 , ⟨ [2] m1m3 , [2] m2m3 ⟩ ⟩


==>-diamond ([3] {α} c0c1) ([3] c0c2) with ==>-diamond' c0c1 c0c2
...                              | ⟨ c3 , ⟨ c1c3 , c2c3 ⟩ ⟩ = ⟨ μ α ⇒ c3 , ⟨ [3] c1c3 , [3] c2c3 ⟩ ⟩

==>-diamond ([3] {α} c0c1) ([0] freshγ) = {!   !}


==>-diamond ([4] m0m1 n0n1) ([4] m0m2 n0n2) with ==>-diamond m0m1 m0m2
... | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ = ⟨ (m3 · n3) , ⟨ [4] m1m3 n1n3 , [4] m2m3 n2n3 ⟩ ⟩

==>-diamond ([4] m0m1 n0n1) ([7] {x} val m0λm2 n0v2) with ==>-diamond m0m1 m0λm2 
... | ⟨ ƛ x ⇒ m3 , ⟨ m1λm3 , [2] m2m3 ⟩ ⟩ with ==>-diamond n0n1 n0v2
... | ⟨ v3 , ⟨ n1v3 , v2v3 ⟩ ⟩ = ⟨ (m3 [ v3 / x ]β) , ⟨ [7] (val-red-val v2v3 val) m1λm3 n1v3 , β-subst-lemma m2m3 par-refl ⟩ ⟩

-- ==>-diamond ([4] m0m1 n0n1) ([8] {α} {γ} freshγ m0μc2 n0n2) with ==>-diamond m0m1 m0μc2 
-- ... | ⟨ μ α ⇒ c3 , ⟨ m1μc3 , [3] c2c3 ⟩ ⟩ with ==>-diamond n0n1 n0n2
-- ... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ with max ((μ α ⇒ c3) · n3)
-- ... | δ = ⟨ μ δ ⇒ c3 [ n3 ∙ δ / α ]r' , {!   !} ⟩
==>-diamond ([4] m0m1 n0n1) ([8] {α} {γ} freshγ m0μc2 n0n2) with ==>-diamond m0m1 m0μc2
... | ⟨ μ α ⇒ c3 , ⟨ m1m3 , [3] c2c3 ⟩ ⟩ = {!   !}
... | ⟨ .(μ _ ⇒ _ [ _ / α ]ρ') , ⟨ m1m3 , [0] x ⟩ ⟩ = {!   !}

==>-diamond ([4] m0m1 n0n1) ([9] {α} {γ} freshγ val m0v2 n0μc2) with ==>-diamond m0m1 m0v2
... | ⟨ v3 , ⟨ m1v3 , v2v3 ⟩ ⟩ with ==>-diamond n0n1 n0μc2
... | ⟨ μ α ⇒ c3 , ⟨ n1μc3 , [3] c2c3 ⟩ ⟩ with max (v3 · (μ α ⇒ c3))
... | δ = ⟨ μ δ ⇒ c3 [ v3 ∙ δ / α ]l' , {!   !} ⟩


==>-diamond ([7] val m0λm1 n0v1) ([4] m0m2 n0n2) with ==>-diamond m0λm1 m0m2
... | ⟨ ƛ x ⇒ m3 , ⟨ [2] m1m3 , m2λm3 ⟩ ⟩ with ==>-diamond n0v1 n0n2
... | ⟨ v3 , ⟨ v1v3 , n2v3 ⟩ ⟩ = ⟨ (m3 [ v3 / x ]β) , ⟨ β-subst-lemma m1m3 par-refl , [7] (val-red-val v1v3 val) m2λm3 n2v3 ⟩ ⟩

==>-diamond ([7] v_ m0λm1 n0v1) ([7] _ m0λm2 n0v2) with ==>-diamond m0λm1 m0λm2 
... | ⟨ ƛ x ⇒ m3 , ⟨ [2] m1m3 , [2] m2m3 ⟩ ⟩ with ==>-diamond n0v1 n0v2
... | ⟨ v3 , ⟨ v1v3 , v2v3 ⟩ ⟩ = ⟨ m3 [ v3 / x ]β , ⟨ β-subst-lemma m1m3 par-refl , β-subst-lemma m2m3 par-refl ⟩ ⟩

==>-diamond ([7] _ m0λm1 _) ([8] _ m0μc2 _) with ==>-diamond m0λm1 m0μc2
... | ⟨ .(ƛ _ ⇒ _) , ⟨ [2] _ , () ⟩ ⟩

==>-diamond ([7] val _ n0v1) ([9] _ _ _ n0μc2) with ==>-diamond n0v1 n0μc2 
... | ⟨ .(μ _ ⇒ _) , ⟨ v1μc3 , [3] _ ⟩ ⟩ with val-red-val v1μc3 val
... | ()


==>-diamond ([8] {α} {γ} freshγ m0μc1 n0n1) ([4] m0m2 n0n2) with ==>-diamond m0μc1 m0m2
... | ⟨ μ α ⇒ c3 , ⟨ [3] m1m3 , m2μc3 ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ with max ((μ α ⇒ c3) · n3)
... | δ = ⟨ μ δ ⇒ c3 [ n3 ∙ δ / α ]r' , {!   !} ⟩

==>-diamond ([8] _ m0μc1 _) ([7] _ m0λm2 _) with ==>-diamond m0μc1 m0λm2
... | ⟨ .(μ _ ⇒ _) , ⟨ [3] _ , () ⟩ ⟩

==>-diamond ([8] {α} {γ} freshγ m0μc1 n0n1) ([8] freshδ m0μc2 n0n2) with ==>-diamond m0μc1 m0μc2
... | ⟨ μ α ⇒ c3 , ⟨ [3] c1c3 , [3] c2c3 ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ = {!   !}

==>-diamond ([8] _ m0μc1 _) ([9] _ val2 m0v2 _) with ==>-diamond m0μc1 m0v2
... | ⟨ .(μ _ ⇒ _) , ⟨ [3] _ , v2v3 ⟩ ⟩ with val-red-val v2v3 val2
... | ()


==>-diamond ([9] {α} {γ} freshγ val1 m0v1 n0μc1) ([4] m0m2 n0n2) with ==>-diamond m0v1 m0m2
... | ⟨ v3 , ⟨ v1v3 , m2v3 ⟩ ⟩ with ==>-diamond n0μc1 n0n2
... | ⟨ μ α ⇒ c3 , ⟨ [3] c1c3 , n2μc3 ⟩ ⟩ with max (v3 · (μ α ⇒ c3))
... | δ = ⟨ (μ δ ⇒ c3 [ v3 ∙ δ / α ]l') , {!   !} ⟩

==>-diamond ([9] _ _ _ n0μc1) ([7] val2 _ n0v2) with ==>-diamond n0μc1 n0v2
... | ⟨ .(μ _ ⇒ _) , ⟨ [3] _ , v2v3 ⟩ ⟩ with val-red-val v2v3 val2
... | ()

==>-diamond ([9] _ val1 m0v1 _) ([8] _ m0μc2 _) with ==>-diamond m0v1 m0μc2
... | ⟨ .(μ _ ⇒ _) , ⟨ v1v3 , [3] _ ⟩ ⟩ with val-red-val v1v3 val1 
... | ()

==>-diamond ([9] {α} {γ} freshγ val1 m0v1 n0μc1) ([9] freshδ val2 m0v2 n0μc2) with ==>-diamond m0v1 m0v2
... | ⟨ v3 , ⟨ v1v3 , v2v3 ⟩ ⟩ with ==>-diamond n0μc1 n0μc2
... | ⟨ μ α ⇒ c3 , ⟨ [3] c1c3 , [3] c2c3 ⟩ ⟩ = {!   !}

==>-diamond ([0] freshγ) ([3] x) = {!   !}
==>-diamond ([0] freshγ) ([0] x) = {!   !}


==>-diamond' ([5] {α} m0m1) ([5] m0m2) with ==>-diamond m0m1 m0m2
... | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ = ⟨ [ α ] m3 , ⟨ ([5] m1m3) , ([5] m2m3) ⟩ ⟩

==>-diamond' ([5] {α} m0m1) ([6] m0μc2) with ==>-diamond m0m1 m0μc2
... | ⟨ μ β ⇒ c3 , ⟨ m1μc3 , [3] c2c3 ⟩ ⟩ = ⟨ c3 [ α / β ]ρ' , ⟨ [6] m1μc3 , ρ-subst-lemma' c2c3 ⟩ ⟩


==>-diamond' ([6] m0μc1) ([5] {α} m0m2) with ==>-diamond m0μc1 m0m2 
... | ⟨ μ β ⇒ c3 , ⟨ [3] c1c3 , m2μc3 ⟩ ⟩ = ⟨ c3 [ α / β ]ρ' , ⟨ ρ-subst-lemma' c1c3 , [6] m2μc3 ⟩ ⟩
 
==>-diamond' ([6] {α} {β} m0μc1) ([6] m0μc2) with ==>-diamond m0μc1 m0μc2
... | ⟨ μ β ⇒ c3 , ⟨ [3] c1c3 , [3] c2c3 ⟩ ⟩ = ⟨ c3 [ α / β ]ρ' , ⟨ ρ-subst-lemma' c1c3 , ρ-subst-lemma' c2c3 ⟩ ⟩
