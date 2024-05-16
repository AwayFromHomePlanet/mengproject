module Confluence where

open import Definitions
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)

-- The substitution lemmas
postulate β-subst-lemma : ∀ {z : Id} {P P' Q Q' : Term}      → P ==> P' → Q ==> Q  → P [ Q / z ]β     ==> P' [ Q' / z ]β
postulate ρ-subst-lemma : ∀ {α β : Name} {P P' : Term}       → P ==> P'            → P [ α / β ]ρ     ==> P' [ α / β ]ρ
postulate μr-subst-lemma : ∀ {α γ : Name} {P P' Q Q' : Term} → P ==> P' → Q ==> Q' → P [ Q ∙ γ / α ]r ==> P' [ Q' ∙ γ / α ]r
postulate μl-subst-lemma : ∀ {α γ : Name} {P P' Q Q' : Term} → P ==> P' → Q ==> Q' → P [ Q ∙ γ / α ]l ==> P' [ Q' ∙ γ / α ]l

postulate β-subst-lemma' : ∀ {z : Id} {C C' : Command} {Q Q' : Term}      → C ==>' C' → Q ==> Q  → C [ Q / z ]β'     ==>' C' [ Q' / z ]β'
postulate ρ-subst-lemma' : ∀ {α β : Name} {C C' : Command}                → C ==>' C'            → C [ α / β ]ρ'     ==>' C' [ α / β ]ρ'
postulate μr-subst-lemma' : ∀ {α γ : Name} {C C' : Command} {Q Q' : Term} → C ==>' C' → Q ==> Q' → C [ Q ∙ γ / α ]r' ==>' C' [ Q' ∙ γ / α ]r'
postulate μl-subst-lemma' : ∀ {α γ : Name} {C C' : Command} {Q Q' : Term} → C ==>' C' → Q ==> Q' → C [ Q ∙ γ / α ]l' ==>' C' [ Q' ∙ γ / α ]l'

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


==>-diamond ([4] m0m1 n0n1) ([4] m0m2 n0n2) with ==>-diamond m0m1 m0m2
... | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ = ⟨ (m3 · n3) , ⟨ ([4] m1m3 n1n3) , ([4] m2m3 n2n3) ⟩ ⟩

==>-diamond ([4] m0m1 n0n1) ([7] {x} val m0λm2 n0v2) with ==>-diamond m0m1 m0λm2 
... | ⟨ ƛ x ⇒ m3 , ⟨ m1λm3 , [2] m2m3 ⟩ ⟩ with ==>-diamond n0n1 n0v2
... | ⟨ v3 , ⟨ n1v3 , v2v3 ⟩ ⟩ = ⟨ (m3 [ v3 / x ]β) , ⟨ ([7] (val-red-val v2v3 val) m1λm3 n1v3) , (β-subst-lemma m2m3 par-refl) ⟩ ⟩

==>-diamond ([4] m0m1 n0n1) ([8] {α} {γ} m0μc2 n0n2) with ==>-diamond m0m1 m0μc2 
... | ⟨ μ α ⇒ c3 , ⟨ m1μc3 , [3] c2c3 ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ = ⟨ μ γ ⇒ c3 [ n3 ∙ γ / α ]r' , ⟨ ([8] m1μc3 n1n3) , ([3] (μr-subst-lemma' c2c3 n2n3)) ⟩ ⟩

==>-diamond ([4] m0m1 n0n1) ([9] {α} {γ} val m0v2 n0μc2) with ==>-diamond m0m1 m0v2
... | ⟨ v3 , ⟨ m1v3 , v2v3 ⟩ ⟩ with ==>-diamond n0n1 n0μc2
... | ⟨ μ α ⇒ c3 , ⟨ n1μc3 , [3] c2c3 ⟩ ⟩ = ⟨ (μ γ ⇒ c3 [ v3 ∙ γ / α ]l') , ⟨ ([9] (val-red-val v2v3 val) m1v3 n1μc3) , [3] (μl-subst-lemma' c2c3 v2v3) ⟩ ⟩


==>-diamond ([7] x tu tu₁) tv = {!   !}


==>-diamond ([8] tu tu₁) tv = {!   !}


==>-diamond ([9] x tu tu₁) tv = {!   !}


==>-diamond' ([5] x) tv = {!   !}


==>-diamond' ([6] x) tv = {!   !}
