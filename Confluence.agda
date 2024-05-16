module Confluence where

open import Definitions
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)

-- The substitution lemmas
postulate β-subst-lemma : ∀ {z : Id} {P P' Q Q' : Term}      → P ==> P' → Q ==> Q  → P [ Q / z ]β     ==> P' [ Q' / z ]β

postulate ρ-subst-lemma : ∀ {α β : Name} {P P' : Term}       → P ==> P'            → P [ α / β ]ρ     ==> P' [ α / β ]ρ

postulate μr-subst-lemma : ∀ {α γ : Name} {P P' Q Q' : Term} → P ==> P' → Q ==> Q' → P [ Q ∙ γ / α ]r ==> P' [ Q' ∙ γ / α ]r

postulate μl-subst-lemma : ∀ {α γ : Name} {P P' Q Q' : Term} → P ==> P' → Q ==> Q' → P [ Q ∙ γ / α ]l ==> P' [ Q' ∙ γ / α ]l

-- Values only reduce to values
val-red-val : ∀ {V V' : Term} → V ==> V' → Value V → Value V'
val-red-val [1] Vx = Vx
val-red-val ([2] vv') Vƛ = Vƛ

-- The main theorem: If P0 ==> P1 and P0 ==> P2, there exists some P3 such that P1 ==> P3 and P2 ==> P3
==>-diamond : diamond _==>_
==>-diamond ([1] {x}) [1] = ⟨ (` x) , ⟨ [1] , [1] ⟩ ⟩

==>-diamond ([2] {x} tu) ([2] tv) with ==>-diamond tu tv
...                              | ⟨ w , ⟨ uw , vw ⟩ ⟩ = ⟨ ƛ x ⇒ w , ⟨ [2] uw , [2] vw ⟩ ⟩

==>-diamond ([3] {α} {β} tu) ([3] tv) with ==>-diamond tu tv
... | ⟨ w , ⟨ uw , vw ⟩ ⟩ = ⟨ μ α [ β ] w , ⟨ [3] uw , [3] vw ⟩ ⟩
==>-diamond ([3] {α} {β} tu) ([5] tμ) with ==>-diamond tu tμ
... | ⟨ w , ⟨ uw , μw ⟩ ⟩ = {!   !}

==>-diamond ([4] m0m1 n0n1) ([4] m0m2 n0n2) with ==>-diamond m0m1 m0m2
... | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ with ==>-diamond n0n1 n0n2 
... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ = ⟨ (m3 · n3) , ⟨ ([4] m1m3 n1n3) , ([4] m2m3 n2n3) ⟩ ⟩
==>-diamond ([4] m0m1 n0n1) ([6] {x} val m0λm2 n0v2) with ==>-diamond m0m1 m0λm2
... | ⟨ ƛ x ⇒ m3 , ⟨ m1m3 , [2] m2m3 ⟩ ⟩ with ==>-diamond n0n1 n0v2
... | ⟨ v3 , ⟨ n1v3 , v2v3 ⟩ ⟩ = ⟨ m3 [ v3 / x ]β , ⟨ [6] (val-red-val v2v3 val) m1m3 n1v3 , β-subst-lemma m2m3 par-refl ⟩ ⟩
==>-diamond ([4] m0m1 n0n1) ([7] tv tv₁) = {!   !}
==>-diamond ([4] m0m1 n0n1) ([8] x tv tv₁) = {!   !}

==>-diamond ([5] tu) tv = {!   !} 
==>-diamond ([6] x tu tu₁) tv = {!   !}
==>-diamond ([7] tu tu₁) tv = {!   !}  
==>-diamond ([8] x tu tu₁) tv = {!   !}