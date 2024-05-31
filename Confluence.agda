module Confluence where

open import Definitions
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)

-- The substitution lemmas
postulate β-subst-lemma : ∀ {z : Id} {M N P Q : Term} → M ==> N → P ==> Q → M [ P / z ]β ==> N [ Q / z ]β
postulate ρ-subst-lemma : ∀ {α β : Name} {C D : Command} → C ==>' D → C [ α / β ]ρ' ==>' D [ α / β ]ρ'
postulate μr-subst-lemma : ∀ {α γ δ : Name} {C D : Command} {M N : Term} → C ==>' D → M ==> N → γ ∉ (μ α ⇒ C) · M → δ ∉ (μ α ⇒ D) · N → μ γ ⇒ C [ M ∙ γ / α ]r' ==> μ δ ⇒ D [ N ∙ δ / α ]r'
postulate μl-subst-lemma : ∀ {α γ δ : Name} {C D : Command} {M N : Term} → C ==>' D → M ==> N → γ ∉ M · (μ α ⇒ C) → δ ∉ N · (μ α ⇒ D) → μ γ ⇒ C [ M ∙ γ / α ]l' ==> μ δ ⇒ D [ N ∙ δ / α ]l'

-- Values only reduce to values
val-red-val : ∀ {V V' : Term} → V ==> V' → Value V → Value V'
val-red-val [1] Vx = Vx
val-red-val ([2] vv') Vƛ = Vƛ

-- The main theorem: If P0 ==> P1 and P0 ==> P2, there exists some P3 such that P1 ==> P3 and P2 ==> P3
{-# TERMINATING #-}
==>-diamond  : diamond _==>_
==>-diamond' : diamond _==>'_

-- Helper function for main theorem
reverse  : diamond _==>_
reverse' : diamond _==>'_ 
reverse  p0p1 p0p2 with ==>-diamond p0p2 p0p1
...                   | ⟨ p3 , ⟨ p2p3 , p1p3 ⟩ ⟩ = ⟨ p3 , ⟨ p1p3 , p2p3 ⟩ ⟩
reverse' c0c1 c0c2 with ==>-diamond' c0c2 c0c1
...                   | ⟨ c3 , ⟨ c2c3 , c1c3 ⟩ ⟩ = ⟨ c3 , ⟨ c1c3 , c2c3 ⟩ ⟩

==>-diamond ([1] {x}) [1] = ⟨ (` x) , ⟨ [1] , [1] ⟩ ⟩


==>-diamond ([2] {x} m0m1) ([2] m0m2) with ==>-diamond m0m1 m0m2
...                              | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ 
  = ⟨ ƛ x ⇒ m3 , ⟨ [2] m1m3 , [2] m2m3 ⟩ ⟩


==>-diamond ([3] {α} c0c1) ([3] c0c2) with ==>-diamond' c0c1 c0c2
...                              | ⟨ c3 , ⟨ c1c3 , c2c3 ⟩ ⟩ 
  = ⟨ μ α ⇒ c3 , ⟨ [3] c1c3 , [3] c2c3 ⟩ ⟩


==>-diamond ([4] m0m1 n0n1) ([4] m0m2 n0n2) with ==>-diamond m0m1 m0m2
... | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ 
  = ⟨ (m3 · n3) , ⟨ [4] m1m3 n1n3 , [4] m2m3 n2n3 ⟩ ⟩

==>-diamond ([4] m0m1 n0n1) ([7] {x} val m0λm2 n0v2) with ==>-diamond m0m1 m0λm2 
... | ⟨ ƛ x ⇒ m3 , ⟨ m1λm3 , [2] m2m3 ⟩ ⟩ with ==>-diamond n0n1 n0v2
... | ⟨ v3 , ⟨ n1v3 , v2v3 ⟩ ⟩ 
  = ⟨ (m3 [ v3 / x ]β) , ⟨ [7] (val-red-val v2v3 val) m1λm3 n1v3 , β-subst-lemma m2m3 v2v3 ⟩ ⟩

==>-diamond ([4] m0m1 n0n1) ([8] {α} γ∉αc2n2 m0μc2 n0n2) with ==>-diamond m0m1 m0μc2 
... | ⟨ μ α ⇒ c3 , ⟨ m1μc3 , [3] c2c3 ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ with fresh ((μ α ⇒ c3) · n3)
... | ⟨ δ , δ∉αc3n3 ⟩ 
  = ⟨ μ δ ⇒ c3 [ n3 ∙ δ / α ]r' , ⟨ [8] δ∉αc3n3 m1μc3 n1n3 , μr-subst-lemma c2c3 n2n3 γ∉αc2n2 δ∉αc3n3 ⟩ ⟩

==>-diamond ([4] m0m1 n0n1) ([9] {α} γ∉v2αc2 val m0v2 n0μc2) with ==>-diamond m0m1 m0v2
... | ⟨ v3 , ⟨ m1v3 , v2v3 ⟩ ⟩ with ==>-diamond n0n1 n0μc2
... | ⟨ μ α ⇒ c3 , ⟨ n1μc3 , [3] c2c3 ⟩ ⟩ with fresh (v3 · (μ α ⇒ c3))
... | ⟨ δ , δ∉v3αc3 ⟩ 
  = ⟨ μ δ ⇒ c3 [ v3 ∙ δ / α ]l' , ⟨ [9] δ∉v3αc3 (val-red-val v2v3 val) m1v3 n1μc3 , μl-subst-lemma c2c3 v2v3 γ∉v2αc2 δ∉v3αc3 ⟩ ⟩


==>-diamond p0p1@([7] _ _ _) p0p2@([4] _ _) 
  = reverse p0p1 p0p2

==>-diamond ([7] v_ m0λm1 n0v1) ([7] _ m0λm2 n0v2) with ==>-diamond m0λm1 m0λm2 
... | ⟨ ƛ x ⇒ m3 , ⟨ [2] m1m3 , [2] m2m3 ⟩ ⟩ with ==>-diamond n0v1 n0v2
... | ⟨ v3 , ⟨ v1v3 , v2v3 ⟩ ⟩ 
  = ⟨ m3 [ v3 / x ]β , ⟨ β-subst-lemma m1m3 v1v3 , β-subst-lemma m2m3 v2v3 ⟩ ⟩

==>-diamond ([7] _ m0λm1 _) ([8] _ m0μc2 _) with ==>-diamond m0λm1 m0μc2
... | ⟨ .(ƛ _ ⇒ _) , ⟨ [2] _ , () ⟩ ⟩

==>-diamond ([7] val _ n0v1) ([9] _ _ _ n0μc2) with ==>-diamond n0v1 n0μc2 
... | ⟨ .(μ _ ⇒ _) , ⟨ v1μc3 , [3] _ ⟩ ⟩ with val-red-val v1μc3 val
... | ()


==>-diamond p0p1@([8] _ _ _) p0p2@([4] _ _) = reverse p0p1 p0p2

==>-diamond p0p1@([8] _ _ _) p0p2@([7] _ _ _) = reverse p0p1 p0p2

==>-diamond ([8] {α} γ∉αc1n1 m0μc1 n0n1) ([8] δ∉αc2n2 m0μc2 n0n2) with ==>-diamond m0μc1 m0μc2
... | ⟨ μ α ⇒ c3 , ⟨ [3] c1c3 , [3] c2c3 ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ with fresh ((μ α ⇒ c3) · n3)
... | ⟨ ε , ε∉αc3n3 ⟩ 
  = ⟨ μ ε ⇒ c3 [ n3 ∙ ε / α ]r' , ⟨ μr-subst-lemma c1c3 n1n3 γ∉αc1n1 ε∉αc3n3 , μr-subst-lemma c2c3 n2n3 δ∉αc2n2 ε∉αc3n3 ⟩ ⟩

==>-diamond ([8] _ m0μc1 _) ([9] _ val2 m0v2 _) with ==>-diamond m0μc1 m0v2
... | ⟨ .(μ _ ⇒ _) , ⟨ [3] _ , v2v3 ⟩ ⟩ with val-red-val v2v3 val2
... | ()


==>-diamond p0p1@([9] _ _ _ _) p0p2@([4] _ _) = reverse p0p1 p0p2

==>-diamond p0p1@([9] _ _ _ _) p0p2@([7] _ _ _) = reverse p0p1 p0p2

==>-diamond p0p1@([9] _ _ _ _) p0p2@([8] _ _ _) = reverse p0p1 p0p2

==>-diamond ([9] {α} γ∉v1αc1 val1 m0v1 n0μc1) ([9] δ∉v2αc2 val2 m0v2 n0μc2) with ==>-diamond m0v1 m0v2
... | ⟨ v3 , ⟨ v1v3 , v2v3 ⟩ ⟩ with ==>-diamond n0μc1 n0μc2
... | ⟨ μ α ⇒ c3 , ⟨ [3] c1c3 , [3] c2c3 ⟩ ⟩ with fresh (v3 · (μ α ⇒ c3))
... | ⟨ ε , ε∉v3αc3 ⟩ 
  = ⟨ μ ε ⇒ c3 [ v3 ∙ ε / α ]l' , ⟨ μl-subst-lemma c1c3 v1v3 γ∉v1αc1 ε∉v3αc3 , μl-subst-lemma c2c3 v2v3 δ∉v2αc2 ε∉v3αc3 ⟩ ⟩


==>-diamond' ([5] {α} m0m1) ([5] m0m2) with ==>-diamond m0m1 m0m2
... | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ 
  = ⟨ [ α ] m3 , ⟨ ([5] m1m3) , ([5] m2m3) ⟩ ⟩

==>-diamond' ([5] {α} m0m1) ([6] m0μc2) with ==>-diamond m0m1 m0μc2
... | ⟨ μ β ⇒ c3 , ⟨ m1μc3 , [3] c2c3 ⟩ ⟩ 
  = ⟨ c3 [ α / β ]ρ' , ⟨ [6] m1μc3 , ρ-subst-lemma c2c3 ⟩ ⟩


==>-diamond' c0c1@([6] _) c0c2@([5] _) = reverse' c0c1 c0c2

==>-diamond' ([6] {α} {β} m0μc1) ([6] m0μc2) with ==>-diamond m0μc1 m0μc2
... | ⟨ μ β ⇒ c3 , ⟨ [3] c1c3 , [3] c2c3 ⟩ ⟩ 
  = ⟨ c3 [ α / β ]ρ' , ⟨ ρ-subst-lemma c1c3 , ρ-subst-lemma c2c3 ⟩ ⟩
