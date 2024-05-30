module Confluence where

open import Definitions
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- The substitution lemmas
postulate ==>-β-subst : ∀ {z : Id} {P P' Q Q' : Term}      → P ==> P' → Q ==> Q' → P [ Q / z ]β     ==> P' [ Q' / z ]β
postulate ==>-ρ-subst : ∀ {α β : Name} {P P' : Term}       → P ==> P'            → P [ α / β ]ρ     ==> P' [ α / β ]ρ
postulate ==>-μr-subst : ∀ {α γ : Name} {P P' Q Q' : Term} → P ==> P' → Q ==> Q' → P [ Q ∙ γ / α ]r ==> P' [ Q' ∙ γ / α ]r
postulate ==>-μl-subst : ∀ {α γ : Name} {P P' Q Q' : Term} → P ==> P' → Q ==> Q' → P [ Q ∙ γ / α ]l ==> P' [ Q' ∙ γ / α ]l

postulate ==>-β-subst' : ∀ {z : Id} {C C' : Command} {Q Q' : Term}      → C ==>' C' → Q ==> Q' → C [ Q / z ]β'     ==>' C' [ Q' / z ]β'
postulate ==>-ρ-subst' : ∀ {α β : Name} {C C' : Command}                → C ==>' C'            → C [ α / β ]ρ'     ==>' C' [ α / β ]ρ'
postulate ==>-μr-subst' : ∀ {α γ : Name} {C C' : Command} {Q Q' : Term} → C ==>' C' → Q ==> Q' → C [ Q ∙ γ / α ]r' ==>' C' [ Q' ∙ γ / α ]r'
postulate ==>-μl-subst' : ∀ {α γ : Name} {C C' : Command} {Q Q' : Term} → C ==>' C' → Q ==> Q' → C [ Q ∙ γ / α ]l' ==>' C' [ Q' ∙ γ / α ]l'

postulate =α-β-subst : ∀ {x : Id} {M M' N N' : Term} → M =α M' → N =α N' → M [ N / x ]β =α M' [ N' / x ]β

-- postulate ≡-ββ-subst : ∀ {x y : Id} {M N : Term} → y ∉ᵥ M → M [ ` y / x ]β [ N / y ]β ≡ M [ N / x ]β

postulate ≣-ρρ-subst : ∀ {α β γ : Name} {C D : Command} → β ∉' C → C [ β / α ]ρ' [ γ / β ]ρ' ≡ C [ γ / α ]ρ'

postulate =α-ρ-fresh : ∀ {α β γ δ : Name} (C D : Command) → γ ∉' C → γ ∉' D → C [ γ / α ]ρ' =α' D [ γ / β ]ρ' → C [ δ / α ]ρ' =α' D [ δ / β ]ρ'

postulate =α-ρ-μr : ∀ {α β γ δ ε : Name} {M N : Term} (C D : Command) → ε ∉' C → ε ∉' D → C [ ε / α ]ρ' =α' D [ ε / β ]ρ' → M =α N → μ γ ⇒ C [ M ∙ γ / α ]r' =α μ δ ⇒ D [ N ∙ δ / β ]r'

postulate =α-ρ-μl : ∀ {α β γ δ ε : Name} {M N : Term} (C D : Command) → ε ∉' C → ε ∉' D → C [ ε / α ]ρ' =α' D [ ε / β ]ρ' → M =α N → μ γ ⇒ C [ M ∙ γ / α ]l' =α μ δ ⇒ D [ N ∙ δ / β ]l'

-- Values only reduce to values
val-red-val : ∀ {V V' : Term} → V ==> V' → Value V → Value V'
val-red-val [1] Vx = Vx
val-red-val ([2] vv') Vƛ = Vƛ

-- Values are only α-equivalent to values
val-α-val : ∀ {V V' : Term} → V =α V' → Value V → Value V'
val-α-val [α-var] Vx = Vx
val-α-val ([α-λ] _) Vƛ = Vƛ

-- The main theorem: If P0 ==> P1 and P0 ==> P2, there exists some P3 such that P1 ==> P3 and P2 ==> P3
{-# TERMINATING #-}
==>-diamond  : diamond _==>_  _=α_
==>-diamond' : diamond _==>'_ _=α'_

-- Helper function for main theorem
reverse : diamond _==>_  _=α_
reverse' : diamond _==>'_  _=α'_
reverse p0p1 p0p2 with ==>-diamond p0p2 p0p1
... | ⟨ p4 , ⟨ p3 , ⟨ p4~p3 , ⟨ p2p4 , p1p3 ⟩ ⟩ ⟩ ⟩
  = ⟨ p3 , ⟨ p4 , ⟨ =α-symm p4~p3 , ⟨ p1p3 , p2p4 ⟩ ⟩ ⟩ ⟩
reverse' c0c1 c0c2 with ==>-diamond' c0c2 c0c1
... | ⟨ c4 , ⟨ c3 , ⟨ c4~c3 , ⟨ c2c4 , c1c3 ⟩ ⟩ ⟩ ⟩
  = ⟨ c3 , ⟨ c4 , ⟨ =α-symm' c4~c3 , ⟨ c1c3 , c2c4 ⟩ ⟩ ⟩ ⟩

==>-diamond ([1] {x}) [1] 
  = ⟨ ` x , ⟨ ` x , ⟨ [α-var] , ⟨ [1] , [1] ⟩ ⟩ ⟩ ⟩


==>-diamond ([2] {x} m0m1) ([2] m0m2) with ==>-diamond m0m1 m0m2
... | ⟨ m3 , ⟨ m4 , ⟨ m3~m4 , ⟨ m1m3 , m2m4 ⟩ ⟩ ⟩ ⟩ 
  = ⟨ ƛ x ⇒ m3 , ⟨ ƛ x ⇒ m4 , ⟨ [α-λ] m3~m4 , ⟨ ([2] m1m3) , ([2] m2m4) ⟩ ⟩ ⟩ ⟩


==>-diamond ([3] {α} c0c1) ([3] c0c2) with ==>-diamond' c0c1 c0c2
... | ⟨ c3 , ⟨ c4 , ⟨ c3~c4 , ⟨ c1c3 , c2c4 ⟩ ⟩ ⟩ ⟩ 
  = ⟨ μ α ⇒ c3 , ⟨ μ α ⇒ c4 , ⟨ =α-mu c3~c4 , ⟨ [3] c1c3 , [3] c2c4 ⟩ ⟩ ⟩ ⟩


==>-diamond ([4] m0m1 n0n1) ([4] m0m2 n0n2) with ==>-diamond m0m1 m0m2
... | ⟨ m3 , ⟨ m4 , ⟨ m3~m4 , ⟨ m1m3 , m2m4 ⟩ ⟩ ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n4 , ⟨ n3~n4 , ⟨ n1n3 , n2n4 ⟩ ⟩ ⟩ ⟩ 
  = ⟨ (m3 · n3) , ⟨ (m4 · n4) , ⟨ ([α-app] m3~m4 n3~n4) , ⟨ ([4] m1m3 n1n3) , ([4] m2m4 n2n4) ⟩ ⟩ ⟩ ⟩

==>-diamond ([4] m0m1 n0n1) ([7] {x} val2 m0λm2 n0v2) with ==>-diamond m0m1 m0λm2 
... | ⟨ ƛ x ⇒ m3 , ⟨ ƛ x ⇒ m4 , ⟨ [α-λ] m3~m4 , ⟨ m1m3 , [2] m2m4 ⟩ ⟩ ⟩ ⟩ with ==>-diamond n0n1 n0v2
... | ⟨ n3 , ⟨ v4 , ⟨ n3~v4 , ⟨ n1n3 , v2v4 ⟩ ⟩ ⟩ ⟩ 
  = ⟨ (m3 [ n3 / x ]β) , ⟨ (m4 [ v4 / x ]β) , ⟨ =α-β-subst m3~m4 n3~v4 , ⟨ [7] val3 m1m3 n1n3 , ==>-β-subst m2m4 v2v4 ⟩ ⟩ ⟩ ⟩
  where val3 = val-α-val (=α-symm n3~v4) (val-red-val v2v4 val2)

==>-diamond ([4] m0m1 n0n1) ([8] {β} {δ} new m0μc2 n0n2) with ==>-diamond m0m1 m0μc2
... | ⟨ μ α ⇒ c3 , ⟨ μ β ⇒ c4 , ⟨ [α-μ] ε∉c3 ε∉c4 c3~εc4 , ⟨ m1μc3 , [3] c2c4 ⟩ ⟩ ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n4 , ⟨ n3~n4 , ⟨ n1n3 , n2n4 ⟩ ⟩ ⟩ ⟩ with fresh ((μ α ⇒ c3) · n3)
... | ⟨ γ , δ∉αc3n3 ⟩
  = ⟨ μ γ ⇒ c3 [ n3 ∙ γ / α ]r' , ⟨ μ δ ⇒ c4 [ n4 ∙ δ / β ]r' , ⟨ =α-ρ-μr c3 c4 ε∉c3 ε∉c4 c3~εc4 n3~n4 , ⟨ [8] δ∉αc3n3 m1μc3 n1n3 , [3] (==>-μr-subst' c2c4 n2n4) ⟩ ⟩ ⟩ ⟩

==>-diamond ([4] m0m1 n0n1) ([9] {β} {δ} new val2 m0v2 n0μc2) with ==>-diamond m0m1 m0v2
... | ⟨ m3 , ⟨ v4 , ⟨ m3~v4 , ⟨ m1m3 , v2v4 ⟩ ⟩ ⟩ ⟩ with ==>-diamond n0n1 n0μc2
... | ⟨ μ α ⇒ c3 , ⟨ μ β ⇒ c4 , ⟨ [α-μ] ε∉c3 ε∉c4 c3~εc4 , ⟨ n1μc3 , [3] c2c4 ⟩ ⟩ ⟩ ⟩ with fresh (m3 · (μ α ⇒ c3))
... | ⟨ γ , δ∉αc3n3 ⟩
  = ⟨ (μ γ ⇒ c3 [ m3 ∙ γ / α ]l') , ⟨ (μ δ ⇒ c4 [ v4 ∙ δ / β ]l') , ⟨ (=α-ρ-μl c3 c4 ε∉c3 ε∉c4 c3~εc4 m3~v4) , ⟨ ([9] δ∉αc3n3 val3 m1m3 n1μc3) , [3] (==>-μl-subst' c2c4 v2v4) ⟩ ⟩ ⟩ ⟩
  where val3 = val-α-val (=α-symm m3~v4) (val-red-val v2v4 val2)


==>-diamond p0p1@([7] _ _ _) p0p2@([4] _ _) = reverse p0p1 p0p2

==>-diamond ([7] {x} val1 m0λm1 n0v1) ([7] val2 m0λm2 n0v2) with ==>-diamond m0λm1 m0λm2
... | ⟨ ƛ x ⇒ m3 , ⟨ ƛ x ⇒ m4 , ⟨ [α-λ] m3~m4 , ⟨ [2] m1m3 , [2] m2m4 ⟩ ⟩ ⟩ ⟩ with ==>-diamond n0v1 n0v2
... | ⟨ v3 , ⟨ v4 , ⟨ v3~v4 , ⟨ v1v3 , v2v4 ⟩ ⟩ ⟩ ⟩
  = ⟨ m3 [ v3 / x ]β , ⟨ m4 [ v4 / x ]β , ⟨ (=α-β-subst m3~m4 v3~v4) , ⟨ ==>-β-subst m1m3 v1v3 , ==>-β-subst m2m4 v2v4 ⟩ ⟩ ⟩ ⟩

==>-diamond ([7] _ m0λm1 _) ([8] _ m0μc2 _) with ==>-diamond m0λm1 m0μc2
... | ⟨ .(ƛ _ ⇒ _) , ⟨ .(μ _ ⇒ _) , ⟨ () , ⟨ [2] _ , [3] _ ⟩ ⟩ ⟩ ⟩

==>-diamond ([7] val1 _ n0v1) ([9] _ _ _ n0μc2) with ==>-diamond n0v1 n0μc2 
... | ⟨ .(μ _ ⇒ _) , ⟨ .(μ _ ⇒ _) , ⟨ [α-μ] _ _ _ , ⟨ v1μc3 , [3] _ ⟩ ⟩ ⟩ ⟩ with val-red-val v1μc3 val1
... | ()


==>-diamond p0p1@([8] _ _ _) p0p2@([4] _ _) = reverse p0p1 p0p2

==>-diamond p0p1@([8] _ _ _) p0p2@([7] _ _ _) = reverse p0p1 p0p2

==>-diamond ([8] {α} {γ} γ∉αc1n1 m0μc1 n0n1) ([8] {β} {δ} δ∉βc2n2 m0μc2 n0n2) with ==>-diamond m0μc1 m0μc2
... | ⟨ μ α ⇒ c3 , ⟨ μ β ⇒ c4 , ⟨ [α-μ] ε∉c3 ε∉c4 c3~εc4 , ⟨ [3] c1c3 , [3] c2c4 ⟩ ⟩ ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n4 , ⟨ n3~n4 , ⟨ n1n3 , n2n4 ⟩ ⟩ ⟩ ⟩
  = ⟨ μ γ ⇒ c3 [ n3 ∙ γ / α ]r' , ⟨ μ δ ⇒ c4 [ n4 ∙ δ / β ]r' , ⟨ =α-ρ-μr c3 c4 ε∉c3 ε∉c4 c3~εc4 n3~n4 , ⟨ [3] (==>-μr-subst' c1c3 n1n3) , [3] (==>-μr-subst' c2c4 n2n4) ⟩ ⟩ ⟩ ⟩

==>-diamond ([8] _ m0μc1 _) ([9] _ val2 m0v2 _) with ==>-diamond m0μc1 m0v2
... | ⟨ .(μ _ ⇒ _) , ⟨ .(μ _ ⇒ _) , ⟨ [α-μ] _ _ _ , ⟨ [3] _ , v2μc4 ⟩ ⟩ ⟩ ⟩ with val-red-val v2μc4 val2
... | ()


==>-diamond p0p1@([9] _ _ _ _) p0p2@([4] _ _) = reverse p0p1 p0p2

==>-diamond p0p1@([9] _ _ _ _) p0p2@([7] _ _ _) = reverse p0p1 p0p2

==>-diamond p0p1@([9] _ _ _ _) p0p2@([8] _ _ _) = reverse p0p1 p0p2

==>-diamond ([9] {α} {γ} γ∉v1αc1 val1 m0v1 n0μc1) ([9] {β} {δ} δ∉v2βc2 val2 m0v2 n0μc2) with ==>-diamond m0v1 m0v2
... | ⟨ v3 , ⟨ v4 , ⟨ v3~v4 , ⟨ v1v3 , v2v4 ⟩ ⟩ ⟩ ⟩ with ==>-diamond n0μc1 n0μc2
... | ⟨ μ α ⇒ c3 , ⟨ μ β ⇒ c4 , ⟨ [α-μ] ε∉c3 ε∉c4 c3~εc4 , ⟨ [3] c1c3 , [3] c2c4 ⟩ ⟩ ⟩ ⟩
  = ⟨ μ γ ⇒ c3 [ v3 ∙ γ / α ]l' , ⟨ μ δ ⇒ c4 [ v4 ∙ δ / β ]l' , ⟨ =α-ρ-μl c3 c4 ε∉c3 ε∉c4 c3~εc4 v3~v4 , ⟨ [3] (==>-μl-subst' c1c3 v1v3) , [3] (==>-μl-subst' c2c4 v2v4) ⟩ ⟩ ⟩ ⟩


==>-diamond' ([5] {α} m0m1) ([5] m0m2) with ==>-diamond m0m1 m0m2
... | ⟨ m3 , ⟨ m4 , ⟨ m3~m4 , ⟨ m1m3 , m2m4 ⟩ ⟩ ⟩ ⟩ 
  = ⟨ [ α ] m3 , ⟨ [ α ] m4 , ⟨ [α-name] m3~m4 , ⟨ [5] m1m3 , [5] m2m4 ⟩ ⟩ ⟩ ⟩

==>-diamond' ([5] {δ} m0m1) ([6] m0μc2) with ==>-diamond m0m1 m0μc2
... | ⟨ μ α ⇒ c3 , ⟨ μ β ⇒ c4 , ⟨ [α-μ] γ∉c3 γ∉c4 c3~γc4 , ⟨ m1μc3 , [3] c2c4 ⟩ ⟩ ⟩ ⟩
  = ⟨ c3 [ δ / α ]ρ' , ⟨ c4 [ δ / β ]ρ' , ⟨ =α-ρ-fresh c3 c4 γ∉c3 γ∉c4 c3~γc4 , ⟨ [6] m1μc3 , ==>-ρ-subst' c2c4 ⟩ ⟩ ⟩ ⟩


==>-diamond' p0p1@([6] _) p0p2@([5] _) = reverse' p0p1 p0p2

==>-diamond' ([6] {δ} {α} m0μc1) ([6] {δ'} {β} m0μc2) with ==>-diamond m0μc1 m0μc2
... | ⟨ μ α ⇒ c3 , ⟨ μ β ⇒ c4 , ⟨ [α-μ] γ∉c3 γ∉c4 c3~γc4 , ⟨ [3] c1c3 , [3] c2c4 ⟩ ⟩ ⟩ ⟩ 
  = ⟨ c3 [ δ / α ]ρ' , ⟨ c4 [ δ / β ]ρ' , ⟨ =α-ρ-fresh c3 c4 γ∉c3 γ∉c4 c3~γc4 , ⟨ ==>-ρ-subst' c1c3 , ==>-ρ-subst' c2c4 ⟩ ⟩ ⟩ ⟩

{-==>-diamond ([1] {x}) [1] = ⟨ (` x) , ⟨ [1] , [1] ⟩ ⟩


==>-diamond ([2] {x} m0m1) ([2] m0m2) with ==>-diamond m0m1 m0m2
...                              | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ = ⟨ ƛ x ⇒ m3 , ⟨ [2] m1m3 , [2] m2m3 ⟩ ⟩


==>-diamond ([3] {α} c0c1) ([3] c0c2) with ==>-diamond' c0c1 c0c2
...                              | ⟨ c3 , ⟨ c1c3 , c2c3 ⟩ ⟩ = ⟨ μ α ⇒ c3 , ⟨ [3] c1c3 , [3] c2c3 ⟩ ⟩


==>-diamond ([4] m0m1 n0n1) ([4] m0m2 n0n2) with ==>-diamond m0m1 m0m2
... | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ = ⟨ (m3 · n3) , ⟨ [4] m1m3 n1n3 , [4] m2m3 n2n3 ⟩ ⟩

==>-diamond ([4] m0m1 n0n1) ([7] {x} val m0λm2 n0v2) with ==>-diamond m0m1 m0λm2 
... | ⟨ ƛ x ⇒ m3 , ⟨ m1λm3 , [2] m2m3 ⟩ ⟩ with ==>-diamond n0n1 n0v2
... | ⟨ v3 , ⟨ n1v3 , v2v3 ⟩ ⟩ = ⟨ (m3 [ v3 / x ]β) , ⟨ [7] (val-red-val v2v3 val) m1λm3 n1v3 , β-subst-lemma m2m3 par-refl ⟩ ⟩

==>-diamond ([4] m0m1 n0n1) ([8] {α} {γ} m0μc2 n0n2) with ==>-diamond m0m1 m0μc2 
... | ⟨ μ α ⇒ c3 , ⟨ m1μc3 , [3] c2c3 ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ = ⟨ μ γ ⇒ c3 [ n3 ∙ γ / α ]r' , ⟨ [8] m1μc3 n1n3 , [3] (μr-subst-lemma' c2c3 n2n3) ⟩ ⟩

==>-diamond ([4] m0m1 n0n1) ([9] {α} {γ} val m0v2 n0μc2) with ==>-diamond m0m1 m0v2
... | ⟨ v3 , ⟨ m1v3 , v2v3 ⟩ ⟩ with ==>-diamond n0n1 n0μc2
... | ⟨ μ α ⇒ c3 , ⟨ n1μc3 , [3] c2c3 ⟩ ⟩ = ⟨ μ γ ⇒ c3 [ v3 ∙ γ / α ]l' , ⟨ [9] (val-red-val v2v3 val) m1v3 n1μc3 , [3] (μl-subst-lemma' c2c3 v2v3) ⟩ ⟩


==>-diamond ([7] val m0λm1 n0v1) ([4] m0m2 n0n2) with ==>-diamond m0λm1 m0m2
... | ⟨ ƛ x ⇒ m3 , ⟨ [2] m1m3 , m2λm3 ⟩ ⟩ with ==>-diamond n0v1 n0n2
... | ⟨ v3 , ⟨ v1v3 , n2v3 ⟩ ⟩ = ⟨ (m3 [ v3 / x ]β) , ⟨ β-subst-lemma m1m3 par-refl , [7] (val-red-val v1v3 val) m2λm3 n2v3 ⟩ ⟩

==>-diamond ([7] v_ m0λm1 n0v1) ([7] _ m0λm2 n0v2) with ==>-diamond m0λm1 m0λm2 
... | ⟨ ƛ x ⇒ m3 , ⟨ [2] m1m3 , [2] m2m3 ⟩ ⟩ with ==>-diamond n0v1 n0v2
... | ⟨ v3 , ⟨ v1v3 , v2v3 ⟩ ⟩ = ⟨ m3 [ v3 / x ]β , ⟨ β-subst-lemma m1m3 par-refl , β-subst-lemma m2m3 par-refl ⟩ ⟩

==>-diamond ([7] _ m0λm1 _) ([8] m0μc2 _) with ==>-diamond m0λm1 m0μc2
... | ⟨ .(ƛ _ ⇒ _) , ⟨ [2] _ , () ⟩ ⟩

==>-diamond ([7] val _ n0v1) ([9] _ _ n0μc2) with ==>-diamond n0v1 n0μc2 
... | ⟨ .(μ _ ⇒ _) , ⟨ v1μc3 , [3] _ ⟩ ⟩ with val-red-val v1μc3 val
... | ()


==>-diamond ([8] {α} {γ} m0μc1 n0n1) ([4] m0m2 n0n2) with ==>-diamond m0μc1 m0m2
... | ⟨ μ α ⇒ c3 , ⟨ [3] m1m3 , m2μc3 ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ = ⟨ μ γ ⇒ c3 [ n3 ∙ γ / α ]r' , ⟨ [3] (μr-subst-lemma' m1m3 n1n3) , [8] m2μc3 n2n3 ⟩ ⟩

==>-diamond ([8] m0μc1 _) ([7] _ m0λm2 _) with ==>-diamond m0μc1 m0λm2
... | ⟨ .(μ _ ⇒ _) , ⟨ [3] _ , () ⟩ ⟩

==>-diamond ([8] {α} {γ} m0μc1 n0n1) ([8] m0μc2 n0n2) with ==>-diamond m0μc1 m0μc2
... | ⟨ μ α ⇒ c3 , ⟨ [3] c1c3 , [3] c2c3 ⟩ ⟩ with ==>-diamond n0n1 n0n2
... | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ = ⟨ μ γ ⇒ c3 [ n3 ∙ γ / α ]r' , ⟨ [3] (μr-subst-lemma' c1c3 n1n3) , {!   !} ⟩ ⟩

==>-diamond ([8] m0μc1 _) ([9] val2 m0v2 _) with ==>-diamond m0μc1 m0v2
... | ⟨ .(μ _ ⇒ _) , ⟨ [3] _ , v2v3 ⟩ ⟩ with val-red-val v2v3 val2
... | ()


==>-diamond ([9] {α} {γ} val1 m0v1 n0μc1) ([4] m0m2 n0n2) with ==>-diamond m0v1 m0m2
... | ⟨ v3 , ⟨ v1v3 , m2v3 ⟩ ⟩ with ==>-diamond n0μc1 n0n2
... | ⟨ μ α ⇒ c3 , ⟨ [3] c1c3 , n2μc3 ⟩ ⟩ = ⟨ (μ γ ⇒ c3 [ v3 ∙ γ / α ]l') , ⟨ ([3] (μl-subst-lemma' c1c3 v1v3)) , [9] (val-red-val v1v3 val1) m2v3 n2μc3 ⟩ ⟩

==>-diamond ([9] _ _ n0μc1) ([7] val2 _ n0v2) with ==>-diamond n0μc1 n0v2
... | ⟨ .(μ _ ⇒ _) , ⟨ [3] _ , v2v3 ⟩ ⟩ with val-red-val v2v3 val2
... | ()

==>-diamond ([9] val1 m0v1 _) ([8] m0μc2 _) with ==>-diamond m0v1 m0μc2
... | ⟨ .(μ _ ⇒ _) , ⟨ v1v3 , [3] _ ⟩ ⟩ with val-red-val v1v3 val1 
... | ()

==>-diamond ([9] {α} {γ} val1 m0v1 n0μc1) ([9] val2 m0v2 n0μc2) with ==>-diamond m0v1 m0v2
... | ⟨ v3 , ⟨ v1v3 , v2v3 ⟩ ⟩ with ==>-diamond n0μc1 n0μc2
... | ⟨ μ α ⇒ c3 , ⟨ [3] c1c3 , [3] c2c3 ⟩ ⟩ = {!   !}


==>-diamond' ([5] {α} m0m1) ([5] m0m2) with ==>-diamond m0m1 m0m2
... | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ = ⟨ [ α ] m3 , ⟨ ([5] m1m3) , ([5] m2m3) ⟩ ⟩

==>-diamond' ([5] {α} m0m1) ([6] m0μc2) with ==>-diamond m0m1 m0μc2
... | ⟨ μ β ⇒ c3 , ⟨ m1μc3 , [3] c2c3 ⟩ ⟩ = ⟨ c3 [ α / β ]ρ' , ⟨ [6] m1μc3 , ρ-subst-lemma' c2c3 ⟩ ⟩

 
==>-diamond' ([6] m0μc1) ([5] {α} m0m2) with ==>-diamond m0μc1 m0m2 
... | ⟨ μ β ⇒ c3 , ⟨ [3] c1c3 , m2μc3 ⟩ ⟩ = ⟨ c3 [ α / β ]ρ' , ⟨ ρ-subst-lemma' c1c3 , [6] m2μc3 ⟩ ⟩
  
==>-diamond' ([6] {α} {β} m0μc1) ([6] m0μc2) with ==>-diamond m0μc1 m0μc2
... | ⟨ μ β ⇒ c3 , ⟨ [3] c1c3 , [3] c2c3 ⟩ ⟩ = ⟨ c3 [ α / β ]ρ' , ⟨ ρ-subst-lemma' c1c3 , ρ-subst-lemma' c2c3 ⟩ ⟩
-} 