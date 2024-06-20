module LConfluence where

open import LDefinitions
open import Data.Product using (∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)

-- The substitution lemmas
postulate 
  β-subst-lemma : ∀ {z : Id} {M N P Q : Term} 
    → M ==> N 
    → P ==> Q 
    ----------------
    → M [ P / z ]β ==> N [ Q / z ]β

  ρ-subst-lemma : ∀ {α β : Name} {M N : Term} 
    → M ==> N 
    ----------------
    → M [ α / β ]ρ ==> N [ α / β ]ρ

  -- The following two lemmas involve alpha conversion and are not provable with the given definition of ==> 
  μr-subst-lemma : ∀ {α γ δ : Name} {M N P Q : Term} 
    → M ==> N
    → P ==> Q
    → γ ∉ (μ α ⇒ M) · P
    → δ ∉ (μ α ⇒ N) · Q
    ----------------
    → μ γ ⇒ M [ P ∙ γ / α ]μr ==> μ δ ⇒ N [ Q ∙ δ / α ]μr
    
  μl-subst-lemma : ∀ {α γ δ : Name} {M N P Q : Term} 
    → M ==> N 
    → P ==> Q
    → γ ∉ P · (μ α ⇒ M) 
    → δ ∉ Q · (μ α ⇒ N) 
    ----------------
    → μ γ ⇒ M [ P ∙ γ / α ]μl ==> μ δ ⇒ N [ Q ∙ δ / α ]μl

  δr-subst-lemma : ∀ {α : Name} {M N P Q : Term} 
    → M ==> N 
    → P ==> Q 
    ----------------
    → M [ P / α ]δr ==> N [ Q / α ]δr

  δl-subst-lemma : ∀ {α : Name} {M N P Q : Term} 
    → M ==> N 
    → P ==> Q 
    ----------------
    → M [ P / α ]δl ==> N [ Q / α ]δl

-- Values only reduce to values
val-red-val : ∀ {V V' : Term} → V ==> V' → Value V → Value V'
val-red-val [1] Vx = Vx
val-red-val ([2] vv') Vƛ = Vƛ

-- If P0 ==> P1 and P0 ==> P2, there exists some P3 such that P1 ==> P3 and P2 ==> P3
{-# TERMINATING #-}
==>-diamond  : diamond _==>_

reverse  : diamond _==>_
reverse  p0p1 p0p2 with ==>-diamond p0p2 p0p1
...                   | ⟨ p3 , ⟨ p2p3 , p1p3 ⟩ ⟩ = ⟨ p3 , ⟨ p1p3 , p2p3 ⟩ ⟩

==>-diamond ([1] {x}) [1] 
  = ⟨ (` x) , ⟨ [1] , [1] ⟩ ⟩


==>-diamond ([2] {x} m0m1) ([2] m0m2) 
  with ==>-diamond m0m1 m0m2
...  | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ 
  = ⟨ ƛ x ⇒ m3 , ⟨ [2] m1m3 , [2] m2m3 ⟩ ⟩


==>-diamond ([3] {x} m0m1) ([3] m0m2) 
  with ==>-diamond m0m1 m0m2
...  | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ 
  = ⟨ ν x ⇒ m3 , ⟨ [3] m1m3 , [3] m2m3 ⟩ ⟩


==>-diamond ([4] {α} m0m1) ([4] m0m2) 
  with ==>-diamond m0m1 m0m2
...  | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ 
  = ⟨ μ α ⇒ m3 , ⟨ [4] m1m3 , [4] m2m3 ⟩ ⟩


==>-diamond ([5] m0m1 n0n1) ([5] m0m2 n0n2) 
  with ==>-diamond m0m1 m0m2
...  | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ 
    with ==>-diamond n0n1 n0n2
...    | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ 
  = ⟨ (m3 · n3) , ⟨ [5] m1m3 n1n3 , [5] m2m3 n2n3 ⟩ ⟩

==>-diamond ([5] m0m1 n0n1) ([9] {x} val m0λm2 n0v2)
  with ==>-diamond m0m1 m0λm2 
...  | ⟨ ƛ x ⇒ m3 , ⟨ m1λm3 , [2] m2m3 ⟩ ⟩ 
    with ==>-diamond n0n1 n0v2
...    | ⟨ v3 , ⟨ n1v3 , v2v3 ⟩ ⟩ 
  = ⟨ (m3 [ v3 / x ]β) , ⟨ [9] (val-red-val v2v3 val) m1λm3 n1v3 , β-subst-lemma m2m3 v2v3 ⟩ ⟩

==>-diamond ([5] m0m1 n0n1) ([11] {α} γ∉αm2n2 m0μm2 n0n2) 
  with ==>-diamond m0m1 m0μm2 
...  | ⟨ μ α ⇒ m3 , ⟨ m1μm3 , [4] m2m3 ⟩ ⟩ 
    with ==>-diamond n0n1 n0n2
...    | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ 
      with fresh ((μ α ⇒ m3) · n3)
...      | ⟨ δ , δ∉αm3n3 ⟩ 
  = ⟨ μ δ ⇒ m3 [ n3 ∙ δ / α ]μr , ⟨ [11] δ∉αm3n3 m1μm3 n1n3 , μr-subst-lemma m2m3 n2n3 γ∉αm2n2 δ∉αm3n3 ⟩ ⟩

==>-diamond ([5] m0m1 n0n1) ([12] {α} γ∉v2αn2 val m0v2 n0μn2) 
  with ==>-diamond m0m1 m0v2
...  | ⟨ v3 , ⟨ m1v3 , v2v3 ⟩ ⟩ 
    with ==>-diamond n0n1 n0μn2
...    | ⟨ μ α ⇒ n3 , ⟨ n1μn3 , [4] n2n3 ⟩ ⟩ 
      with fresh (v3 · (μ α ⇒ n3))
...      | ⟨ δ , δ∉v3αn3 ⟩ 
  = ⟨ μ δ ⇒ n3 [ v3 ∙ δ / α ]μl , ⟨ [12] δ∉v3αn3 (val-red-val v2v3 val) m1v3 n1μn3 , μl-subst-lemma n2n3 v2v3 γ∉v2αn2 δ∉v3αn3 ⟩ ⟩


==>-diamond ([6] m0m1 n0n1) ([6] m0m2 n0n2)
  with ==>-diamond m0m1 m0m2
...  | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ 
    with ==>-diamond n0n1 n0n2
...    | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ 
  = ⟨ ⁅ m3 ⁆ n3 , ⟨ [6] m1m3 n1n3 , [6] m2m3 n2n3 ⟩ ⟩ 

==>-diamond ([6] m0m1 n0n1) ([10] {x} val m0νm2 n0v2)
  with ==>-diamond m0m1 m0νm2 
...  | ⟨ ν x ⇒ m3 , ⟨ m1νm3 , [3] m2m3 ⟩ ⟩ 
    with ==>-diamond n0n1 n0v2
...    | ⟨ v3 , ⟨ n1v3 , v2v3 ⟩ ⟩ 
  = ⟨ m3 [ v3 / x ]β , ⟨ [10] (val-red-val v2v3 val) m1νm3 n1v3 , β-subst-lemma m2m3 v2v3 ⟩ ⟩

==>-diamond ([6] m0m1 n0n1) ([13] {α} m0μm2 n0n2) 
  with ==>-diamond m0m1 m0μm2
...  | ⟨ μ α ⇒ m3 , ⟨ m1μm3 , [4] m2m3 ⟩ ⟩ 
    with ==>-diamond n0n1 n0n2
...    | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ 
  = ⟨ m3 [ n3 / α ]δr , ⟨ [13] m1μm3 n1n3 , δr-subst-lemma m2m3 n2n3 ⟩ ⟩

==>-diamond ([6] m0m1 n0n1) ([14] {α} val m0v2 n0μn2) 
  with ==>-diamond m0m1 m0v2
...  | ⟨ v3 , ⟨ m1v3 , v2v3 ⟩ ⟩ 
    with ==>-diamond n0n1 n0μn2
...    | ⟨ μ α ⇒ n3 , ⟨ n1μn3 , [4] n2n3 ⟩ ⟩ 
  = ⟨ n3 [ v3 / α ]δl , ⟨ [14] (val-red-val v2v3 val) m1v3 n1μn3 , δl-subst-lemma n2n3 v2v3 ⟩ ⟩


==>-diamond ([7] {α} m0m1) ([7] m0m2) 
  with ==>-diamond m0m1 m0m2
...  | ⟨ m3 , ⟨ m1m3 , m2m3 ⟩ ⟩ 
  = ⟨ [ α ] m3 , ⟨ ([7] m1m3) , ([7] m2m3) ⟩ ⟩

==>-diamond ([7] {α} m0m1) ([8] m0μm2) 
  with ==>-diamond m0m1 m0μm2
...  | ⟨ μ β ⇒ m3 , ⟨ m1μm3 , [4] m2m3 ⟩ ⟩ 
  = ⟨ m3 [ α / β ]ρ , ⟨ [8] m1μm3 , ρ-subst-lemma m2m3 ⟩ ⟩


==>-diamond p0p1@([8] _) p0p2@([7] _) = reverse p0p1 p0p2

==>-diamond ([8] {α} {β} m0μm1) ([8] m0μm2) 
  with ==>-diamond m0μm1 m0μm2
...  | ⟨ μ β ⇒ m3 , ⟨ [4] m1m3 , [4] m2m3 ⟩ ⟩ 
  = ⟨ m3 [ α / β ]ρ , ⟨ ρ-subst-lemma m1m3 , ρ-subst-lemma m2m3 ⟩ ⟩


==>-diamond p0p1@([9] _ _ _) p0p2@([5] _ _) = reverse p0p1 p0p2

==>-diamond ([9] _ m0λm1 n0v1) ([9] _ m0λm2 n0v2) 
  with ==>-diamond m0λm1 m0λm2 
...  | ⟨ ƛ x ⇒ m3 , ⟨ [2] m1m3 , [2] m2m3 ⟩ ⟩ 
    with ==>-diamond n0v1 n0v2
...    | ⟨ v3 , ⟨ v1v3 , v2v3 ⟩ ⟩ 
  = ⟨ m3 [ v3 / x ]β , ⟨ β-subst-lemma m1m3 v1v3 , β-subst-lemma m2m3 v2v3 ⟩ ⟩

==>-diamond ([9] _ m0λm1 _) ([11] _ m0μm2 _) 
  with ==>-diamond m0λm1 m0μm2
...  | ⟨ .(ƛ _ ⇒ _) , ⟨ [2] _ , () ⟩ ⟩

==>-diamond ([9] val _ n0v1) ([12] _ _ _ n0μm2) 
  with ==>-diamond n0v1 n0μm2 
...  | ⟨ .(μ _ ⇒ _) , ⟨ v1μm3 , [4] _ ⟩ ⟩ 
    with val-red-val v1μm3 val
...    | ()


==>-diamond p0p1@([10] _ _ _) p0p2@([6] _ _) = reverse p0p1 p0p2

==>-diamond ([10] {x} _ m0νm1 n0v1) ([10] _ m0νm2 n0v2) 
  with ==>-diamond m0νm1 m0νm2
...  | ⟨ ν x ⇒ m3 , ⟨ [3] m1m3 , [3] m2m3 ⟩ ⟩
    with ==>-diamond n0v1 n0v2
...    | ⟨ v3 , ⟨ v1v3 , v2v3 ⟩ ⟩
  = ⟨ m3 [ v3 / x ]β , ⟨ β-subst-lemma m1m3 v1v3 , β-subst-lemma m2m3 v2v3 ⟩ ⟩

==>-diamond ([10] _ m0νm1 _) ([13] m0μm2 _)
  with ==>-diamond m0νm1 m0μm2
... | ⟨ .(ν _ ⇒ _) , ⟨ [3] _ , () ⟩ ⟩

==>-diamond ([10] val _ n0v1) ([14] _ _ n0μm2) 
  with ==>-diamond n0v1 n0μm2 
...  | ⟨ .(μ _ ⇒ _) , ⟨ v1μm3 , [4] _ ⟩ ⟩ 
    with val-red-val v1μm3 val
...    | ()


==>-diamond p0p1@([11] _ _ _) p0p2@([5] _ _) = reverse p0p1 p0p2

==>-diamond p0p1@([11] _ _ _) p0p2@([9] _ _ _) = reverse p0p1 p0p2

==>-diamond ([11] {α} γ∉αm1n1 m0μm1 n0n1) ([11] δ∉αm2n2 m0μm2 n0n2) 
  with ==>-diamond m0μm1 m0μm2
...  | ⟨ μ α ⇒ m3 , ⟨ [4] m1m3 , [4] m2m3 ⟩ ⟩ 
    with ==>-diamond n0n1 n0n2
...    | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩ 
      with fresh ((μ α ⇒ m3) · n3)
...      | ⟨ ε , ε∉αm3n3 ⟩ 
  = ⟨ μ ε ⇒ m3 [ n3 ∙ ε / α ]μr , ⟨ μr-subst-lemma m1m3 n1n3 γ∉αm1n1 ε∉αm3n3 , μr-subst-lemma m2m3 n2n3 δ∉αm2n2 ε∉αm3n3 ⟩ ⟩

==>-diamond ([11] _ m0μm1 _) ([12] _ val2 m0v2 _) 
  with ==>-diamond m0μm1 m0v2
...  | ⟨ .(μ _ ⇒ _) , ⟨ [4] _ , v2v3 ⟩ ⟩ 
    with val-red-val v2v3 val2
...    | ()


==>-diamond p0p1@([12] _ _ _ _) p0p2@([5] _ _) = reverse p0p1 p0p2

==>-diamond p0p1@([12] _ _ _ _) p0p2@([9] _ _ _) = reverse p0p1 p0p2

==>-diamond p0p1@([12] _ _ _ _) p0p2@([11] _ _ _) = reverse p0p1 p0p2

==>-diamond ([12] {α} γ∉v1αn1 val1 m0v1 n0μn1) ([12] δ∉v2αn2 val2 m0v2 n0μn2) 
  with ==>-diamond m0v1 m0v2
...  | ⟨ v3 , ⟨ v1v3 , v2v3 ⟩ ⟩ 
    with ==>-diamond n0μn1 n0μn2
...    | ⟨ μ α ⇒ n3 , ⟨ [4] n1n3 , [4] n2n3 ⟩ ⟩ 
      with fresh (v3 · (μ α ⇒ n3))
...      | ⟨ ε , ε∉v3αn3 ⟩ 
  = ⟨ μ ε ⇒ n3 [ v3 ∙ ε / α ]μl , ⟨ μl-subst-lemma n1n3 v1v3 γ∉v1αn1 ε∉v3αn3 , μl-subst-lemma n2n3 v2v3 δ∉v2αn2 ε∉v3αn3 ⟩ ⟩


==>-diamond p0p1@([13] _ _) p0p2@([6] _ _) = reverse p0p1 p0p2

==>-diamond p0p1@([13] _ _) p0p2@([10] _ _ _) = reverse p0p1 p0p2

==>-diamond ([13] {α} m0μm1 n0n1) ([13] m0μm2 n0n2)
  with ==>-diamond m0μm1 m0μm2
... | ⟨ μ α ⇒ m3 , ⟨ [4] m1m3 , [4] m2m3 ⟩ ⟩
    with ==>-diamond n0n1 n0n2
...    | ⟨ n3 , ⟨ n1n3 , n2n3 ⟩ ⟩
  = ⟨ m3 [ n3 / α ]δr , ⟨ δr-subst-lemma m1m3 n1n3 , δr-subst-lemma m2m3 n2n3 ⟩ ⟩

==>-diamond ([13] m0μm1 _) ([14] val2 m0v2 _) 
  with ==>-diamond m0μm1 m0v2
...  | ⟨ .(μ _ ⇒ _) , ⟨ [4] _ , v2v3 ⟩ ⟩ 
    with val-red-val v2v3 val2
...    | ()


==>-diamond p0p1@([14] _ _ _) p0p2@([6] _ _) = reverse p0p1 p0p2

==>-diamond p0p1@([14] _ _ _) p0p2@([10] _ _ _) = reverse p0p1 p0p2

==>-diamond p0p1@([14] _ _ _) p0p2@([13] _ _) = reverse p0p1 p0p2

==>-diamond ([14] {α} val1 m0v1 n0μn1) ([14] val2 m0v2 n0μn2) 
  with ==>-diamond m0v1 m0v2
...  | ⟨ v3 , ⟨ v1v3 , v2v3 ⟩ ⟩ 
    with ==>-diamond n0μn1 n0μn2
...    | ⟨ μ α ⇒ n3 , ⟨ [4] n1n3 , [4] n2n3 ⟩ ⟩ 
  = ⟨ n3 [ v3 / α ]δl , ⟨ δl-subst-lemma n1n3 v1v3 , δl-subst-lemma n2n3 v2v3 ⟩ ⟩


-- MAIN RESULT: ⟶ is confluent  
⟶-confluent : confluent _⟶_
⟶-confluent rewrite same-rtc = rtc-diamond _==>_ ==>-diamond 