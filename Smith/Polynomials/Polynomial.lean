/-
# Computable implementation of polyonomials with arrays

-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Tactic
import Smith.RangeCursor

namespace APolynomial

variable {F : Type} [Field F] [DecidableEq F]

def clean_zeros (A : Array F) : Array F :=
  if h : A.size = 0 then
    A else
  if A[A.size-1]'(by grind) = 0 then
    clean_zeros (A.pop)
  else
    A
termination_by A.size

lemma clean_zeros_prop (A : Array F) :
    clean_zeros A = #[] ∨ (clean_zeros A).getD ((clean_zeros A).size -1) 0 ≠ 0 := by
  suffices hsuf : ∀ n, n = A.size →
    (clean_zeros A = #[] ∨ (clean_zeros A).getD ((clean_zeros A).size -1) 0 ≠ 0)
  · apply hsuf (A.size)
    simp
  intro n
  revert A
  induction' n with n hn
  · intro A h
    rw  [eq_comm,Array.size_eq_zero_iff] at h
    left
    nth_rewrite 1 [h]
    simp [clean_zeros]
  · intro A hA
    by_cases hcas : A.size = 0
    · grind
    by_cases hcas2 : A.getD (A.size - 1) 0 = 0
    · unfold clean_zeros
      simp only [hcas, ↓reduceDIte, Array.getD_eq_getD_getElem?, ne_eq]
      have haux : A.getD (A.size -1) 0 = A[A.size -1]'(by omega)
      · exact Eq.symm (Array.getElem_eq_getD 0)
      rw [haux] at hcas2
      simp only [hcas2, ↓reduceIte]
      specialize hn A.pop ?_
      · simp
        omega
      simp only [Array.getD_eq_getD_getElem?, ne_eq] at hn
      exact hn
    · unfold clean_zeros
      rw  [← (Array.getElem_eq_getD 0)] at hcas2
      · simp only [hcas, ↓reduceDIte, hcas2, ↓reduceIte]
        right
        simp only [Array.getD, tsub_lt_self_iff, zero_lt_one, and_true,
          Array.getInternal_eq_getElem, ne_eq, dite_eq_right_iff, not_forall]
        fconstructor
        · omega
        · exact hcas2

 lemma clean_zeros_eq (A : Array F) (i : ℕ) : A.getD i 0 = (clean_zeros A).getD i 0 := by
  generalize hn : A.size = n
  revert hn A
  induction' n with n hind
  · unfold clean_zeros
    simp
  · intro A hA
    by_cases hcas : A[n]'(by omega) = 0
    · unfold clean_zeros
      simp only [ hA, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceDIte, add_tsub_cancel_right, hcas, ↓reduceIte]
      specialize hind A.pop ?_
      · simp [hA]
      by_cases hi : n ≤ i
      · rw [le_iff_lt_or_eq] at hi
        cases' hi  with hi hi
        · have haux : A.getD i 0 = 0
          · grind only
          rw [eq_comm,haux]
          grind
        · cases hi
          have haux : A.getD i 0 = 0
          · exact dite_eq_right_iff.mpr fun h ↦ hcas
          rw [haux,eq_comm]
          grind
      · simp at hi
        rw [← hind]
        have hi1 : i < A.size := by omega
        simp [hi1,Array.getD]
        grind
    · unfold clean_zeros
      simp [hA,hcas]

@[ext]
structure Poly (F : Type) [Field F] [DecidableEq F] : Type where
( Ar : Array F)
( hAr : Ar = #[] ∨ Ar.getD (Ar.size - 1) 0 ≠ 0)

def to_polynomial (A : Poly F) : Polynomial F := by
  fconstructor
  fconstructor
  · cases' A  with Ar hAr
    apply List.toFinset
    have L := [:Ar.size].toList.filter (fun i ↦ Ar.getD i 0 ≠ 0)
    exact L
  · intro i
    exact A.Ar.getD i 0
  · intro i
    simp
    grind

lemma def_to_polynomial (A : Poly F) (n : ℕ ) : (to_polynomial A).coeff n = A.Ar.getD n 0 := by
  simp [to_polynomial]

def from_polynomial (A : Polynomial F) : Poly F := by
  let d := A.degree
  have hd : A.degree = d := rfl
  match d with
  | none => exact {Ar := #[]
                   hAr := by simp}
  | some deg => exact {
      Ar := ([:deg + 1].toList.map A.coeff).toArray
      hAr := by
        have hA := Polynomial.coeff_ne_zero_of_eq_degree hd
        by_cases hcas : deg = 0
        · simp [hcas]
          cases hcas
          exact hA
        · simp [hcas]
          exact hA

  }


  lemma to_from_poly (A : Polynomial F) : to_polynomial (from_polynomial A) = A := by
    simp [to_polynomial,from_polynomial]
    ext n
    simp
    let d := A.degree
    have hd : A.degree = d := rfl
    split
    · expose_names
      rw [Polynomial.coeff_eq_zero_of_degree_lt]
      simp
      rw [heq]
      exact compareOfLessAndEq_eq_lt.mp rfl
    · expose_names
      simp_all
      by_cases hcas : n < deg + 1
      · simp [hcas]
      · simp [hcas]
        rw [Polynomial.coeff_eq_zero_of_degree_lt]
        simp_all
        rw [← hd_1]
        have haux : deg < n := by omega
        refine WithBot.lt_iff_exists.mpr ?_
        use n
        fconstructor
        · rfl
        · intro a ha
          cases ha
          exact haux

lemma from_to_poly (A : Poly F) : from_polynomial (to_polynomial A) = A := by
  simp [from_polynomial,to_polynomial]
  split
  · expose_names
    simp_all
    cases' A with Ar hAr
    simp_all
    unfold Polynomial.degree at hd_1
    simp_all
    cases' hAr with hAr hAr
    · cases hAr
      simp_all
    · have haux : (Ar.size -1 ) ∈ {x ∈ [:Ar.size].toList.toFinset | ¬Ar[x]?.getD 0 = 0}
      · simp
        fconstructor
        · grind
        · simp [Array.getD_getElem?]
          simp [Array.getD] at hAr
          exact hAr
      have haux2 := Finset.le_max haux
      rw [hd_1,WithBot.le_def] at haux2
      simp at haux2
      choose b hb1 hb2 using haux2
      cases hb2
  · expose_names
    cases' A with Ar hAr
    simp_all
    unfold Polynomial.degree at hd_1
    simp_all
    cases' hAr with hAr hAr
    · cases hAr
      simp_all
    · ext
      · simp_all
        apply le_antisymm
        · suffices hsuf : deg ∈ [:Ar.size].toList.toFinset
          · simp [Std.Range.toList] at hsuf
            omega
          have haux := Finset.mem_of_max hd_1
          simp at haux
          cases' haux with haux1 haux2
          simp [haux1]
        · have haux0 : Ar.size - 1 ∈ {x ∈ [:Ar.size].toList.toFinset | ¬Ar[x]?.getD 0 = 0}
          · simp
            fconstructor
            · grind
            · exact hAr
          have haux2 := Finset.le_max haux0
          rw [hd_1] at haux2
          cases' haux2
          omega
      · simp_all

lemma to_poly_inj : Function.Injective (to_polynomial : Poly F → Polynomial F):= by
  intro a b hab
  apply_fun from_polynomial at hab
  simp [from_to_poly] at hab
  exact hab

open Std.Do

def add_arrays (a b : Array F) : Array F := Id.run do
    let m := max a.size b.size
    let mut res := (Array.emptyWithCapacity m : Array F)
    for i in [:m] do
      res := res.push ((a.getD i 0) + (b.getD i 0))
    return (clean_zeros res)

lemma add_arrays_prop (a b : Array F) (i : ℕ) : (add_arrays a b).getD i 0 = a.getD i 0 + b.getD i 0 := by
  generalize h : add_arrays a b = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ =>  ⌜letMuts.size = xs.prefix.length ∧  ∀ c ∈ xs.prefix, letMuts.getD c 0 = a.getD c 0 + b.getD c 0⌝
  with mleave
  · expose_names
    fconstructor
    · grind
    · intro c hc
      simp at hc
      cases' h_2 with h2 h3
      cases' hc with hc hc
      · specialize h3 c hc
        have hc2 : c < b_1.size
        · grind
        simp
        rw [Array.getElem?_push_lt]
        simp at h3
        rw [← h3]
        grind
        exact hc2
      · have hc2 : c = b_1.size
        · grind
        simp [← hc,hc2]
  · grind
  · expose_names
    rw [← clean_zeros_eq]
    grind



def add (a b : Poly F) : Poly F where
  Ar := add_arrays a.Ar b.Ar
  hAr := by
    apply clean_zeros_prop

lemma add_prop (a b : Poly F) (i : ℕ) : (add a b).Ar.getD i 0 = a.Ar.getD i 0 + b.Ar.getD i 0 := by
  simp only [add,add_arrays_prop]

instance inst_Add : Add (Poly F) where
  add := add

lemma add_to_polynomial (a b : Poly F) : to_polynomial (a + b) = to_polynomial a + to_polynomial b := by
  ext n
  simp only [to_polynomial, ne_eq, decide_not, List.toFinset_filter,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Polynomial.coeff_ofFinsupp,
    Finsupp.coe_mk, Polynomial.coeff_add]
  apply add_prop


instance inst_Zero : Zero (Poly F) where
  zero := {
    Ar := #[]
    hAr := by left; rfl
  }

lemma def_zero : (0 : Poly F) = {
    Ar := #[]
    hAr := by left; rfl
    } := by rfl

lemma zero_to_polynomial : to_polynomial (0 : Poly F) = 0 := by
  ext n
  simp [to_polynomial]
  rfl

def mul_ar (a b : Array F) : Array F := Id.run do
    let s := a.size + b.size - 1
    let mut res := (Array.emptyWithCapacity s : Array F)
    for i in [:s+1] do
      let mut pres := (0 : F)
      for j in [:i+1] do
        pres := pres + (a.getD j 0) * (b.getD (i - j) 0)
      res := res.push pres
    return (clean_zeros res)

lemma def_mul (a b : Array F) (n : ℕ) : (mul_ar a b).getD n 0 = ∑ (i : Fin (n + 1)), (a.getD i 0) * (b.getD (n - i) 0) := by
  generalize h : mul_ar a b = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ =>
    ⌜letMuts.size = xs.prefix.length ∧  ∀ c ∈ xs.prefix, letMuts.getD c 0 = ∑ (i : Fin (c +1)), a.getD (↑i) 0 * b.getD (c - ↑i) 0⌝
  · ⇓⟨xs, letMuts⟩ => ⌜(letMuts = ∑ (j ∈ xs.prefix.toFinset), (a.getD j 0) * (b.getD (xs.prefix.length + xs.suffix.length - 1 - j) 0))⌝
  with mleave
  · expose_names
    rw [h_4]
    simp
    rw [Finset.sum_insert]
    · ring_nf
      simp
      left
      congr
      grind
    · rw [eq_comm] at h_3
      simp only [Std.Range.toList, tsub_zero, add_tsub_cancel_right, Nat.div_one, zero_add] at h_3
      have haux := RangeCursor.mem_preff 0 (cur +1) cur_1 pref_1 (cur_1 :: suff_1) h_3
      have haux2:= RangeCursor.mem_suff 0 (cur +1 ) cur_1 pref_1 (cur_1 :: suff_1) h_3
      simp at haux2
      intro hneg
      simp [haux] at hneg
      omega
  · expose_names
    fconstructor
    · grind
    · cases' h_2 with h2 h3
      intro c hc
      · simp at hc
        cases' hc with hc hc
        · specialize h3 c hc
          rw [← h3]
          have hc : c < b_1.size
          · rw [h2]
            grind
          simp
          rw [Array.getElem?_push_lt hc]
          simp
          grind
        · cases hc
          simp
          have haux : cur = b_1.size
          · grind
          simp [haux]
          simp [h_3,← haux]
          suffices hsuf : ∑ x ∈ [:cur+1].toList.toFinset, a[x]?.getD 0 * b[cur - x]?.getD 0 = ∑ x ∈ (Set.univ : Set (Fin (cur+1))), a[↑x]?.getD 0 * b[cur - ↑x]?.getD 0
          · simp_all
          by_cases hcas : cur = 0
          · cases hcas
            rw [← haux] at *
            simp [Std.Range.toList]
          rw [← Finset.sum_nbij']
          · intro a
            exact a.val
          · intro a
            exact if h : a < (cur+1) then ⟨a,h⟩ else ⟨0,by omega⟩
          · intro a ha
            simp
          · intro a ha
            simp
          · simp
          · intro a ha
            simp at ha
            simp [ha]
          · simp
  · expose_names
    simp [res_1]
  · expose_names
    rw [← clean_zeros_eq]
    cases' h_1 with h1 h2
    simp at h1
    by_cases hcas : n ≥ (s +1)
    · simp [hcas,h1]
      rw [Finset.sum_eq_zero]
      · intro x hx
        simp
        cases' x with x hx2
        have haux : x ≥ a.size ∨ (n - x) ≥ b.size
        · omega
        cases' haux with ha hb
        · simp [ha]
        · simp [hb]
    · simp at hcas h2
      specialize h2 n hcas
      simp [h2]

def mul (a b : Poly F) : Poly F where
  Ar := mul_ar a.Ar b.Ar
  hAr := by
    apply clean_zeros_prop


instance inst_mul : Mul (Poly F) where
  mul := mul

def M : Poly ℚ where
  Ar := #[1,0,3]
  hAr := by simp

#eval M * M

lemma def_mul' (a b : Poly F) (n : ℕ) : (a * b).Ar.getD n 0 = ∑ (i : Fin (n+1)), (a.Ar.getD i 0) * (b.Ar.getD (n - i) 0) := by
  have haux : (a*b).Ar = mul_ar a.Ar b.Ar := rfl
  rw [haux,def_mul]

lemma mul_to_polynomial (a b : Poly F) : to_polynomial (a * b) = to_polynomial a * to_polynomial b := by
  ext n
  rw [def_to_polynomial,def_mul']
  unfold to_polynomial
  simp [Polynomial.coeff_mul]
  by_cases hcas : n = 0
  · cases hcas
    simp
  rw [Finset.sum_nbij']
  · intro a
    exact ⟨a,n-a⟩
  · rintro ⟨a,b⟩
    exact if h : (a < (n + 1) ∧  a + b = n) then ⟨a,by omega⟩ else ⟨0,by omega⟩
  · simp
    intro a
    cases' a  with a ha
    simp
    omega
  · simp
  · simp
    grind
  · simp
    intro a b hab
    have haux : a < n + 1
    · omega
    simp [haux,hab]
    omega
  · simp

instance inst_one : One (Poly F) where
  one := {
    Ar := #[1]
    hAr := by simp
  }

lemma one_to_polynomial : to_polynomial (1 : Poly F) = 1 := by
  ext n
  simp only [to_polynomial,ne_eq, decide_not, List.toFinset_filter,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Polynomial.coeff_ofFinsupp,
    Finsupp.coe_mk]
  by_cases hn : n = 0
  · simp [hn]
    rfl
  · rw [Polynomial.coeff_eq_zero_of_degree_lt,Array.getD]
    · have haux : (1 : Poly F).Ar.size = 1
      · rfl
      simp [haux]
      intro h2
      omega
    · simp
      omega

def monomioar (n : ℕ) (c : F) : List F :=
  match n with
  | 0 => [c]
  | n + 1 => 0 :: monomioar n c

lemma def_monomioar {n : ℕ } {c : F} (i : ℕ): (monomioar n c).getD i 0 = if i = n then c else 0 := by
  revert i
  induction' n with n hind
  · simp [monomioar]
    intro i
    by_cases hcas: i = 0
    · simp [hcas]
    · simp [hcas]
  · intro i
    rw [monomioar]
    simp [List.getElem?_cons]
    split_ifs with h1 h2 h3
    · grind
    · simp
    · specialize hind (i - 1)
      split_ifs at hind with h4
      · exact hind
      · omega
    · specialize hind (i - 1)
      split_ifs at hind with h5
      · omega
      · grind

def monomio (n : ℕ) (c : F) : Poly F where
  Ar := if c = 0 then #[] else (monomioar n c).toArray
  hAr := by
    by_cases hc : c = 0
    · simp [hc]
    right
    simp
    have haux := @def_monomioar F _ _  n c ((monomioar n c).length - 1)
    simp at haux
    simp [hc,haux]
    clear haux
    induction' n with n hind
    · simp [monomioar]
    · unfold monomioar
      simp
      have haux : (monomioar n c).length > 0
      · unfold monomioar
        split
        · simp
        · simp
      omega

lemma monomio_zero (n : ℕ) : (monomio n (0 : F)) = 0 := by
  simp [monomio]
  rfl

lemma monomio_deg_zero (c : F) : monomio 0 c =
  { Ar := clean_zeros #[c]
    hAr := by
      unfold clean_zeros
      simp
      split_ifs with h1
      · left
        simp [clean_zeros]
      · right
        simp [h1]
  } := by
  ext
  · simp [monomio]
    split_ifs with h1
    · simp [h1,clean_zeros]
    · simp [monomioar,clean_zeros,h1]
  · expose_names
    simp [monomio]
    simp [clean_zeros,monomioar]

lemma def_monomio (n i : ℕ) (c : F) : (monomio n c).Ar.getD i 0 = if i = n then c else 0 := by
  simp [monomio]
  split_ifs with h1 h2 h3
  · simp_all
  · simp
  · have haux := @def_monomioar _ _ _ n c i
    simp at haux
    simp [ List.getElem?_toArray,haux]
    tauto
  · have haux := @def_monomioar _ _ _ n c i
    simp [h3] at haux
    simp [ List.getElem?_toArray,haux]

def shift_mul (P : Poly F) (n : ℕ ) (c : F) : Poly F where
  Ar := Id.run do
    if hn : (c = 0 ∨ P.Ar = #[]) then #[] else
    let mut res := (Array.emptyWithCapacity (P.Ar.size + n)  : Array F)
    for h : i in [:n] do
      res := res.push 0
    for h : i in P.Ar do
      res := res.push (c * i)
    return res
  hAr := by
    split_ifs with h1
    · left
      rfl
    · right
      simp
      rw [Array.getElem?_append]
      split_ifs with h2
      · simp at h2
        have haux2 : P.Ar.size = 0
        · omega
        simp at haux2
        tauto
      · have haux := P.hAr
        simp only [Array.size_replicate]
        intro hneg
        simp at h1
        simp [h1.2] at haux
        apply haux
        have hn : n + P.Ar.size - 1 - n = P.Ar.size - 1
        · have hP : P.Ar.size ≠ 0
          · simp [h1]
          omega
        rw [hn] at hneg
        grind

lemma mul_monom_eq_shift_mul (P : Poly F) (n : ℕ) (c : F) : P * monomio n c = shift_mul P n c := by
  unfold monomio shift_mul
  split_ifs with h1
  · simp [h1]
    apply to_poly_inj
    rw [mul_to_polynomial]
    rw [← def_zero,zero_to_polynomial]
    simp
    rw [← zero_to_polynomial,def_zero]
    congr
  · simp [h1]
    by_cases hcas : P = 0
    · simp [hcas]
      apply to_poly_inj
      simp [mul_to_polynomial,zero_to_polynomial]
      simp [def_zero,←zero_to_polynomial]
      congr
    · have haux : P.Ar ≠ #[]
      · simp [def_zero] at hcas
        intro hneg
        apply hcas
        ext
        simp [hneg]
        simp_all
      simp [haux]
      unfold monomioar










instance inst_ring : Ring (Poly F) where
  add_assoc := by
    intro a b c
    apply_fun to_polynomial
    simp [add_to_polynomial]
    ring
    exact to_poly_inj
  zero_add := by
    intro a
    apply to_poly_inj
    simp [add_to_polynomial,zero_to_polynomial]
  add_zero := by
    intro a
    apply to_poly_inj
    simp [add_to_polynomial,zero_to_polynomial]
  nsmul := fun  n p => (monomio 1 (n : F)) * p
  nsmul_zero := by
    intro x
    simp [monomio_zero]
    apply to_poly_inj
    rw [mul_to_polynomial,zero_to_polynomial,zero_mul]
  nsmul_succ := by
    intro n
    suffices hsuf :
      monomio 1 (n + 1 : F) = (monomio 1 (n : F)) + (1 : Poly F)
      · intro x
        rw [hsuf]

    intro p
    apply to_poly_inj
    rw [mul_to_polynomial,add_to_polynomial]
  add_comm := _
  mul := _
  left_distrib := _
  right_distrib := _
  zero_mul := _
  mul_zero := _
  mul_assoc := _
  one := _
  one_mul := _
  mul_one := _
  natCast := _
  natCast_zero := _
  natCast_succ := _
  npow := _
  npow_zero := _
  npow_succ := _
  neg := _
  sub := _
  sub_eq_add_neg := _
  zsmul := _
  zsmul_zero' := _
  zsmul_succ' := _
  zsmul_neg' := _
  neg_add_cancel := _
  intCast := _
  intCast_ofNat := _
  intCast_negSucc := _


end APolynomial
