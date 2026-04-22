/-
# Array related functions for Polynomials

This file contains functions related to arrays of field elements, to be used by polynomials.
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic
import Smith.RangeCursor

namespace APolynomial

open Array Std.Do

variable {F : Type} [Field F] [DecidableEq F]

def clean_zeros (A : Array F) : Array F :=
  if h : A.size = 0 then
    A else
  if A[A.size-1]'(by grind) = 0 then
    clean_zeros (A.pop)
  else
    A
termination_by A.size

lemma clean_zeros_size (A : Array F) (hA : A.getD (A.size - 1) 0 ≠ 0) : clean_zeros A = A := by
  unfold clean_zeros
  simp_all only [getD_eq_getD_getElem?, ne_eq, size_eq_zero_iff]
  split_ifs with h1 h2
  · tauto
  · exfalso
    apply hA
    have haux : A.size -1 < A.size
    · grind
    simp [haux,h2]
  · rfl

lemma clean_zeros_size_le (A : Array F) : (clean_zeros A).size ≤ A.size := by
  generalize hn : A.size = n
  revert A
  induction' n with n hind
  · unfold clean_zeros
    simp
  · intro A hA
    unfold clean_zeros
    simp [hA]
    split_ifs with h1
    · specialize hind A.pop
      simp [hA] at hind
      omega
    · omega

lemma clean_zeros_size_lt (A : Array F) (hs : A.size > 0) (hA : A[A.size - 1]'(by omega) = 0) :
    (clean_zeros A).size < A.size := by
  unfold clean_zeros
  split_ifs with h1
  · omega
  · have haux := clean_zeros_size_le A.pop
    simp at haux
    omega

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
    rw  [eq_comm,size_eq_zero_iff] at h
    left
    nth_rewrite 1 [h]
    simp [clean_zeros]
  · intro A hA
    by_cases hcas : A.size = 0
    · grind
    by_cases hcas2 : A.getD (A.size - 1) 0 = 0
    · unfold clean_zeros
      simp only [hcas, ↓reduceDIte, getD_eq_getD_getElem?, ne_eq]
      have haux : A.getD (A.size -1) 0 = A[A.size -1]'(by omega)
      · exact Eq.symm (getElem_eq_getD 0)
      rw [haux] at hcas2
      simp only [hcas2, ↓reduceIte]
      specialize hn A.pop ?_
      · simp
        omega
      simp only [getD_eq_getD_getElem?, ne_eq] at hn
      exact hn
    · unfold clean_zeros
      rw  [← (getElem_eq_getD 0)] at hcas2
      · simp only [hcas, ↓reduceDIte, hcas2, ↓reduceIte]
        right
        simp only [getD, tsub_lt_self_iff, zero_lt_one, and_true,
          getInternal_eq_getElem, ne_eq, dite_eq_right_iff, not_forall]
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
        simp [hi1,getD]
        grind
    · unfold clean_zeros
      simp [hA,hcas]

lemma clean_zeros_size_lt' (A : Array F) (n : ℕ) (hn : 0 < n) (h : ∀ i ≥ (n - 1), A.getD i 0 = 0):
    (clean_zeros A).size < n := by
  by_contra hcon
  simp at hcon
  have haux := clean_zeros_prop A
  cases' haux with h1 h2
  · grind
  · specialize h ((clean_zeros A).size  -1) ?_
    · omega
    · apply h2
      rw [← clean_zeros_eq,h]

@[simp]
lemma getD_replicate_append (i n : ℕ) (A : Array F) :
    getD ((replicate n 0) ++ A) i 0  = if i < n then 0 else A.getD (i - n) 0 := by
  by_cases hcas : i < n
  · simp [hcas]
    rw [getElem?_append_left,getElem?_replicate]
    · simp [hcas]
    · rw [size_replicate]
      exact hcas
  · simp [hcas]
    rw [getElem?_append_right,size_replicate]
    rw [size_replicate]
    omega

@[simp]
lemma getD_replicate_append' (i n : ℕ) (A : Array F) :
    getD ((replicate (n + 1) 0) ++ A) i 0  = if i < n then 0 else if n = i then 0 else A.getD (i - (n + 1)) 0 := by
  simp
  split_ifs with h1 h2
  · rw [getElem?_append_left,getElem?_replicate]
    · have haux : i < n + 1 := by omega
      simp [haux]
    · rw [size_replicate]
      omega
  · cases h2
    rw [getElem?_append_left]
    · grind
    · grind
  · rw [getElem?_append_right]
    · simp
    · simp
      omega

@[simp]
lemma getD_replicate_pop_append (i n : ℕ) (c : F) (A : Array F) :
    getD (((replicate n 0).push c) ++ A) i 0  = if i < n then 0 else if i = n then c else A.getD (i - n - 1) 0 := by
  rw [push_eq_append,append_assoc,getD_replicate_append]
  split_ifs with h1 h2
  · rfl
  · simp [h2]
  · simp
    rw [getElem?_append_right]
    · simp
    · simp
      omega

@[simp]
lemma getD_replicate_push (i n : ℕ) (c : F):
    getD ((replicate n 0).push c) i 0 = if i = (n) then c else 0 := by
  rw [push_eq_append,getD_replicate_append]
  split_ifs with h1 h2 h3
  · omega
  · rfl
  · simp [h3]
  · grind

@[simp]
lemma getD_replicate_zero (i n : ℕ) : (replicate n (0 : F))[i]?.getD 0 = 0 := by
  grind

def add_arrays (a b : Array F) : Array F := Id.run do
    let m := max a.size b.size
    let mut res := (Array.emptyWithCapacity m : Array F)
    for i in [:m] do
      res := res.push ((a.getD i 0) + (b.getD i 0))
    return res

lemma add_arrays_size (a b : Array F) : (add_arrays a b).size = max a.size b.size := by
  simp [add_arrays]

lemma add_arrays_prop (a b : Array F) (i : ℕ) :
    (add_arrays a b).getD i 0 = a.getD i 0 + b.getD i 0 := by
  generalize h : add_arrays a b = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ =>  ⌜letMuts.size = xs.prefix.length ∧
      ∀ c ∈ xs.prefix, letMuts.getD c 0 = a.getD c 0 + b.getD c 0⌝
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
  · grind

def sub_array (a b : Array F) : Array F := Id.run do
    let m := max a.size b.size
    let mut res := (Array.emptyWithCapacity m : Array F)
    for i in [:m] do
      res := res.push ((a.getD i 0) - (b.getD i 0))
    return (clean_zeros res)

lemma sub_arrays_prop (a b : Array F) (i : ℕ) :
    (sub_array a b).getD i 0 = a.getD i 0 - b.getD i 0 := by
  generalize h : sub_array a b = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ =>  ⌜letMuts.size = xs.prefix.length ∧
      ∀ c ∈ xs.prefix, letMuts.getD c 0 = a.getD c 0 - b.getD c 0⌝
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


def mul_ar (a b : Array F) : Array F := Id.run do
    let s := a.size + b.size - 1
    let mut res := (Array.emptyWithCapacity (s) : Array F)
    for i in [:s] do
      let mut pres := (0 : F)
      for j in [:i+1] do
        pres := pres + (a.getD j 0) * (b.getD (i - j) 0)
      res := res.push pres
    return res


lemma def_mul (a b : Array F) (n : ℕ) :
    (mul_ar a b).getD n 0 = ∑ (i : Fin (n + 1)), (a.getD i 0) * (b.getD (n - i) 0) := by
  generalize h : mul_ar a b = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ =>
    ⌜letMuts.size = xs.prefix.length ∧
      ∀ c ∈ xs.prefix, letMuts.getD c 0 = ∑ (i : Fin (c +1)), a.getD (↑i) 0 * b.getD (c - ↑i) 0⌝
  · ⇓⟨xs, letMuts⟩ => ⌜(letMuts = ∑ (j ∈ xs.prefix.toFinset), (a.getD j 0) *
        (b.getD (xs.prefix.length + xs.suffix.length - 1 - j) 0))⌝
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
          suffices hsuf : ∑ x ∈ [:cur+1].toList.toFinset, a[x]?.getD 0 * b[cur - x]?.getD 0 =
              ∑ x ∈ (Set.univ : Set (Fin (cur+1))), a[↑x]?.getD 0 * b[cur - ↑x]?.getD 0
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
    -- rw [← clean_zeros_eq]
    cases' h_1 with h1 h2
    simp at h1
    by_cases hcas : n ≥ (s )
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


lemma mul_ar_len (a b : Array F) :
    (mul_ar a b).size = a.size + b.size - 1 := by
  simp [mul_ar]

/-
  have haux := def_mul a b (a.size + b.size - 1 - 1)
  unfold mul_ar
  simp
  rw [clean_zeros_size]
  · simp only [List.size_toArray, List.length_append, List.length_map, List.length_range', List.length_cons]
  · rw [clean_zeros_eq]
    simp [mul_ar] at haux
    simp [haux]
    have haux : (fun (x : Fin (a.size + b.size - 1 - 1 + 1)) =>
                  a[x.1]?.getD 0 * b[a.size + b.size - 1 - 1 - x.1]?.getD 0 ) =
                 fun (x : Fin (a.size + b.size - 1 - 1 + 1)) =>
                    if x.1 = a.size - 1 then a[a.size - 1]?.getD 0 *
                      b[a.size + b.size - 1 - 1 - (a.size -1)]?.getD 0 else 0
    · ext x
      split_ifs with hx
      · simp [hx]
      · by_cases hcas : x ≥ a.size
        · simp [hcas]
        · have hb : a.size + b.size - 1 - 1 - ↑x ≥ b.size
          · have hx2 := x.2
            omega
          simp [hb]
    rw [haux,Finset.sum_ite]
    simp
    have hcard : ({x | ↑x = a.size - 1} : Finset (Fin (a.size + b.size - 1 - 1 + 1))).card  = 1
    · rw [Finset.card_eq_one]
      fconstructor
      · fconstructor
        · exact a.size -1
        · suffices hsuf : b.size ≠ 0
          · omega
          grind
      · grind
    rw [hcard]
    simp
    fconstructor
    · simp at ha
      exact ha
    · suffices hsuf : a.size + b.size - 1 - 1 - (a.size - 1) = b.size -1
      · rw [hsuf]
        simp at hb
        exact hb
      · suffices hsuf : a.size ≠ 0 ∧ b.size ≠ 0
        · grind
        grind
-/


def monomioar (n : ℕ) (c : F) : List F :=
  match n with
  | 0 => [c]
  | n + 1 => 0 :: monomioar n c

lemma def_monomioar {n : ℕ } {c : F} (i : ℕ) :
    (monomioar n c).getD i 0 = if i = n then c else 0 := by
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

def sub_displaced_array (A B : Array F) (hB : B.size > 0)
  (i : ℕ) (hi : i < A.size - B.size - 1) (c : F) :
      Array F := Id.run do
  let mut res : {Ar : Array F // Ar.size = A.size}:= ⟨A,by rfl⟩
  for hj : j in [:B.size - 1] do
    have hres : j + i < res.1.size := by simp at hj; omega
    res := ⟨res.1.set (j + i) (res.1.getD (j + i ) 0  - c * B.getD (j) 0),  by grind⟩
  return res


@[inline]
def rem_quot_aux (A B : Array F) (i : ℕ) (hi : A.size - i ≥ B.size) (hB : B.size > 0) (c : F):
    Array F := Id.run do
  let mut res : { Ar : Array F // Ar.size = A.size}:= ⟨A,rfl⟩
  for hj :  j in [:B.size] do
    have hres : i + j < res.1.size := by simp at hj; have haux := res.2; omega;
    res := ⟨res.1.set (i + j) ((res.1.getD (i + j) 0) - (B.getD j 0) * c), by grind⟩
  return res.1

lemma rem_quot_aux_eq (A B : Array F ) (i : ℕ) (hi : A.size - i ≥ B.size) (hB : B.size > 0) (c : F)
  (j : ℕ) (hj : j ≥ B.size + i) :
    (rem_quot_aux A B i hi hB c).getD j 0 = A.getD j 0 := by
  generalize h : rem_quot_aux A B i hi hB c = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ => ⌜(letMuts.1).getD j 0 = A.getD j 0⌝
  with mleave
  · expose_names
    unfold res_1
    rw [← h_2]
    simp
    rw [getElem?_set_ne]
    grind

lemma rem_quot_aux_eq' (A B : Array F ) (i : ℕ) (hi : A.size - i ≥ B.size) (hB : B.size > 0) (c : F)
  (j : ℕ) (hj : j < i) :
    (rem_quot_aux A B i hi hB c).getD j 0 = A.getD j 0 := by
  generalize h : rem_quot_aux A B i hi hB c = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ => ⌜(letMuts.1).getD j 0 = A.getD j 0⌝
  with mleave
  · expose_names
    unfold res_1
    rw [← h_2]
    simp
    rw [getElem?_set_ne]
    grind

lemma rem_quot_aux_val (A B : Array F ) (i : ℕ) (hi : A.size - i ≥ B.size) (hB : B.size > 0) (c : F)
  (j : ℕ ) (hj : j ≥ i) (hj2 : j < B.size + i) :
    (rem_quot_aux A B i hi hB c).getD j 0 = A.getD j 0 - c * (B.getD (j - i) 0) := by
  generalize h : rem_quot_aux A B i hi hB c = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ => ⌜(∀ k ∈ xs.prefix, (letMuts.1).getD (k + i) 0 = A.getD (k + i) 0 - c * (B.getD (k) 0)) ∧ ∀ k ∈ xs.suffix, (letMuts.1.getD (k + i) 0) = A.getD (k + i) 0⌝
  with mleave
  any_goals grind
  · expose_names
    unfold res_1
    simp_all
    cases' h_2 with h2 h3
    cases' h3 with h3 h4
    fconstructor
    · intro k hk
      cases' hk with hk hk
      · specialize h2 k hk
        rw [getElem?_set_ne]
        · exact h2
        · grind
      · cases hk
        rw [getElem?_set]
        grind
    · intro k hk
      specialize h4 k hk
      rw [getElem?_set_ne,h4]
      grind

lemma rem_quot_aux_size (A B : Array F) (i : ℕ) (hi : A.size - i ≥ B.size) (hB : B.size > 0) (c : F):
    (rem_quot_aux A B i hi hB c).size = A.size := by
  generalize h : rem_quot_aux A B i hi hB c = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ =>  ⌜letMuts.1.size = A.size⌝
  with grind

lemma rem_quot_aux_prop (A B : Array F) (i : ℕ) (hi : A.size - i ≥ B.size) (hB : B.size > 0) (c : F) :
    A = add_arrays (mul_ar B ((replicate i 0).push c)) (rem_quot_aux A B i hi hB c) := by
  ext j hi1 hi2
  · rw [add_arrays_size,mul_ar_len,rem_quot_aux_size]
    simp
    omega
  · rw [getElem_eq_getD 0,getElem_eq_getD 0]
    rw [add_arrays_prop,def_mul]
    by_cases hcas : i ≤ j
    · have haux : (fun (i_1 : Fin (j + 1)) ↦ B.getD (↑i_1) 0 * ((replicate i 0).push c).getD (j - ↑i_1) 0) =
        fun (i_1  : Fin (j + 1)) ↦  if (↑i_1 = j - i) then ((B.getD (↑i_1) 0) * c) else 0
      · ext l
        rw [getD_replicate_push]
        simp
        split_ifs with h1 h2 h3
        · rfl
        · omega
        · omega
        · rfl
      rw [haux]
      simp [Finset.sum_ite]
      rw [Finset.sum_filter]
      have haux3 : ∀ (x : Fin (j + 1)), x = ⟨j - i, by omega⟩  ↔ ↑x = j - i
      · grind
      simp [← haux3]
      simp only [← getD_eq_getD_getElem?]
      by_cases hcas2 : j - i < B.size
      · rw [rem_quot_aux_val]
        · ring_nf
        · omega
        · omega
      · rw [rem_quot_aux_eq]
        · simp [hcas2]
        · omega
    · have haux : (fun (i_1 : Fin (j + 1)) ↦ B.getD (↑i_1) 0 * ((replicate i 0).push c).getD (j - ↑i_1) 0) =
        fun (i_1  : Fin (j + 1)) ↦  0
      . ext x
        rw [getD_replicate_push]
        split_ifs with h1
        · grind
        · simp
      rw [haux]
      simp only [Finset.sum_const_zero, zero_add]
      rw [rem_quot_aux_eq']
      omega


lemma rem_quot_aux_zero (A B : Array F ) (i : ℕ) (hi : A.size - i ≥ B.size) (hB : B.size > 0) (hB0 : B.getD (B.size -1) 0 ≠ 0) :
    (rem_quot_aux A B i hi hB ((A.getD (i + B.size -1) 0) / (B.getD (B.size - 1) 0))).getD (B.size -1 + i)  0 = 0  := by
  rw [rem_quot_aux_val]
  · simp only [add_tsub_cancel_right]
    rw [div_mul_comm,div_self,one_mul,sub_eq_zero_of_eq]
    · congr
      omega
    · exact hB0
  · omega
  · omega

def rem_quot_array (A B : Array F) (hB : B.size > 0) : Array F × Array F := Id.run do
  let sdif := A.size + 1 - B.size
  let mut rem : {Ar : Array F // Ar.size = A.size}:= ⟨A,rfl⟩
  let mut quot := emptyWithCapacity sdif
  for hi : i in [:sdif] do
    if rem.1.getD (rem.1.size - 1 - i) 0 ≠ 0 then
      let q := rem.1.getD (rem.1.size -1- i) 0 / B.getD (B.size - 1) 0
      rem := ⟨rem_quot_aux rem.1 B (sdif - 1 - i) (by simp_all; grind [rem.2]) hB q, by rw [rem_quot_aux_size,rem.2]⟩
      quot := quot.push q
    else
      quot := quot.push 0
  return (rem.1,quot.reverse)

lemma rem_quot_array_zeros (A B : Array F) (hB : B.size > 0) (hB2 : B.getD (B.size -1) 0 ≠ 0) (i : ℕ) (hi : i ≥ B.size) :
    (rem_quot_array A B hB).1.getD i 0 = 0 := by
  generalize h : rem_quot_array A B hB = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ =>
    ⌜(letMuts.2.1.size = A.size) ∧ ((hxs : 0 < xs.suffix.length) → ∀ k > (A.size - 1 - xs.current), letMuts.2.1.getD (k) 0 = 0) ∧ (xs.suffix = [] → letMuts.2.1.getD i 0 = 0)⌝
  with mleave
  · expose_names
    cases' h_3 with h3 h4
    cases' h4 with h4 h5
    fconstructor
    · unfold rem_2
      rw [rem_quot_aux_size]
      exact h3
    fconstructor
    · unfold rem_2 q sdif rem_1 at *
      simp_all
      intro hxs k hk
      by_cases hcas : k > (A.size -1 - cur)
      · by_cases hcas2 : k < A.size + 1 - B.size - 1 - cur
        · rw [← Array.getD_eq_getD_getElem?, rem_quot_aux_eq']
          · specialize h4 k hcas
            simp [h4]
          · exact hcas2
        · simp at hcas2
          rw [← Array.getD_eq_getD_getElem?, rem_quot_aux_eq]
          · specialize h4 k hcas
            simp [h4]
          · grind
      · simp at hcas
        have haux : suff[0] = cur + 1
        · exact RangeCursor.cur_suf0' h_1 hxs
        rw [haux] at hk
        have haux2 : k = A.size -1 -cur
        · omega
        rw [haux2]
        have haux3 : cur < A.size + 1 - B.size
        · grind
        rw [← Array.getD_eq_getD_getElem?, rem_quot_aux_val]
        · simp
          rw [div_mul_eq_mul_div,sub_div',div_eq_zero_iff]
          · left
            have haux4 : A.size - 1 - cur - (A.size + 1 - B.size - 1 - cur) = B.size -1
            · omega
            simp [haux4]
            grind
          · exact hB2
        · omega
        · omega
    · intro hsuf
      unfold rem_2 q sdif rem_1 at *
      simp_all
      specialize h4 i ?_
      · have hcur : cur = A.size +1 -B.size -1
        · grind
        omega
      rw [← getD_eq_getD_getElem?,rem_quot_aux_eq]
      · simp [h4]
      · have hcur : cur = A.size +1 -B.size -1
        · grind
        omega
  · expose_names
    cases' h_3 with h3 h4
    fconstructor
    · exact h3
    fconstructor
    · unfold sdif rem_1 at *
      simp_all
      intro hxs k hk
      by_cases hcas : k > (A.size -1 - cur)
      · rw [← Array.getD_eq_getD_getElem?]
        specialize h4 k hcas
        simp [h4]
      · simp at hcas
        have haux : suff[0] = cur + 1
        · exact RangeCursor.cur_suf0' h_1 hxs
        rw [haux] at hk
        have haux2 : k = A.size -1 -cur
        · omega
        rw [haux2]
        exact h_2
    · intro hs
      simp at h4
      specialize h4 i ?_
      · grind
      simp [rem_1,h4]
  · expose_names
    simp [rem]
    fconstructor
    · intro h2 k hk
      grind
    · grind
  · expose_names
    apply h_1.2.2

lemma rem_quot_array_prop (A B : Array F) (hB : B.size > 0) (hB2 : B.getD (B.size -1) 0 ≠ 0) (hA : A.getD (A.size -1) 0 ≠ 0) (hAB : A.size ≥ B.size):
    A = add_arrays (mul_ar B (rem_quot_array A B hB).2) (rem_quot_array A B hB).1 := by
  generalize h : (rem_quot_array A B hB) = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ =>
    ⌜(letMuts.1.size = xs.prefix.length) ∧ (A = add_arrays (mul_ar B ((replicate xs.suffix.length 0) ++ letMuts.1.reverse)) (letMuts).2.1) ∧ ((hl : letMuts.1.size > 0) → letMuts.1[0]'(hl) ≠ 0)⌝
  with mleave
  · expose_names
    simp [quot_2,rem_2,quot_1,rem_1] at *
    cases' h_3 with h3 h4
    cases' h4 with h4 h5
    fconstructor
    · exact h3
    fconstructor
    · ext i hi1 hi2
      · simp [h4,add_arrays_size,rem_quot_aux_size,mul_ar_len]
      · have haux := rem_quot_aux_prop (↑b.snd) B (sdif - 1 - cur) (by grind) hB q
        rw [haux] at h4
        simp only [h4]
        rw [getElem_eq_getD 0,getElem_eq_getD 0,add_arrays_prop,add_arrays_prop,add_arrays_prop]
        rw [def_mul,def_mul,def_mul]
        simp only [getD_replicate_push,getD_replicate_pop_append,getD_replicate_append]
        simp only [← add_assoc]
        rw [@add_right_cancel_iff]
        rw [<- Finset.sum_add_distrib]
        simp only [← mul_add]
        congr
        ext x
        congr
        split_ifs with ha1 ha2 ha3 ha4 ha5 ha6
        any_goals grind
    · by_cases hcas : pref = []
      · simp_all
        unfold q
        simp only [div_eq_zero_iff, not_or]
        simp_all
        exact h_2
      · rw [getElem_push]
        grind
  · expose_names
    fconstructor
    · unfold quot_1
      simp [h_3.1]
    fconstructor
    · simp_all [quot_1,rem_1]
      congr
      grind
    · simp [quot_1]
      by_cases hcas : b.fst = #[]
      · simp_all
        have haux : pref = []
        · grind
        simp [haux,sdif] at *
        have haux2 : cur = (cur :: suff)[0]
        · simp
        simp [← h_1] at haux2
        simp [haux2] at *
        simp [rem_1] at *
        apply hA
        simp only [← getD_eq_getD_getElem?,add_arrays_prop,def_mul,add_arrays_size,mul_ar_len]
        simp [getD_replicate_zero]
        grind
      · grind
  · expose_names
    fconstructor
    · rfl
    fconstructor
    · simp_all [sdif,rem,quot]
      ext i hi1 hi2
      · simp [add_arrays_size,mul_ar_len]
        omega
      · rw [getElem_eq_getD 0,getElem_eq_getD 0,add_arrays_prop,def_mul]
        simp
    · simp [quot]
  · grind


lemma rem_quot_array_zero (A B : Array F) (hB : B.size > 0) (hB2 : B.getD (B.size -1) 0 ≠ 0)  :
    (rem_quot_array A B hB).1.getD (B.size - 1) 0 = 0 := by
  generalize h : (rem_quot_array A B hB) = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, ⟨quo,⟨rem,hrem⟩⟩⟩ =>
    ⌜ xs.suffix = [] → (rem).getD (B.size - 1) 0 = 0⌝
  with mleave
  any_goals grind  [rem_quot_aux_zero]





















end APolynomial
