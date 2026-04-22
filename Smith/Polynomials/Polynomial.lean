/-
# Computable implementation of polyonomials with arrays

-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Tactic
import Mathlib.Algebra.Group.Defs
import Smith.Polynomials.ArrayFunctions

namespace APolynomial

variable {F : Type} [Field F] [DecidableEq F]

@[ext]
structure Poly (F : Type) [Field F] [DecidableEq F] : Type where
( Ar : Array F)
( hAr : Ar = #[] ∨ Ar.getD (Ar.size - 1) 0 ≠ 0)

lemma eq_poly (A B : Poly F) : A = B ↔ A.Ar = B.Ar := by
  fconstructor
  · tauto
  · intro h
    ext n ha hb
    · rw [h]
    · simp [h]

lemma eq_poly' (A B : Poly F) (h : ∀ n, A.Ar.getD n 0 = B.Ar.getD n 0) : A = B := by
  have h1 := A.hAr
  have h2 := B.hAr
  rw [eq_poly]
  cases' h1 with h1 h1
  · cases' h2 with h2 h2
    · simp [h1,h2]
    · rw [h1]
      specialize h (B.Ar.size -1)
      simp [h1] at h
      simp [Array.getD_getElem?] at h h2
      choose hb hb2 using h2
      specialize h hb
      tauto
  · cases' h2 with h2 h2
    · rw [h2]
      specialize h (A.Ar.size -1)
      simp [h2] at h
      simp [Array.getD_getElem?] at h h1
      choose hb hb2 using h1
      specialize h hb
      tauto
    · ext
      · by_contra hneg
        wlog hl : A.Ar.size < B.Ar.size
        · specialize this B A
          apply this ?_ h2 h1
          · tauto
          · omega
          · simp [h]
        · grind
      · expose_names
        specialize h i
        simp_all


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
    · simp
    · rw [heq]
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

def add (a b : Poly F) : Poly F where
  Ar := clean_zeros (add_arrays a.Ar b.Ar)
  hAr := by
    apply clean_zeros_prop

lemma add_prop (a b : Poly F) (i : ℕ) : (add a b).Ar.getD i 0 = a.Ar.getD i 0 + b.Ar.getD i 0 := by
  simp only [add,← clean_zeros_eq,add_arrays_prop]

instance inst_Add : Add (Poly F) where
  add := add

lemma add_array (a b : Poly F) : (a + b).Ar = clean_zeros (add_arrays a.Ar b.Ar) := rfl

@[simp]
lemma def_add (a b : Poly F) (i : ℕ) : (a + b).Ar.getD i 0 = a.Ar.getD i 0 + b.Ar.getD i 0 := by
  apply add_prop

lemma add_to_polynomial (a b : Poly F) :
    to_polynomial (a + b) = to_polynomial a + to_polynomial b := by
  ext n
  simp only [to_polynomial, ne_eq, decide_not, List.toFinset_filter,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Polynomial.coeff_ofFinsupp,
    Finsupp.coe_mk, Polynomial.coeff_add]
  apply add_prop

def sub (a b : Poly F) : Poly F where
  Ar := sub_array a.Ar b.Ar
  hAr := by
    apply clean_zeros_prop

lemma sub_prop (a b : Poly F) (i : ℕ) : (sub a b).Ar.getD i 0 = a.Ar.getD i 0 - b.Ar.getD i 0 := by
  simp only [sub,sub_arrays_prop]

instance instSub : Sub (Poly F) where
  sub := sub

@[simp]
lemma def_sub (a b : Poly F) (i : ℕ) : (a - b).Ar.getD i 0 = a.Ar.getD i 0 - b.Ar.getD i 0 := by
  apply sub_prop

lemma sub_to_polynomial (a b : Poly F) :
    to_polynomial (a - b) = to_polynomial a - to_polynomial b := by
  ext n
  simp only [to_polynomial, ne_eq, decide_not, List.toFinset_filter,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Polynomial.coeff_ofFinsupp,
    Finsupp.coe_mk, Polynomial.coeff_sub]
  apply sub_prop

def neg (p : Poly F) : Poly F := {
      Ar := p.Ar.map (fun x => -x)
      hAr := by
        have hAr := p.hAr
        cases' hAr with hAr hAr
        · left
          simp [hAr]
        · right
          simp  [Array.size_map,Array.getElem?_map,Option.map]
          split
          · simp_all
          · simp_all
  }

lemma neg_prop (a : Poly F) (i : ℕ) : (neg a).Ar.getD i 0 = - a.Ar.getD i 0 := by
  simp only [neg, Array.getD_eq_getD_getElem?, Array.getElem?_map,Option.map]
  grind

instance instNeg : Neg (Poly F) where
  neg := neg

@[simp]
lemma def_neg (a : Poly F) (i : ℕ) : (-a).Ar.getD i 0 = - a.Ar.getD i 0 := by
  apply neg_prop

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

def mul (a b : Poly F) : Poly F where
  Ar := clean_zeros (mul_ar a.Ar b.Ar)
  hAr := by
    apply clean_zeros_prop


instance inst_mul : Mul (Poly F) where
  mul := mul

@[simp]
lemma def_mul' (a b : Poly F) (n : ℕ) : (a * b).Ar.getD n 0 =
    ∑ (i : Fin (n+1)), (a.Ar.getD i 0) * (b.Ar.getD (n - i) 0) := by
  have haux : (a*b).Ar = clean_zeros (mul_ar a.Ar b.Ar) := rfl
  rw [haux,← clean_zeros_eq,def_mul]

lemma mul_to_polynomial (a b : Poly F) :
    to_polynomial (a * b) = to_polynomial a * to_polynomial b := by
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

lemma def_one : (1 : Poly F) = {
    Ar := #[1]
    hAr := by simp
  } := rfl

@[simp]
lemma def_one' (i : ℕ) : (1 : Poly F).Ar.getD i 0 = if i = 0 then 1 else 0 := by
  by_cases hcas : i = 0
  · simp [def_one,hcas]
  · simp [def_one,hcas]

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
  rw [eq_poly]
  expose_names
  simp [monomio]
  simp [clean_zeros,monomioar]

@[simp]
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

def shift_mul (P : Poly F) (n : ℕ) (c : F) : Poly F where
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
  apply eq_poly'
  intro m
  rw [shift_mul]
  simp only [Array.emptyWithCapacity_eq, bind_pure_comp, map_pure,
    RangeCursor.mem_range', zero_le, true_and, forIn'_eq_forIn, Std.Range.forIn_eq_forIn_range',
    Std.Range.size, tsub_zero, add_tsub_cancel_right, Nat.div_one, List.forIn_pure_yield_eq_foldl,
    List.foldl_push_eq_append, List.map_const', List.length_range', List.toArray_replicate,
    Array.empty_append, Array.forIn_pure_yield_eq_foldl, Array.foldl_push_eq_append, bind_pure,
    dite_eq_ite]
  split_ifs with hi
  · cases' hi with hi hi
    · simp [hi,monomio_zero,Array.getD_getElem?,Id.run]
      suffices hsuf : P * 0 = 0
      · simp [hsuf]
        simp [def_zero]
      apply to_poly_inj
      rw [mul_to_polynomial,zero_to_polynomial]
      simp
    · rw [def_mul']
      simp [hi,Id.run]
  · rw [def_mul']
    have haux := @def_monomio F _ _ n
    have haux2 : ∑ (i : Fin (m +1)), P.Ar.getD (↑i) 0 * (monomio n c).Ar.getD (m - ↑i) 0 = ∑ (i : Fin (m + 1)), (P.Ar.getD (↑i) 0) * (if (m - ↑i) = n then c else 0)
    · congr
      ext i
      congr
      rw [def_monomio]
    rw [haux2]
    simp
    by_cases hcas : m < n
    · rw [Array.getElem?_append_left]
      simp [Array.getElem?_replicate]
      simp [hcas]
      apply Finset.sum_eq_zero
      simp
      intro x hx
      left
      omega
      grind
    · rw [Array.getElem?_append_right,Array.getElem?_map,Array.size_replicate]
      · rw [Finset.sum_eq_ite ⟨m-n, by omega⟩]
        · simp
          grind
        · grind
      · grind

def npow (n : ℕ) (p : Poly F) :  (Poly F) := match n with
| 0 => 1
| n + 1 => npow n p * p

instance inst_ring : CommRing (Poly F) where
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
  nsmul := nsmulRec
  nsmul_zero := fun x ↦ Poly.ext rfl
  nsmul_succ := by
    exact fun n x ↦ Poly.ext rfl
  add_comm := by
    intro a b
    apply to_poly_inj
    simp [add_to_polynomial]
    apply add_comm
  left_distrib := by
    intro a b c
    apply to_poly_inj
    simp [add_to_polynomial,mul_to_polynomial]
    apply left_distrib
  right_distrib := by
    intro a b c
    apply to_poly_inj
    simp [add_to_polynomial,mul_to_polynomial]
    apply right_distrib
  zero_mul := by
    intro a
    apply to_poly_inj
    simp [zero_to_polynomial,mul_to_polynomial]
  mul_zero := by
    intro a
    apply to_poly_inj
    simp [zero_to_polynomial,mul_to_polynomial]
  mul_comm := by
    intro a b
    apply to_poly_inj
    simp [mul_to_polynomial]
    ring
  mul_assoc := by
    intro a b  c
    apply to_poly_inj
    simp [mul_to_polynomial]
    apply mul_assoc
  one_mul := by
    intro a
    apply to_poly_inj
    simp [mul_to_polynomial,one_to_polynomial]
  mul_one := by
    intro a
    apply to_poly_inj
    simp [mul_to_polynomial,one_to_polynomial]
  natCast := fun n => monomio 0 n
  natCast_zero := by
    apply eq_poly'
    intro n
    simp [monomio,def_zero]
  natCast_succ := by
    intro n
    apply eq_poly'
    intro i
    rw [def_monomio,def_add,def_monomio]
    split_ifs with h1
    · rw [h1,def_one']
      simp
    simp [def_one,h1]
  npow := npow
  npow_zero := by
    intro x
    rfl
  npow_succ := by
    intro n x
    rfl
  sub_eq_add_neg := by
    intro a b
    apply eq_poly'
    intro i
    rw [def_sub,def_add,def_neg,sub_eq_add_neg]
  zsmul :=zsmulRec
  zsmul_zero' := fun p => Poly.ext rfl
  zsmul_succ' := fun n a ↦ Poly.ext rfl
  zsmul_neg' := fun n a ↦ Poly.ext rfl
  neg_add_cancel := by
    intro a
    apply eq_poly'
    intro n
    rw [def_add,def_neg,neg_add_cancel,def_zero]
    grind
  intCast := fun n => monomio 0 n
  intCast_ofNat := by
    intro n
    apply eq_poly'
    intro i
    simp [monomio]
    grind
  intCast_negSucc := by
    intro n
    apply eq_poly'
    intro i
    rw [def_neg]
    simp [monomio,monomioar,Nat.cast]
    grind

instance inst_EuclideanDomain : EuclideanDomain (Poly F) where
  exists_pair_ne := by
    use {Ar := #[], hAr := by tauto }
    use {Ar := #[1], hAr := by simp}
    simp
  quotient := fun a b ↦
    if hb : b.Ar.size = 0 then
      0
    else if b.Ar.size > a.Ar.size then
      0
    else
      {Ar := (clean_zeros (rem_quot_array a.Ar b.Ar (by omega)).2), hAr := by grind [clean_zeros_prop]}
  quotient_zero := by
    intro a
    simp [def_zero]
  remainder := fun a b ↦
    if hb : b.Ar.size = 0 then
      a
    else if b.Ar.size > a.Ar.size then
      a
    else
      {Ar := (clean_zeros (rem_quot_array a.Ar b.Ar (by omega)).1), hAr := by grind [clean_zeros_prop]}
  quotient_mul_add_remainder_eq := by
    intro a b
    simp
    split_ifs
    any_goals grind
    · expose_names
      have haux := rem_quot_array_prop a.Ar b.Ar (by grind) ?_ ?_ (by omega)
      · apply eq_poly'
        intro n
        nth_rewrite 3 [haux]
        simp only [def_add,def_mul',← clean_zeros_eq,add_arrays_prop,def_mul]
      · grind [b.hAr]
      · grind [a.hAr]
  r := fun a b ↦ a.Ar.size < b.Ar.size
  r_wellFounded :=  WellFounded.onFun wellFounded_lt
  remainder_lt := by
    intro a b hb
    split_ifs with h1 h2
    · simp [def_zero] at hb
      simp at h1
      exfalso
      apply hb
      ext
      · simp [h1]
      · simp [h1]
    · exact h2
    · simp
      apply clean_zeros_size_lt'
      · omega
      · intro i hi
        by_cases hcas : i = b.Ar.size -1
        · rw [hcas]
          apply rem_quot_array_zero
          · grind [b.hAr]
        · rw [rem_quot_array_zeros]
          grind [b.hAr]
          omega

  mul_left_not_lt := by
    intro a b h
    by_cases hcas : a = 0
    · simp [hcas]
    simp [def_zero] at hcas
    have hanz : a.Ar ≠ #[]
    · intro h
      apply hcas
      ext
      all_goals simp [h]
    have haux : (a * b).Ar = clean_zeros (mul_ar a.Ar b.Ar)
    · rfl
    rw [haux]
    rw [clean_zeros_size,mul_ar_len]
    · suffices hsuf : b.Ar.size > 0
      · omega
      simp [def_zero] at h
      by_contra hcon
      apply h
      simp at hcon
      ext
      · simp [hcon]
      · simp [hcon]
    · rw [def_mul]
      have hb : b.Ar.size > 0
      · simp [def_zero] at h
        cases b
        grind
      have heq : a.Ar.size + b.Ar.size - 1 - 1 - (a.Ar.size - 1) = b.Ar.size - 1
      · have ha : a.Ar.size > 0
        · grind
        omega
      rw [Finset.sum_eq_single ⟨a.Ar.size -1,by rw [mul_ar_len]; omega⟩ ]
      · simp [mul_ar_len a.Ar b.Ar]
        fconstructor
        · have ha := a.hAr
          cases' ha with ha ha
          · tauto
          · simp at ha
            exact ha
        · have hauc2 := b.hAr
          cases' hauc2 with h1 h2
          · grind
          · simp at h2
            rw [heq]
            exact h2
      · intro i hun hiv
        cases' i with i ival
        simp_all
        by_cases hcas : i < a.Ar.size - 1
        · right
          rw [mul_ar_len]
          grind
        · left
          grind
      · simp

end APolynomial
