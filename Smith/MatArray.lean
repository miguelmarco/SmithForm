/-
# Matrices implemented as arrays.

We introduce the structure `Mat` to represent a n × m matrix as an
array, together with a proofs that its size is n * m.
-/
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Std.Tactic

set_option linter.style.cases false
set_option linter.flexible false

variable {m n l : ℕ}
variable {R : Type}

open Matrix Nat Array

namespace AMat

structure Mat (n m : ℕ) (R : Type) where
  Ar : Array R
  hAr : size Ar = n * m

variable (A : Mat n m R) (B : Mat m l R)

@[simp]
lemma Mat_size (A : Mat n m R) : A.Ar.size = n * m := A.hAr

@[grind →]
lemma ijle (i : ℕ) (hi : i < n) (j : ℕ) (hj : j < m) : i * m + j < n * m := by
  nlinarith

@[grind →]
lemma imn (i m n : ℕ) (h : i < n * m) : i / m < n := by
  rw [Nat.div_lt_iff_lt_mul]
  · exact h
  · grind

@[grind →]
lemma imn' (i m n : ℕ) (h : i < n * m) : i % m < m := by
  apply mod_lt
  grind

@[grind →]
lemma eq_mod (a1 a2 : Fin n) (b1 b2 : Fin m) (h : a1.1 * m + b1.1 = a2.1 * m + b2.1) : b1 = b2 := by
  cases' b1 with b1 hb1
  cases' b2 with b2 hb2
  simp at h ⊢
  apply_fun (fun x => x % m) at h
  simp [mod_eq_of_lt hb1, mod_eq_of_lt hb2] at h
  exact h

@[grind →]
lemma eq_mod' (a1 a2 : Fin n) (b1 b2 : Fin m) (h : a1.1 * m + b1.1 = a2.1 * m + b2.1) :
    a1 = a2 := by
  have haux := eq_mod _ _ _ _ h
  cases haux
  simp at h
  cases' b1 with b1 hb1
  omega

def Aget (A : Mat n m R) (i : Fin n) (j : Fin m) : R :=
  A.Ar[i * m + j]'(by rw [A.hAr]; exact ijle i.1 i.2 j.1 j.2)

def Aset (A : Mat n m R) (i : Fin n) (j : Fin m) (v : R) : Mat n m R := by
  fconstructor
  · exact Array.set A.Ar (i.1 * m + j.1) v (by rw [A.hAr]; grind)
  · rw [Array.size_set,A.hAr]

lemma def_Aget (A : Mat n m R) (i : Fin n) (j : Fin m) :
    Aget A i j = A.Ar[i * m + j]'(by rw [A.hAr]; exact ijle i.1 i.2 j.1 j.2) := by
  rfl

lemma def_Aget' (A : Mat n m R) (i : ℕ) (hi : i < n * m) :
    A.Ar[i]'(by simp [hi]) = Aget A ⟨i / m , by grind⟩ ⟨i % m , by grind⟩ := by
  by_cases hcas : 0 = m
  · cases hcas
    grind
  simp [def_Aget]
  congr
  rw [mul_comm,Nat.div_add_mod]

lemma eq_iff (A B : Mat n m R) : A = B ↔ ∀ i, ∀ j, Aget A i j = Aget B i j := by
  fconstructor
  · intro h
    rw [h]
    simp
  · intro h
    suffices hsuf : A.Ar = B.Ar
    · cases' A with A hA
      cases' B with B hB
      simp at hsuf
      simp [hsuf]
    ext i hi hi2
    · simp [A.hAr,B.hAr]
    · simp [A.hAr] at hi
      specialize h ⟨(i / m),by grind⟩  ⟨(i % m),by grind⟩
      simp [def_Aget] at h
      have haux : i / m * m + i % m = i
      · exact div_add_mod' i m
      grind

@[ext]
lemma Aget_eq (A B : Mat n m R) (h : ∀ i, ∀ j, Aget A i j = Aget B i j) :  A = B := by
  rw [eq_iff]
  exact h

lemma def_Aset (A : Mat n m R) (i : Fin n) (j : Fin m) (v : R) (a : Fin n) (b : Fin m) :
  Aget (Aset A i j v) a b = if a = i ∧ b = j then
    v
  else
    Aget A a b := by
  simp [def_Aget,Aset]
  split_ifs with h1
  · grind only [= getElem_set]
  · have haux : a.1 * m + b.1 ≠ i.1 * m + j.1
    · intro hneg
      apply h1
      grind
    grind

def frommatrix (M : Matrix (Fin n) (Fin m) R) : Mat n m R where
  Ar := ofFn (fun i : Fin (n * m) => M ⟨(i / m), by grind⟩ ⟨i % m, by grind⟩)
  hAr := by simp

def tomatrix (A : Mat n m R) : Matrix (Fin n) (Fin m) R := Aget A

@[simp]
lemma def_tomatrix (A : Mat n m R) (a : Fin n) (b : Fin m) :
  tomatrix A a b = Aget A a b := rfl

@[simp]
lemma def_frommatrix (M : Matrix (Fin n) (Fin m) R) (a : Fin n) (b : Fin m) :
    Aget (frommatrix M) a b = M a b := by
  simp [Aget,frommatrix]
  cases' a with a ha
  cases' b with b hb
  simp
  congr
  · rw [Nat.div_eq_iff]
    · fconstructor
      · grind
      · omega
    · omega
  · exact mod_eq_of_lt hb

@[simp]
lemma tofrommatrix (M : Matrix (Fin n) (Fin m) R) : tomatrix (frommatrix M) = M := by
  ext i j
  simp

@[simp]
lemma fromtomatrix (A : Mat n m R) : frommatrix (tomatrix A) = A := by
  ext i j
  simp

def swap (A : Mat n m R) (i1 : Fin n) (j1 : Fin m) (i2 : Fin n) (j2 : Fin m) : Mat n m R := by
  fconstructor
  · apply Array.swap A.Ar (i1.1 * m + j1.1) (i2.1 * m + j2.1) (by grind [A.hAr]) (by grind [A.hAr])
  · simp [A.hAr]

lemma def_swap (A : Mat n m R) (i1 : Fin n) (j1 : Fin m) (i2 : Fin n)
  (j2 : Fin m) (a : Fin n) (b : Fin m) :
    Aget (swap A i1 j1 i2 j2) a b =
      if (a = i1 ∧ b = j1)
      then
        Aget A i2 j2
      else if (a = i2 ∧ b = j2)
      then
        Aget A i1 j1
      else
        Aget A a b
  := by
  simp [swap,Array.swap_def,Array.getElem_set,def_Aget]
  split_ifs with h1 h2 h3
  all_goals grind

def swap_row (A : Mat n m R) (i j : Fin n) : Mat n m R := Id.run do
  let mut B := A
  for h : k in [:m] do
    B := swap B i (⟨k,Membership.get_elem_helper h rfl⟩ : Fin m)
      j ⟨k,Membership.get_elem_helper h rfl⟩
  return B

open Std.Do

lemma def_swap_row (A : Mat n m R) (i j : Fin n) (a : Fin n) (b : Fin m) :
    Aget (swap_row A i j) a b =
      if a = i then
        Aget A j b
      else if a = j then
        Aget A i b
      else
        Aget A a b := by
  generalize h : swap_row A i j = resul
  apply Id.of_wp_run_eq h
  mvcgen
  · exact ⇓⟨xs, out⟩ => ⌜(xs.prefix.length ≤ b.1 ∧ ∀ a, Aget out a b = Aget A a b) ∨
      (b.1 < xs.prefix.length ∧  ∀ a, Aget A a b =
        if a = i then Aget out j b else if a = j then Aget out i b else Aget out a b)⌝
  all_goals mleave
  · expose_names
    cases' h_2 with h2 h3
    · cases' h2 with h2 h4
      simp
      by_cases hcas : pref.length  = b
      · right
        simp [def_swap]
        simp [hcas]
        intro a
        split_ifs
        any_goals grind
      · left
        fconstructor
        · omega
        · intro a
          rw [def_swap]
          split_ifs with h1 h2
          any_goals grind
    · cases' h3 with h3 h4
      simp [def_swap]
      right
      fconstructor
      · omega
      · intro a
        split_ifs
        any_goals grind
  · simp
  · expose_names
    simp at h_1
    cases' h_1 with h1 h2
    · grind
    · simp [h2]
      split_ifs with h1 h2 h3
      any_goals grind

def swap_col (A : Mat n m R) (i j : Fin m) : Mat n m R := Id.run do
  let mut B := A
  for h : k in [:n] do
    B := swap B ⟨k,Membership.get_elem_helper h rfl⟩  i ⟨k,Membership.get_elem_helper h rfl⟩ j
  return B

lemma def_swap_col (A : Mat n m R) (i j : Fin m) (a : Fin n) (b : Fin m) :
    Aget (swap_col A i j) a b =
      if b = i then
        Aget A a j
      else if b = j then
        Aget A a i
      else
        Aget A a b := by
  generalize h : swap_col A i j = resul
  apply Id.of_wp_run_eq h
  mvcgen
  · exact ⇓⟨xs, out⟩ => ⌜(xs.prefix.length ≤ a.1 ∧ ∀ b, Aget out a b = Aget A a b) ∨
      (a.1 < xs.prefix.length ∧ ∀ b,
        Aget A a b = if b = i then Aget out a j else if b = j then Aget out a i else Aget out a b)⌝
  all_goals mleave
  · expose_names
    cases' h_2 with h2 h3
    · cases' h2 with h2 h4
      simp
      by_cases hcas : pref.length  = a
      · right
        simp [def_swap]
        simp [hcas]
        intro b
        split_ifs
        any_goals grind
      · left
        fconstructor
        · omega
        · intro b
          rw [def_swap]
          split_ifs with h1 h2
          any_goals grind
    · cases' h3 with h3 h4
      simp [def_swap]
      right
      fconstructor
      · omega
      · intro b
        split_ifs
        any_goals grind
  · simp
  · expose_names
    simp at h_1
    cases' h_1 with h1 h2
    · grind
    · simp [h2]
      split_ifs with h1 h2 h3
      any_goals grind


variable [ED : EuclideanDomain R]

infixl:50 " ≺ " => EuclideanDomain.r

def TM (i j : Fin n) : Matrix (Fin n) (Fin n) R := fun a b =>
  if a = j then (if b = i then 1 else 0) else
    if a = i then (if b = j then 1 else 0) else
    if a = b then 1 else 0

def AM (i j : Fin n) (k : R) : Matrix (Fin n) (Fin n) R := fun a b =>
  if a = j ∧ b = i then k else
    if a = b then 1 else 0

def RM : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun a b =>
  if a = ⟨n, by grind⟩ then
    if b = 0 then 1 else 0
  else
    if b = a + 1 then 1 else 0

@[grind →]
lemma abmn (a b m n : ℕ) (ha : a < n) (hb : b < m) : a * m + b <  n * m := by
  have hn : 1 ≤ n
  · grind
  have hm : 0 < m
  · grind
  have ha : a ≤  n - 1
  · grind
  have hm : m ≤ n * m
  · nth_grewrite 1 [← one_mul m,Nat.mul_le_mul_right_iff ]
    · exact hn
    exact hm
  calc a * m + b ≤  (n - 1) * m + b := by simp [Nat.mul_le_mul_right m ha]
       _ < (n - 1) * m + m := by grind
       _ = n * m := by rw [Nat.sub_mul,one_mul, Nat.sub_add_cancel]; exact hm

def Mat_mul (A : Mat n m R) (B : Mat m l R) : Mat n l R where
  Ar := Array.ofFn (fun (a : Fin (n * l)) => ∑ (j : Fin m),
    (Aget A ⟨(a.1 / l),imn _ _ _  a.2⟩  j) * (Aget B j ⟨a.1 % l,by grind⟩))
  hAr := size_ofFn

instance hmul_inst : HMul (Mat n m R) (Mat m l R) (Mat n l R) where
  hMul := Mat_mul

lemma def_Mat_mul (A : Mat n m R) (B : Mat m l R) (a : Fin n) (b : Fin l) :
    Aget (A * B) a b = ∑ (j : Fin m), (Aget A a j) * (Aget B j b) := by
  cases' a with a ha
  cases' b with b hb
  have haux : l > 0 := by omega
  have haux1 : (a * l + b) / l = a
  · rw [mul_comm,Nat.mul_add_div haux]
    simp
    grind
  simp [hmul_inst,Mat_mul,def_Aget,haux1,Nat.mod_eq_of_lt hb]

theorem mul_hom (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin l) R) :
    (frommatrix A) * (frommatrix B) = frommatrix (A * B) := by
  ext i j
  rw [def_Mat_mul]
  simp [def_frommatrix]
  rw [mul_apply]

theorem mul_hom' (A : Mat n m R) (B : Mat m l R) :
    tomatrix (A * B) = tomatrix A * (tomatrix B) := by
  apply_fun frommatrix
  · rw [← mul_hom]
    simp
  · intro a b hab
    rw [← tofrommatrix a, ← tofrommatrix b, hab]

@[simp]
theorem mul_assoc (s : ℕ) (A : Mat n m R) (B : Mat m l R) (C : Mat l s R) :
    A * (B * C) = A * B * C := by
  apply_fun tomatrix
  · simp [mul_hom']
    rw [Matrix.mul_assoc]
  · intro a b ha
    rw [← fromtomatrix a, ← fromtomatrix b, ha]

def add_multiple_row (A : Mat n m R) (i j : Fin n) (l : R) : (Mat n m R) := Id.run do
  let mut res := A
  for h : k in [:m] do
    let fk : Fin m := ⟨k,Membership.get_elem_helper h rfl⟩
    res := Aset res j fk ((Aget A j fk ) + l * (Aget A i fk))
  return res

lemma def_add_multiple_row (A : Mat n m R) (i j : Fin n) (l : R) (a : Fin n) (b : Fin m) :
    Aget (add_multiple_row A i j l) a b =
      if a = j then
        Aget A j b + l * Aget A i b
      else
        Aget A a b := by
  generalize h : add_multiple_row A i j l = result
  apply Id.of_wp_run_eq h
  mvcgen
  · exact ⇓⟨xs, out⟩ => ⌜(xs.prefix.length ≤ b.1 ∧ ∀ a, Aget out a b = Aget A a b) ∨
    (b.1 < xs.prefix.length ∧ ∀ a, Aget out a b =
      if a = j then Aget A j b + l * Aget A i b  else  Aget A a b)⌝
  all_goals mleave
  · expose_names
    cases' h_2 with h2 h2
    · cases' h2 with h3 h4
      simp
      by_cases hcas : pref.length + 1 ≤ b
      · left
        fconstructor
        · omega
        · simp [res,def_Aset]
          intro a
          split_ifs with hja
          any_goals grind
      · right
        fconstructor
        · omega
        · simp [res,def_Aset]
          intro a
          split_ifs with hj1 hj2 hj3
          any_goals grind
    · cases' h2 with h2 h3
      simp [res,def_Aset]
      right
      fconstructor
      · omega
      · intro a
        split_ifs with hj1 hj2
        any_goals grind
  · simp
  · expose_names
    simp at h_1
    cases' h_1 with h1 h2
    · cases' h1 with h1 h2
      split_ifs
      any_goals grind
    · rw [h2]

def add_multiple_col (A : Mat n m R) (i j : Fin m) (l : R) : (Mat n m R) := Id.run do
  let mut res := A
  for h : k in [:n] do
    let fk : Fin n := ⟨k,Membership.get_elem_helper h rfl⟩
    res := Aset res fk j ((Aget A fk j ) + l * (Aget A fk i))
  return res

lemma def_add_multiple_col (A : Mat n m R) (i j : Fin m) (l : R) (a : Fin n) (b : Fin m) :
    Aget (add_multiple_col A i j l) a b =
      if b = j then
        Aget A a j + l * Aget A a i
      else
        Aget A a b := by
  generalize h : add_multiple_col A i j l = result
  apply Id.of_wp_run_eq h
  mvcgen
  · exact ⇓⟨xs, out⟩ => ⌜(xs.prefix.length ≤ a.1 ∧ ∀ b, Aget out a b = Aget A a b) ∨
    (a.1 < xs.prefix.length ∧ ∀ b, Aget out a b =
      if b = j then Aget A a j + l * Aget A a i else  Aget A a b)⌝
  all_goals mleave
  · expose_names
    cases' h_2 with h2 h2
    · cases' h2 with h3 h4
      simp
      by_cases hcas : pref.length + 1 ≤ a
      · left
        fconstructor
        · omega
        · simp [res,def_Aset]
          intro b
          split_ifs with hja
          any_goals grind
      · right
        fconstructor
        · omega
        · simp [res,def_Aset]
          intro b
          split_ifs with hj1 hj2 hj3
          any_goals grind
    · cases' h2 with h2 h3
      simp [res,def_Aset]
      right
      fconstructor
      · omega
      · intro b
        split_ifs with hj1 hj2
        any_goals grind
  · simp
  · expose_names
    simp at h_1
    cases' h_1 with h1 h2
    · cases' h1 with h1 h2
      split_ifs
      any_goals grind
    · rw [h2]

lemma mul_swap_row (A : Mat n m R) (B : Mat m l R) (i j : Fin n) :
    (swap_row A i j) * B = swap_row (A * B) i j := by
  ext a b
  simp [def_Mat_mul,def_swap_row]

lemma mul_swap_col (A : Mat n m R) (B : Mat m l R) (i j : Fin l) :
    A * (swap_col B i j) = swap_col (A * B) i j := by
  ext a b
  simp [def_Mat_mul,def_swap_col]

lemma mul_swap_row_col (A : Mat n m R) (B : Mat m l R) (i j : Fin m) :
    (swap_col A i j) * (swap_row B i j) = A * B := by
  ext a b
  simp [def_Mat_mul]
  rw [← Finset.sum_add_sum_compl {i,j}, ←Finset.sum_add_sum_compl {i,j}]
  have haux : ({i, j} : Finset (Fin m))  = {j, i} := by aesop
  nth_rewrite 1 [haux]
  congr 1
  · by_cases hcas : i = j
    · simp [hcas,def_swap_col,def_swap_row]
    · have haux2 : j ≠ i := by tauto
      simp [Finset.sum_pair hcas, Finset.sum_pair haux2, def_swap_row,def_swap_col,haux2]
  · apply Finset.sum_bijective (id : Fin m → Fin m)
    any_goals simp
    · intro k h1 h2
      simp [def_swap_col,def_swap_row,h1,h2]

lemma mul_TM_row (A : Mat n m R) (i j : Fin n) : (frommatrix (TM i j) :
    Mat n n R)  * A = swap_row A i j := by
  ext a b
  simp [def_swap_row,def_Mat_mul, TM]
  split_ifs
  any_goals grind

lemma mul_TM_row_tomatrix (A : Mat n m R) (i j : Fin n) :
    (TM i j) * tomatrix A = tomatrix (swap_row A i j) := by
  ext a b
  simp [def_tomatrix,mul_apply, TM,def_swap_row]
  split_ifs
  any_goals grind

lemma mul_TM_col (A : Mat n m R) (i j : Fin m) :
    A * (frommatrix (TM i j : Matrix (Fin m) (Fin m) R)) = swap_col A i j := by
  ext a b
  simp [def_swap_col,def_Mat_mul, TM]
  split_ifs with h1 h2 h3
  · cases h1
    cases h2
    simp [Finset.sum_ite]
    have haux : ∑ x ∈ {x | ¬x = i} with x = i, Aget A a x = 0
    · apply Finset.sum_eq_zero
      simp
    simp [haux]
    apply Finset.sum_eq_single_of_mem i
    any_goals grind
  · cases h1
    rw [Finset.sum_ite,Finset.sum_eq_single_of_mem j]
    · simp
      apply Finset.sum_eq_zero
      simp
      grind
    any_goals grind
  · cases h3
    simp [Finset.sum_ite]
    rw [Finset.sum_eq_single i]
    any_goals grind
  · simp [Finset.sum_ite]
    grind

lemma mul_TM_col_tomatrix (A : Mat n m R) (i j : Fin m) :
    tomatrix A* (TM i j)  = tomatrix (swap_col A i j) := by
  apply_fun frommatrix
  · simp [← mul_hom,mul_TM_col]
  · intro a b hab
    rw [← tofrommatrix a,← tofrommatrix b, hab]

lemma mul_add_multiple_row (A : Mat n m R) (B : Mat m l R) (i j : Fin n) (d : R) :
    (add_multiple_row A i j d) * B = add_multiple_row (A * B) i j d := by
  ext a b
  simp [def_add_multiple_row,def_Mat_mul]
  split_ifs with h1
  · cases h1
    have haux : ∑ x, Aget A j x * Aget B x b + d * ∑ x, Aget A i x * Aget B x b =
         ∑ x, (Aget A j x * Aget B x b + d * Aget A i x * Aget B x b)
    · rw [← Set.toFinset_univ,Finset.sum_add_distrib,Finset.mul_sum]
      simp
      grind
    rw [haux]
    grind
  · grind

lemma mul_add_multiple_col (A : Mat n m R) (B : Mat m l R) (i j : Fin l) (d : R) :
    A * (add_multiple_col B i j d)  = add_multiple_col (A * B) i j d := by
  ext a b
  simp [def_add_multiple_col,def_Mat_mul]
  split_ifs with h1
  · cases h1
    have haux :  ∑ x, Aget A a x * Aget B x j + d * ∑ x, Aget A a x * Aget B x i =
        ∑ x, (Aget A a x * Aget B x j + d * Aget A a x * Aget B x i)
    · rw [← Set.toFinset_univ,mul_comm d _, Finset.sum_mul,Finset.sum_add_distrib]
      simp [mul_comm _ d]
      grind
    rw [haux]
    grind
  · grind

lemma mul_add_multiple_row_eq (A : Mat n m R) (B : Mat m l R) (i j : Fin m) (h : i ≠ j) (d : R) :
    (add_multiple_col A i j d) * (add_multiple_row B j i (-d)) = A * B := by
  ext a b
  simp [def_add_multiple_col,def_add_multiple_row,def_Mat_mul]
  rw [← Finset.sum_add_sum_compl {i,j}, ←Finset.sum_add_sum_compl {i,j}]
  congr 1
  · simp [Finset.sum_pair h, h]
    split_ifs
    · grind
    · ring
  · rw [Finset.sum_bijective id]
    · simp
    · simp
    · intro x hx
      simp at hx
      simp [hx]

structure LUM (A : Mat n m R) : Type where
  (L : Mat n n R)
  (M : Mat n m R)
  (R : Mat m m R)
  (h : L * M * R = A)

def triv_LUM (A : Mat n m R) : LUM A where
  L := frommatrix 1
  M := A
  R := frommatrix 1
  h := by
    apply_fun tomatrix
    · simp [mul_hom']
    · intro a b hab
      rw [← fromtomatrix a, ← fromtomatrix b, hab]

def LUM_swap_row (D : LUM A) (i j : Fin n) : LUM A where
  L := swap_col D.L i j
  M := swap_row D.M i j
  R := D.R
  h := by
    rw [@mul_swap_row_col,D.h]

def LUM_swap_col (D : LUM A) (i j : Fin m) : LUM A where
  L := D.L
  M := swap_col D.M i j
  R := swap_row D.R i j
  h := by rw [← mul_assoc, mul_swap_row_col, mul_assoc,D.h]

def LUM_add_multiple_col (D : LUM A) (i j : Fin m) (h : i ≠ j) (d : R) : LUM A where
  L := D.L
  M := add_multiple_col D.M i j d
  R := add_multiple_row D.R j i (-d)
  h := by
    rw [← mul_assoc,mul_add_multiple_row_eq _ _ _ _ h,mul_assoc]
    exact D.h

def LUM_add_multiple_row (D : LUM A) (i j : Fin n) (h : j ≠ i) (d : R) : LUM A where
  L := add_multiple_col D.L j i (-d)
  M := add_multiple_row D.M i j d
  R := D.R
  h := by
    nth_rewrite  2 [← neg_neg d]
    rw [mul_add_multiple_row_eq _ _ _ _ h (-d)]
    exact D.h

variable [DecidableEq R]


open Std.Do

set_option mvcgen.warning false

@[grind →]
lemma aux_cursor (i m j : ℕ) (xs : [i:m].toList.Cursor) (hj : j ∈ xs.prefix) : j < m := by
  have haux := xs.property
  suffices hsuf : j ∈ [i:m].toList
  · rw [List.mem_range'] at hsuf
    choose x hx using hsuf
    simp at hx
    omega
  rw [← haux]
  exact List.mem_append_left xs.suffix hj

@[simp]
lemma mem_range' (i m j : ℕ) : j ∈ [i:m].toList ↔ i ≤ j ∧ j < m := by
  rw [List.mem_range']
  simp
  fconstructor
  · intro h
    choose k hk hk2 using h
    omega
  · intro h
    cases' h with h1 h2
    use j - i
    omega

lemma aux_cursor' (i m j : ℕ) (xs : [i:m].toList.Cursor) (h : 0 < xs.suffix.length) : j ∈ xs.prefix ↔ i ≤ j ∧ j < xs.current := by
  have haux := xs.property
  fconstructor
  · intro h2
    fconstructor
    · suffices hsuf: j ∈ [i:m].toList
      · simp at hsuf
        exact hsuf.1
      rw [← haux]
      simp
      left
      exact h2
    · induction' m with m hm
      · have haux2 : j ∈ [i:0].toList
        · rw [← haux]
          simp
          left
          exact h2
        simp at haux2
      ·


@[grind →]
lemma aux_cursor' (i m j : ℕ) (xs : [i:m].toList.Cursor) (hj : j ∈ xs.suffix) : j < m := by
  have haux := xs.property
  suffices hsuf : j ∈ [i:m].toList
  · rw [List.mem_range'] at hsuf
    choose x hx using hsuf
    simp at hx
    omega
  rw [← haux]
  exact List.mem_append_right xs.prefix hj

def first_nonzero_i_row (A : Mat n m R) (i : ℕ) : Option ℕ := Id.run do
  if hi : n ≤ i ∨ m ≤ i then return none else
  let ki : Fin n := ⟨i,by simp at hi; tauto⟩
  for h : k in [i:m] do
    if Aget A ki ⟨k,Membership.get_elem_helper h rfl⟩ ≠ 0 then
      return some k
    else
      continue
  return none

@[grind →]
lemma first_nonzero_i_row_inter (A : Mat n m R) (i b : ℕ) :
    first_nonzero_i_row A i = some b → (i < n ∧ i < m ∧ i ≤ b ∧ b < m) := by
  generalize hA : first_nonzero_i_row A i = res
  apply Id.of_wp_run_eq hA
  mvcgen invariants
  · ⇓⟨xs, out⟩ => ⌜(out.1 = some (some b) →
        (i < n ∧ i < m ∧ i ≤ b ∧ b < m)) ∧ ∀ k_idx, k_idx ∈ xs.prefix → i ≤ k_idx⌝
  with mleave
  · tauto
  · expose_names
    simp_all
    fconstructor
    · intro hcur
      have haux : b ∈ [i:m].toList
      · rw [h_1,hcur]
        simp
      grind
    · grind
  · expose_names
    simp_all
    grind
  · simp
  · simp
  · expose_names
    intro ha
    apply h_2.1
    grind

lemma first_nonzero_i_row_prop_1 (A : Mat n m R) (i b : ℕ) (h : first_nonzero_i_row A i = some b) :
    Aget A ⟨i,by grind⟩ ⟨b,by grind⟩ ≠ 0 := by
  have him := first_nonzero_i_row_inter A i b h
  suffices hsuf : first_nonzero_i_row A i = some b → Aget A ⟨i,by grind⟩ ⟨b,by grind⟩ ≠ 0
  · apply hsuf h
  generalize hA : first_nonzero_i_row A i = res
  apply Id.of_wp_run_eq hA
  mvcgen invariants
  · ⇓⟨xs, out⟩ => ⌜(out.1 = some (some b) → Aget A ⟨i,by grind⟩ ⟨b,by grind⟩ ≠ 0)⌝
  with simp_all
  · grind

lemma first_nonzero_i_row_prop_2 (A : Mat n m R) (i b : ℕ) (h : first_nonzero_i_row A i = some b) :
    ∀ (h : c < b), i ≤ c → Aget A ⟨i,by grind⟩ ⟨c,by grind⟩ = 0 := by
  have him := first_nonzero_i_row_inter A i b h
  suffices hsuf : first_nonzero_i_row A i = some b → ∀ (h : c < b), i ≤ c → Aget A ⟨i,by grind⟩ ⟨c,by grind⟩ = 0
  · apply hsuf h
  generalize hA : first_nonzero_i_row A i = res
  apply Id.of_wp_run_eq hA
  mvcgen invariants
  · Invariant.withEarlyReturn (onReturn := fun r letMuts =>
      ⌜r = some b → ∀ (h : c < b), i ≤ c → Aget A ⟨i, by grind⟩ ⟨c, by grind⟩ = 0⌝) (onContinue :=
      fun xs letMuts => ⌜(hxs : 0 < xs.suffix.length) →  ∀ d, (hd : d < (xs.current hxs)) →  Aget A ⟨i, by grind⟩ ⟨d,by grind⟩ = 0⌝)
  with mleave
  · simp
  · expose_names
    right
    cases' h_4 with h4 h4
    · cases' h4 with h4 h5
      simp at h5
      simp
      intro hcur hcb hic
      cases hcur
      apply h5
      exact hcb
    · simp
      intro hcur hcb hic
      choose a ha using h4
      grind
  · simp_all
    expose_names
    intro hxs d hd
    cases' h_4 with h4 h5
    · by_cases hcas : d = cur
      · cases hcas
        exact h_3
      · apply h5
        change d < cur
        have haix : d < suff[0]'(hxs) := hd
        have haux : cur + 1 = suff[0]'(hxs)
        · have h11 : suff[0]'(hxs) ∈ [i:m].toList
          · rw [h_2]
            simp
          have h12 : cur ∈ [i:m].toList
          · rw [h_2]
            simp
          rw [List.mem_range'] at h11 h12
          simp at h11 h12







open EuclideanDomain

def xgcdcompu (a b : R) : R := b / (gcd a b)

def xgcdcompv (a b : R) : R := -a / (gcd a b)

lemma def_xgcdcompu (a b : R) : b = (xgcdcompu a b) * (gcd a b) := by
  by_cases hb : b = 0
  · simp [hb,xgcdcompu]
  · rw [xgcdcompu,mul_comm,EuclideanDomain.mul_div_cancel']
    · intro h
      rw [EuclideanDomain.gcd_eq_zero_iff] at h
      grind
    · exact EuclideanDomain.gcd_dvd_right a b

lemma def_xgcdcompv (a b : R) : a = -(xgcdcompv a b) * (gcd a b) := by
  by_cases ha : a = 0
  · simp [ha,xgcdcompv]
  · rw [xgcdcompv,mul_comm]
    have haux : (gcd a b ) ∣ a
    · exact EuclideanDomain.gcd_dvd_left a b
    choose c hc using haux
    have haux2 : -a = -c * gcd a b
    · nth_rewrite 1 [hc]
      ring
    rw [haux2,EuclideanDomain.mul_div_assoc,EuclideanDomain.div_self]
    simp
    · exact hc
    · simp [EuclideanDomain.gcd_eq_zero_iff]
      grind
    · simp

lemma xgcdcompzero (a b : R) : (xgcdcompu a b) * a + (xgcdcompv a b) * b = 0 := by
  · simp [xgcdcompv, xgcdcompu]
    have h1 := gcd_dvd a b
    by_cases hcas : (gcd a b) = 0
    · simp [hcas]
    · cases' h1 with h1 h2
      choose x hx using h1
      choose y hy using h2
      have ha : a / (gcd a b) = x
      · nth_rewrite 1 [hx]
        apply mul_div_cancel_left₀
        · exact hcas
      have hb : b / (gcd a b) = y
      · nth_rewrite 1 [hy]
        exact mul_div_cancel_left₀ y hcas
      have haux : ((-a )/ (gcd a b)) * b = - ((a / gcd a b) * b)
      · nth_rewrite 1 3 [hx]
        rw [← mul_neg,mul_comm _ (-x),EuclideanDomain.mul_div_assoc]
        rw [neg_mul,neg_mul]
        rw [mul_comm _ x,EuclideanDomain.mul_div_assoc]
        all_goals simp
      rw [haux,ha,hb,hy]
      nth_rewrite 1 [hx]
      ring

lemma xgcdcompone (a b : R) (hb : a ≠ 0) :
    gcdB a b * xgcdcompu a b - gcdA a b * xgcdcompv a b =  1 := by
  have haux := EuclideanDomain.gcd_eq_gcd_ab a b
  have h1 := def_xgcdcompu a b
  have h2 := def_xgcdcompv a b
  nth_rewrite 2 [h2] at haux
  nth_grewrite 5 [h1] at haux
  rw [mul_comm _ (gcd a b),mul_comm _ (gcd a b), ED.mul_assoc,ED.mul_assoc,← mul_add] at haux
  nth_rewrite 1 [← mul_one (gcd a b)] at haux
  have haux2 := sub_eq_zero_of_eq haux
  rw [← mul_sub,mul_eq_zero_iff_left] at haux2
  · grind
  grind

lemma xgcdcompone' (a b : R) (hb : b ≠ 0) :
    gcdB a b * xgcdcompu a b - gcdA a b * xgcdcompv a b =  1 := by
  have haux := EuclideanDomain.gcd_eq_gcd_ab a b
  have h1 := def_xgcdcompu a b
  have h2 := def_xgcdcompv a b
  nth_rewrite 2 [h2] at haux
  nth_grewrite 5 [h1] at haux
  rw [mul_comm _ (gcd a b),mul_comm _ (gcd a b), ED.mul_assoc,ED.mul_assoc,← mul_add] at haux
  nth_rewrite 1 [← mul_one (gcd a b)] at haux
  have haux2 := sub_eq_zero_of_eq haux
  rw [← mul_sub,mul_eq_zero_iff_left] at haux2
  · grind
  grind

def lincom_cols (A : Mat n m R) (i j : Fin m) (u v x y : R) : Mat n m R := Id.run do
  let mut res := A
  for h : k in [:n] do
    let fk : Fin n := ⟨k,Membership.get_elem_helper h rfl⟩
    let a := Aget res fk i
    let b := Aget res fk j
    res := Aset res fk j (x * a + y * b)
    res := Aset res fk i (u * a + v * b)
  return res

lemma def_lincom_cols (A : Mat n m R) (i j : Fin m) (u v x y : R) (a : Fin n) (b : Fin m) :
    Aget (lincom_cols A i j u v x y) a b =
      if b = i then
        u * Aget A a i + v * Aget A a j
      else if b = j then
        x * Aget A a i + y * Aget A a j
      else
        Aget A a b := by
  generalize h : lincom_cols A i j u v x y = result
  apply Id.of_wp_run_eq h
  mvcgen
  · exact ⇓⟨xs, out⟩ => ⌜(xs.prefix.length ≤ a.1 ∧ ∀ b, Aget out a b = Aget A a b) ∨
    (a.1 < xs.prefix.length ∧ ∀ b, Aget out a b =
      if b = i then u * Aget A a i + v * Aget A a j else if b = j then
        x * Aget A a i + y * Aget A a j else Aget A a b)⌝
  all_goals mleave
  · expose_names
    cases' h_2 with h2 h2
    · cases' h2 with h3 h4
      simp
      by_cases hcas : pref.length + 1 ≤ a
      · left
        fconstructor
        · omega
        · intro b
          simp [res_1,res,def_Aset]
          split_ifs with hja
          any_goals grind
      · right
        fconstructor
        · omega
        · simp [res_1,res,def_Aset]
          intro b
          split_ifs with hj1 hj2 hj3
          any_goals grind
    · cases' h2 with h2 h3
      simp [res,res_1,def_Aset]
      right
      fconstructor
      · omega
      · intro b
        split_ifs with hj1 hj2
        any_goals grind
  · simp
  · expose_names
    simp at h_1
    cases' h_1 with h1 h2
    · cases' h1 with h1 h2
      split_ifs
      any_goals grind
    · rw [h2]

def lincom_rows (A : Mat n m R) (i j : Fin n) (u v x y : R) : Mat n m R := Id.run do
  let mut res := A
  for h : k in [:m] do
    let fk : Fin m := ⟨k,Membership.get_elem_helper h rfl⟩
    let a := Aget res i fk
    let b := Aget res j fk
    res := Aset res j fk (x * a + y * b)
    res := Aset res i fk (u * a + v * b)
  return res

lemma def_lincom_rows (A : Mat n m R) (i j : Fin n) (u v x y : R) (a : Fin n) (b : Fin m) :
    Aget (lincom_rows A i j u v x y) a b =
      if a = i then
        u * Aget A i b + v * Aget A j b
      else if a = j then
        x * Aget A i b + y * Aget A j b
      else
        Aget A a b := by
  generalize h : lincom_rows A i j u v x y = result
  apply Id.of_wp_run_eq h
  mvcgen
  · exact ⇓⟨xs, out⟩ => ⌜(xs.prefix.length ≤ b.1 ∧ ∀ a, Aget out a b = Aget A a b) ∨
    (b.1 < xs.prefix.length ∧ ∀ a, Aget out a b =
      if a = i then u * Aget A i b + v * Aget A j b else if a = j then
        x * Aget A i b + y * Aget A j b else Aget A a b)⌝
  all_goals mleave
  · expose_names
    cases' h_2 with h2 h2
    · cases' h2 with h3 h4
      simp
      by_cases hcas : pref.length + 1 ≤ b
      · left
        fconstructor
        · omega
        · intro aa
          simp [res_1,res,def_Aset]
          split_ifs with hja
          any_goals grind
      · right
        fconstructor
        · omega
        · simp [res_1,res,def_Aset]
          intro b
          split_ifs with hj1 hj2 hj3
          any_goals grind
    · cases' h2 with h2 h3
      simp [res,res_1,def_Aset]
      right
      fconstructor
      · omega
      · intro aa
        split_ifs with hj1 hj2
        any_goals grind
  · simp
  · expose_names
    simp at h_1
    cases' h_1 with h1 h2
    · cases' h1 with h1 h2
      split_ifs
      any_goals grind
    · rw [h2]

def reduce_rows (A : Mat n m R) (i j : Fin n) (k : Fin m) : Mat n m R:=
  lincom_rows A i j (gcdA (Aget A i k) (Aget A j k)) (gcdB (Aget A i k) (Aget A j k))
  (xgcdcompu (Aget A i k) (Aget A j k)) (xgcdcompv (Aget A i k) (Aget A j k))

def reduce_cols (A : Mat n m R) (i j : Fin m) (k : Fin n) : Mat n m R:=
  lincom_cols A i j (gcdA (Aget A k i) (Aget A k j)) (gcdB (Aget A k i) (Aget A k j))
  (xgcdcompu (Aget A k i) (Aget A k j)) (xgcdcompv (Aget A k i) (Aget A k j))

@[simp]
lemma lincom_rows_gcd (A : Mat n m R) (i j : Fin n) (k : Fin m) :
    Aget (reduce_rows A i j k) i k = gcd (Aget A i k) (Aget A j k) := by
  simp [reduce_rows,def_lincom_rows,EuclideanDomain.gcd_eq_gcd_ab]
  ring

@[grind =]
lemma lincom_rows_zero (A : Mat n m R) (i j : Fin n) (k : Fin m) (hij : i ≠ j) :
    Aget (reduce_rows A i j k) j k = 0 := by
  have haux : j ≠ i := by tauto
  simp [reduce_rows,def_lincom_rows,haux,xgcdcompzero]

@[grind =]
lemma lincom_rows_other (A : Mat n m R) (i j : Fin n) (k : Fin m) (a : Fin n) (b : Fin m)
  (hai : a ≠ i) (haj : a ≠ j) :
    Aget (reduce_rows A i j k) a b = Aget A a b := by
  simp [reduce_rows,def_lincom_rows,hai,haj]

@[simp]
lemma lincom_cols_gcd (A : Mat n m R) (i j : Fin m) (k : Fin n) :
    Aget (reduce_cols A i j k) k i = gcd (Aget A k i) (Aget A k j) := by
  simp [reduce_cols,def_lincom_cols,EuclideanDomain.gcd_eq_gcd_ab]
  ring

@[grind =]
lemma lincom_cols_zero (A : Mat n m R) (i j : Fin m) (k : Fin n) (hij : i ≠ j) :
    Aget (reduce_cols A i j k) k j = 0 := by
  have haux : j ≠ i := by tauto
  simp [reduce_cols,def_lincom_cols,haux,xgcdcompzero]

@[grind =]
lemma lincom_cols_other (A : Mat n m R) (i j : Fin m) (k : Fin n) (a : Fin n) (b : Fin m)
  (hbi : b ≠ i) (hbj : b ≠ j) :
    Aget (reduce_cols A i j k) a b = Aget A a b := by
  simp [reduce_cols,def_lincom_cols,hbi,hbj]

@[grind =]
lemma lincom_mul (A : Mat n m R) (B : Mat m l R) (i j: Fin m) (u v x y : R) (hij : i ≠ j)
  (h : u * y - v * x = 1) :
    (lincom_cols A i j u v x y) * (lincom_rows B i j y (-x) (-v) u) = A * B := by
  ext a b
  simp [def_lincom_cols,def_lincom_rows,def_Mat_mul]
  rw [← Finset.sum_add_sum_compl {i,j}, ←Finset.sum_add_sum_compl {i,j}]
  congr 1
  · have haux : ¬ j = i := by tauto
    simp [Finset.sum_pair hij,haux]
    grind
  · apply Finset.sum_bijective (id : Fin m → Fin m)
    · exact Function.bijective_id
    · tauto
    intro ii hii
    simp at hii
    cases' hii with hii hiij
    simp [hii, hiij]

def LUM_lincom_rows (D : LUM A) (i j : Fin n) (u v x y : R) (hij : i ≠ j) (h : u * y - v * x = 1) : LUM A where
  L := lincom_cols D.L i j y (-x) (-v) u
  M := lincom_rows D.M i j u v x y
  R := D.R
  h := by
    have haux := lincom_mul D.L D.M i j y (-x) (-v) u hij (by grind)
    simp at haux
    rw [haux]
    exact D.h

def LUM_lincom_cols (D : LUM A) (i j : Fin m) (u v x y : R) (hij : i ≠ j) (h : u * y - v * x = 1) : LUM A where
  L := D.L
  M := lincom_cols D.M i j u v x y
  R := lincom_rows D.R i j y (-x) (-v) u
  h := by
    have haux := lincom_mul D.M D.R i j u v x y hij h
    rw [← mul_assoc,haux,mul_assoc]
    exact D.h

variable [DecidableRel ED.r]

end AMat
