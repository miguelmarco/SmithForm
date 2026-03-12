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
import Smith.RangeCursor

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

end AMat
