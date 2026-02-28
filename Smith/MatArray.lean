/-
# Matrices implemented as arrays.

We introduce the structure `Mat` to represent a n × m matrix as an
array, together with a proofs that its size is n * m.
-/
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

variable {m n l: ℕ}
variable {R : Type} [ED : EuclideanDomain R] [DecidableEq R] [DecidableRel ED.r]

open Matrix Nat Array

structure Mat (n m : ℕ) (R : Type) where
  Ar : Array R
  hAr : size Ar = n * m

variable (A : Mat n m R) (B : Mat m l R)

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

def Aget (A : Mat n m R) (i : Fin n) (j : Fin m) : R :=
  A.Ar[i * m + j]'(by rw [A.hAr]; exact ijle i.1 i.2 j.1 j.2)

def Aset (A : Mat n m R) (i : Fin n) (j : Fin m) (v : R) : Mat n m R := by
  fconstructor
  · exact Array.set A.Ar (i.1 * m + j.1) v (by rw [A.hAr]; grind)
  · rw [Array.size_set,A.hAr]


#eval Aset (⟨(#[1,2,3,4] : Array ℤ),(by simp)⟩ : Mat 2 2 ℤ) 1 1 7

def frommatrix (M : Matrix (Fin n) (Fin m) R) : Mat n m R where
  Ar := ofFn (fun i : Fin (n * m) => M ⟨(i / m), by grind⟩ ⟨i % m, by grind⟩)
  hAr := by simp

def tomatrix (A : Mat n m R) : Matrix (Fin n) (Fin m) R := Aget A

@[simp]
lemma def_tomatrix (A : Mat n m R) (a : Fin n) (b : Fin m) :
  tomatrix A a b = Aget A a b := rfl

@[simp]
lemma def_frommatrix (M : Matrix (Fin n) (Fin m) R) (a : Fin n) (b : Fin m):
    Aget (frommatrix M) a b = M a b := by
  simp [Aget,frommatrix]
  cases' a with a ha
  cases' b with b hb
  simp
  congr
  · rw [Nat.div_eq_iff]
    fconstructor
    · grind
    · omega
    · omega
  · exact mod_eq_of_lt hb
