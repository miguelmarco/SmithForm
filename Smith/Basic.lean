import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

variable {m n : ℕ}
variable {R : Type} [ED : EuclideanDomain R] [DecidableEq R] [DecidableRel ED.r]

open Matrix Nat

abbrev Mat (n m : ℕ) (R : Type):= Matrix (Fin n) (Fin m) R

def AM (i j : Fin n) (d : R) : Mat n n R := fun a b =>
  if a = i then
    if a = b then 1
    else if b = j then d
    else 0
  else
    if a = b then 1
  else 0

@[simp]
lemma def_AM_left (M : Mat n m R) (i j : Fin n) (d : R) (a : Fin n) (b : Fin m) (h : i ≠ j):
    (AM i j d * M) a b =
    if a = j then
      M a b  +  d * M i b
    else
      M a b
  := by
  simp [AM, Matrix.mul_apply]


def Mp (i j : Fin n) : Mat n n R := fun a b =>
  if a = j then (if b = i then 1 else 0) else
    if a = i then (if b = j then 1 else 0) else
      if a = b then 1 else 0

theorem Mp_inversa (i j : Fin n) : (Mp i j : Mat n n R) * (Mp i j : Mat n n R) = 1 := by
  ext a b
  simp [Mp,Matrix.mul_apply,Matrix.map_natCast,Matrix.ofNat_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  · cases h1
    cases h2
    cases h3
    simp only [ite_self, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, one_apply_eq]
  · cases h1
    cases h2
    simp only [ite_self, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have h4 : ¬ j = i := by grind
    rfl
  · grind
  · cases h1
    cases h4
    simp
  · cases h1
    cases h6
    simp [h4]
    rw [Finset.sum_eq_zero]
    · intro x hx
      split_ifs with h1 h2 h3 h4
      · grind
      · rfl
      · rfl
  · cases h1
    simp [h4]
    rw [Finset.sum_eq_zero]
    grind
  · cases h7
    cases h8
    simp [h1]
    rw [Finset.sum_eq_add j i]
    · simp
      grind
    · exact h1
    · intro c hc hc2
      grind
    · simp
    · simp
  · cases h7
    cases h9
    simp [h8]
  · cases h7
    simp [h8]
    rw [Finset.sum_eq_zero]
    · intro x hx
      grind
  · cases h10
    have haux : ¬ j = b := by grind
    simp [haux]
  · cases h11
    simp
    have haux : ¬ i = b := by grind
    simp [haux]
  · by_cases hab : a = b
    · cases hab
      simp
      rw [Finset.sum_eq_single a]
      simp [h7, h11]
      grind
      simp
    · simp [hab]
      rw [Finset.sum_eq_zero]
      grind

@[simp]
lemma def_Mp_mul_left (M : Mat n m R) (i j a: Fin n) (b : Fin m) :
    ((Mp i j : Mat n n R) * M) a b =
    if a = i then
      M j b
    else if a = j then
      M i b
    else
      M a b := by
  simp [Mp, Matrix.mul_apply]
  split_ifs with h1 h2 h3
  · grind
  · rfl
  · rfl
  · rfl

def RM : Mat n n R :=
  match n with
  | 0 => fun _ _ => 0
  | m + 1 => fun a b =>
    if  a = m then
      if b = 0 then 1 else 0
    else
      if b = a + 1 then 1 else 0

@[simp]
lemma def_RM_left (M : Mat n m R) (a : Fin n) (b : Fin m) :
    ((RM : Mat n n R) * M ) a b =
    if h : a = (n - 1) then
      M ⟨0,by grind⟩ b
    else
      M ⟨a + 1, by grind⟩ b := by
  simp [RM, Matrix.mul_apply]
  cases' n with n hn
  · simp
    split_ifs
    · cases' a with a ha
      grind
    · grind
  · simp
    split_ifs with h
    · rfl
    · congr
      rw [Fin.add_def]
      simp
      cases' a with a ha
      grind


def add_last_row_zeros (M : Mat n m R) : Mat (n + 1) m R :=
  fun a b =>
  if h : a = n then
    0
  else
    M ⟨a.1,by grind⟩ b

def remove_first_row (M : Mat (n + 1) m R) : Mat n m R :=
  fun ⟨a,ha⟩ b => M ⟨a + 1, by grind⟩ b

lemma remove_first_row_add_last_row (M : Mat (n + 1) m R) (hM : ∀ b, M 0 b = 0) :
    add_last_row_zeros (remove_first_row M)  = RM * M := by
  ext a b
  simp [add_last_row_zeros,remove_first_row]
  split_ifs with h1
  · rw [hM]
  · rfl

def add_last_column_zeros (M : Mat n m R) : Mat n (m + 1) R :=
  fun a b =>
  if h : b = m then
    0
  else
    M a ⟨b.1, by grind⟩

lemma mul_add_last_row (A : Mat n n R) (M : Mat n m R) :
    add_last_row_zeros (A * M) = (add_last_column_zeros (add_last_row_zeros A)) * (add_last_row_zeros M) := by
  ext a b
  simp [add_last_row_zeros,add_last_column_zeros, Matrix.mul_apply]
  split_ifs with h1
  · simp
  · rw [Fin.sum_univ_succ]
    simp
    split_ifs with h0
    · cases h0
      simp
    · let nn := n - 1
      let aa := (⟨a , by grind⟩ : Fin n)
      have haa : ⟨a, by grind⟩ = aa := rfl
      simp [haa]
      induction' n with n
      · grind
      · rw [Fin.sum_univ_succ]
        simp
        rw [Fin.sum_univ_castSucc]
        simp
        have haux : ∀ (x : Fin n), x.val ≠ n := by grind
        simp [haux]
        rfl

def find_next_pivot (M : Mat n m R) (i : ℕ) : ℕ :=
  if h0 : n = 0 then 0 else
  if h : i ≥ m then i
  else if (M ⟨0,by grind⟩ ⟨i, by grind⟩) ≠ 0 then i
  else find_next_pivot M (i + 1)

def find_first_pivot (M : Mat n m R) := find_next_pivot M 0

def coloca_pivot (M : Mat n m R) : Mat m m R :=
  let piv := find_first_pivot M
  if hm : m > 0 then
    if h : piv < m then
      Mp ⟨0,hm⟩ ⟨piv,h⟩
    else
      1
  else
    1

def reduce_first_row (M : Mat n m R) :
