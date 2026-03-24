import Smith.MatArray

set_option linter.style.cases false
set_option linter.flexible false

variable {m n l : ℕ}
variable {R : Type} [ED : EuclideanDomain R]

open Matrix Nat Array Std.Do AMat

namespace AMat

variable (A : Mat n m R)
variable [DecidableEq R]

set_option mvcgen.warning false
set_option linter.unusedTactic false

open EuclideanDomain

def pivotize (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m) : LUM A :=
  let v := Aget D.M ⟨i,hin⟩ ⟨i,him⟩
  let S := clean_row_column _ D i hin him
  if hcond : (Aget S.M ⟨i,hin⟩ ⟨i,him⟩) % v = 0 then
    S
  else
    pivotize S i hin him
termination_by Aget D.M ⟨i,hin⟩ ⟨i,him⟩
decreasing_by
  simp [LT.lt]
  fconstructor
  · exact clean_row_column_dvd A D i hin him
  · simp [v,S] at hcond
    exact hcond

lemma pivotize_prop (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m) :
    (∀ (c : Fin m), c > i → Aget (pivotize _ D i hin him).M ⟨i,hin⟩ c = 0) ∧
    (∀ (c : Fin n), c > i → Aget (pivotize _ D i hin him).M c ⟨i,him⟩ = 0) := by
  induction D using pivotize.induct
  · exact i
  · exact hin
  · exact him
  · expose_names
    rw [pivotize]
    simp [v,S,h]
    apply clean_row_column_d_finish
    simp [S,v] at h
    exact h
  · expose_names
    rw [pivotize.eq_def]
    simp [v,S] at h
    simp [h]
    exact ih1

lemma pivotize_others (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m) (p : ℕ) (hp : p < i)
  (hc : ∀ (c : Fin n), c > p → Aget D.M c ⟨p, by grind⟩ = 0)
  (hr : ∀ (c : Fin m), c > p → Aget D.M ⟨p, by grind⟩ c = 0) :
    (∀ (c : Fin n), c > p → Aget (pivotize _ D i hin him).M c ⟨p,by grind⟩ = 0) ∧
    (∀ (c : Fin m), c > p → Aget (pivotize _ D i hin him).M ⟨p,by grind⟩ c = 0) := by
  induction D using pivotize.induct
  · exact i
  · exact hin
  · exact him
  · expose_names
    rw [pivotize]
    simp [v,S,h]
    apply clean_row_column_others
    · exact hc
    · exact hr
    exact hp
  · expose_names
    rw [pivotize.eq_def]
    simp [v,S] at h
    simp only [ge_iff_le, mod_eq_zero, h, ↓reduceDIte]
    have haux := clean_row_column_others  _ _ i hin him p hp hc hr
    apply ih1
    · simp [S]
      apply haux.1
    · simp [S]
      apply haux.2

def diagonalize (D : LUM A) : LUM A := Id.run do
  let mut res := D
  let mi := min n m
  for hi : i in [0:mi] do
    res := pivotize _ res i (by simp [mi] at hi; exact hi.1) (by simp [mi] at hi; exact hi.2)
  return res

abbrev is_diagonal (D : LUM A) :=
  ∀ (r : Fin n) (c : Fin m), r.1 ≠ c.1 → Aget (D).M r c = 0

lemma diagonalize_prop_rows (D : LUM A) :
    is_diagonal _ (diagonalize _ D) := by
  suffices hsuf : ∀ i, (hin : i < n) → (him : i < m) → ((∀ (c : Fin m), (hci : c > i) →
   ( Aget (diagonalize _ D).M ⟨i,hin⟩  c = 0))
  ∧ (∀ (c : Fin n), (hci : c > i) → Aget (diagonalize _ D).M c ⟨i,him⟩ = 0))
  · intro r c hrc
    rw [ne_iff_lt_or_gt] at hrc
    cases' hrc with hr hc
    · specialize hsuf r r.2 (by grind)
      apply hsuf.1
      exact hr
    · specialize hsuf c (by grind) c.2
      apply hsuf.2
      exact hc
  generalize h : diagonalize A D = result
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, res⟩ => ⌜∀ i, (hi : i ∈ xs.prefix) →
      ((∀ (c : Fin n), (hci : c > i) →
        Aget res.M c ⟨i,lt_of_lt_of_le (RangeCursor.prefix_in_range 0 _ i xs hi).2
          (min_le_right n m)⟩ = 0) ∧
        (∀ (c : Fin m), (hci : c > i) →
          (Aget res.M ⟨i,lt_of_lt_of_le (RangeCursor.prefix_in_range 0 _ i xs hi).2
            (min_le_left n m)⟩  c = 0)))⌝
  with mleave
  · expose_names
    intro i hi
    simp at hi
    cases' hi with hi hi
    · specialize h_2 i hi
      cases' h_2 with hc hr
      apply pivotize_others
      · apply hc
      · apply hr
      · grind
    · cases hi
      rw [and_comm]
      apply pivotize_prop
  · simp
  · expose_names
    intro i hin him
    specialize h_1 i ?_
    · simp [mi,hin,him]
    rw [and_comm]
    apply h_1

open EuclideanDomain

def transform_diagonal_dvd (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m) (hjn : j < n) (hjm : j < m) (hij : i ≠ j)
  (h : Aget D.M ⟨i, hin⟩ ⟨i, him⟩ ≠ 0)
  : LUM A :=
  let x := Aget D.M ⟨i,hin⟩ ⟨i,him⟩
  let y := Aget D.M ⟨j,hjn⟩ ⟨j,hjm⟩
  let a := gcdA x y
  let b := gcdB x y
  let g := gcd x y
  let u := -xgcdcompu x y
  let v := xgcdcompv x y
  let D1 := LUM_lincom_rows _ D ⟨i,hin⟩ ⟨j,hjn⟩ 1 1 (b * -u) (a * v) (by simp [hij]) (by simp [a,b,u,v]; apply xgcdcompone; simp [x,h])
  LUM_lincom_cols _ D1 ⟨i,him⟩ ⟨j,hjm⟩  a (b) (-u) v (by simp [hij]) (by simp [a,b,v,u];  rw [← (xgcdcompone x y (by simp [x,h]))])

lemma transform_diagonal_diagonal (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m) (hjn : j < n) (hjm : j < m) (hij : i ≠ j)
  (h : Aget D.M ⟨i, hin⟩ ⟨i, him⟩ ≠ 0) (hd : is_diagonal _ D) :
    is_diagonal _ (transform_diagonal_dvd _ D i j hin him hjn hjm hij h) := by
  simp [transform_diagonal_dvd,is_diagonal]
  intro r c hrc
  simp [def_LUM_lincom_cols,def_LUM_lincom_rows]
  split_ifs with hi1 hi2 hi3 hi4 hi5
  · grind
  · generalize hg1 : (Aget D.M ⟨i, hin⟩ ⟨i, him⟩) = x
    generalize hg2 : (Aget D.M ⟨j, hjn⟩ ⟨j, hjm⟩) = y
    rw [hd,hd]
    · simp [xgcdcompu,xgcdcompv]
      ring_nf
      rw [neg_div,mul_neg,neg_mul,← sub_eq_add_neg]
      simp [ED.mul_assoc ,← mul_sub]
      right
      right
      rw [mul_comm _ x, ←  EuclideanDomain.mul_div_assoc,  ←  EuclideanDomain.mul_div_assoc]
      · ring_nf
      · apply EuclideanDomain.gcd_dvd_right
      · apply EuclideanDomain.gcd_dvd_left
    · grind
    · grind
  · simp_all
    right
    apply hd
    grind
  · simp_all
    apply xgcdcompzero
  all_goals grind








end AMat
