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
    simp only [mod_eq_zero, h, ↓reduceDIte]
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

def transform_diagonal_dvd (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m) (hjn : j < n)
  (hjm : j < m) (hij : i ≠ j)(h : Aget D.M ⟨i, hin⟩ ⟨i, him⟩ ≠ 0) : LUM A :=
  let x := Aget D.M ⟨i,hin⟩ ⟨i,him⟩
  let y := Aget D.M ⟨j,hjn⟩ ⟨j,hjm⟩
  let a := gcdA x y
  let b := gcdB x y
  let g := gcd x y
  let u := -xgcdcompu x y
  let v := xgcdcompv x y
  let D1 := LUM_lincom_rows _ D ⟨i,hin⟩ ⟨j,hjn⟩ 1 1 (b * -u) (a * v) (by simp [hij])
     (by simp [a,b,u,v]; apply xgcdcompone; simp [x,h])
  LUM_lincom_cols _ D1 ⟨i,him⟩ ⟨j,hjm⟩  a (b) (-u) v (by simp [hij])
     (by simp [a,b,v,u];  rw [← (xgcdcompone x y (by simp [x,h]))])

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

lemma transform_diagonal_fix (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m) (hjn : j < n)
  (hjm : j < m) (hij : i ≠ j) (h : Aget D.M ⟨i, hin⟩ ⟨i, him⟩ ≠ 0) (r : Fin n) (c : Fin m)
  (hd : is_diagonal _ D) (hne : ¬((r.1 = i ∧ c.1 = i ) ∨ (r.1 = j ∧ c.1 = j))) :
    Aget (transform_diagonal_dvd _ D i j hin him hjn hjm hij h).M r c = Aget D.M r c := by
  by_cases hcas : r.1 ≠ c.1
  · rw [hd]
    · rw [transform_diagonal_diagonal]
      · exact hd
      · exact hcas
    · exact hcas
  simp [transform_diagonal_dvd,def_LUM_lincom_cols,def_LUM_lincom_rows]
  push_neg at hne
  cases' hne with hne1 hne2
  split_ifs
  any_goals grind

lemma transform_diagonal_gcd (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m) (hjn : j < n)
  (hjm : j < m) (hij : i ≠ j) (h : Aget D.M ⟨i, hin⟩ ⟨i, him⟩ ≠ 0) (hd : is_diagonal _ D) :
    Aget (transform_diagonal_dvd _ D i j hin him hjn hjm hij h).M ⟨i,hin⟩ ⟨i,him⟩ =
      gcd (Aget D.M ⟨i,hin⟩ ⟨i,him⟩) (Aget D.M ⟨j,hjn⟩ ⟨j,hjm⟩) := by
  simp [transform_diagonal_dvd,def_LUM_lincom_cols,def_LUM_lincom_rows]
  nth_rewrite 1 [EuclideanDomain.gcd_eq_gcd_ab]
  simp [hd,hij,hij.symm]
  ring

lemma transform_diagonal_lcm (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m) (hjn : j < n)
  (hjm : j < m) (hij : i ≠ j) (h : Aget D.M ⟨i, hin⟩ ⟨i, him⟩ ≠ 0) (hd : is_diagonal _ D) :
    Aget (transform_diagonal_dvd _ D i j hin him hjn hjm hij h).M ⟨j,hjn⟩ ⟨j,hjm⟩ =
      lcm (Aget D.M ⟨i,hin⟩ ⟨i,him⟩) (Aget D.M ⟨j,hjn⟩ ⟨j,hjm⟩) := by
  simp [transform_diagonal_dvd,def_LUM_lincom_cols,def_LUM_lincom_rows,hd,hij,hij.symm,
    EuclideanDomain.lcm]
  generalize hx : (Aget D.M ⟨i, hin⟩ ⟨i, him⟩) = x
  generalize hy : (Aget D.M ⟨j, hjn⟩ ⟨j, hjm⟩) = y
  have haux := def_xgcdcompu x y
  have haux2 := def_xgcdcompv x y
  have hgcd : gcd x y ≠ 0
  · intro hneg
    apply h
    rw [hx]
    have hauxg := gcd_dvd_left x y
    simp [hneg] at hauxg
    exact hauxg
  nth_rewrite  8 [haux]
  rw [EuclideanDomain.mul_div_assoc x ,EuclideanDomain.mul_div_assoc (-xgcdcompu x y)]
  · simp [hgcd]
    nth_rewrite 8 [haux2]
    ring_nf
    have hux3 := xgcdcompone x y
    grind
  · simp
  · simp

def transform_diagonal (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m) (hjn : j < n)
  (hjm : j < m) (hij : i ≠ j) : LUM A :=
  if h : Aget D.M ⟨i,hin⟩ ⟨i,him⟩ = 0 then
    if Aget D.M ⟨j,hjn⟩ ⟨j,hjm⟩ = 0 then
      D
    else
      LUM_swap_row _ (LUM_swap_col _ D ⟨i,him⟩ ⟨j,hjm⟩) ⟨i,hin⟩ ⟨j,hjn⟩
  else
    transform_diagonal_dvd _ D i j hin him hjn hjm hij h

lemma transform_diagonal_diagonal' (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m) (hjn : j < n)
  (hjm : j < m) (hij : i ≠ j) (hd : is_diagonal _ D) :
    is_diagonal _ (transform_diagonal _ D i j hin him hjn hjm hij) := by
  unfold transform_diagonal
  split_ifs with hi1 hi2
  · exact hd
  · intro r c hrc
    simp [LUM_swap_row,LUM_swap_col,def_swap_row,def_swap_col]
    split_ifs
    any_goals grind
  · apply transform_diagonal_diagonal
    any_goals tauto

lemma transform_diagonal_fix' (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m) (hjn : j < n)
  (hjm : j < m) (hij : i ≠ j) (r : Fin n) (c : Fin m)
  (hd : is_diagonal _ D) (hne : ¬((r.1 = i ∧ c.1 = i ) ∨ (r.1 = j ∧ c.1 = j))) :
    Aget (transform_diagonal _ D i j hin him hjn hjm hij).M r c = Aget D.M r c := by
  unfold transform_diagonal
  split_ifs with hi1 hi2
  · rfl
  · simp [LUM_swap_row,LUM_swap_col,def_swap_row,def_swap_col]
    split_ifs
    any_goals grind
  · apply transform_diagonal_fix
    any_goals tauto

lemma transform_diagonal_gcd' (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m) (hjn : j < n)
  (hjm : j < m) (hij : i ≠ j) (hd : is_diagonal _ D) :
    Aget (transform_diagonal _ D i j hin him hjn hjm hij).M ⟨i,hin⟩ ⟨i,him⟩ =
      gcd (Aget D.M ⟨i,hin⟩ ⟨i,him⟩) (Aget D.M ⟨j,hjn⟩ ⟨j,hjm⟩) := by
  unfold transform_diagonal
  split_ifs with hi1 hi2
  · simp [hi1,hi2]
  · simp [LUM_swap_col,LUM_swap_row,def_swap_col,def_swap_row]
    simp [hi1]
  · apply transform_diagonal_gcd
    any_goals tauto

lemma transform_diagonal_lcm' (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m) (hjn : j < n)
  (hjm : j < m) (hij : i ≠ j) (hd : is_diagonal _ D) :
    Aget (transform_diagonal _ D i j hin him hjn hjm hij).M ⟨j,hjn⟩ ⟨j,hjm⟩ =
      lcm (Aget D.M ⟨i,hin⟩ ⟨i,him⟩) (Aget D.M ⟨j,hjn⟩ ⟨j,hjm⟩) := by
  unfold transform_diagonal
  split_ifs with hi1 hi2
  · simp [hi1,hi2]
  · simp [LUM_swap_col,LUM_swap_row,def_swap_col,def_swap_row]
    split_ifs
    · tauto
    · simp [hi1]
  · apply transform_diagonal_lcm
    any_goals tauto

def fix_diagonal_aux (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m): LUM A := Id.run do
  let mut result := D
  let mi := min n m
  for hj : j in [i+1 : mi] do
    let Ai := Aget result.M ⟨i,hin⟩ ⟨i,him⟩
    let Aj := Aget result.M ⟨j,by simp [mi] at hj; omega⟩ ⟨j,by simp [mi] at hj; omega⟩
    if Aj % Ai ≠ 0 then do
      result := transform_diagonal _ result i j hin him (by simp [mi] at hj; omega)
        (by simp [mi] at hj; omega) (by simp at hj; omega)
    else
      continue
  return result

lemma fix_diagonal_aux_prop (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m) (hd : is_diagonal _ D) :
    (is_diagonal _ (fix_diagonal_aux _ D i hin him))  ∧
    ∀ j, (j > i) → (hjn : j < n) → (hjm : j < m) →
    (Aget (fix_diagonal_aux _ D i hin him).M ⟨i,hin⟩ ⟨i,him⟩ ∣ Aget (fix_diagonal_aux _ D i hin him).M ⟨j,hjn⟩ ⟨j,hjm⟩) := by
  generalize h : fix_diagonal_aux _ D i hin him = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, res⟩ => ⌜is_diagonal _ res ∧ ∀ j, (hj : j ∈ xs.prefix)  → Aget res.M ⟨i,hin⟩ ⟨i,him⟩ ∣
      Aget res.M
        ⟨j,by expose_names; simp [mi] at xs; have haux := RangeCursor.prefix_in_range _ _ j xs hj; omega⟩
        ⟨j,by expose_names; simp [mi] at xs; have haux := RangeCursor.prefix_in_range _ _ j xs hj; omega⟩⌝
  with mleave
  any_goals simp_all
  · expose_names
    fconstructor
    · apply transform_diagonal_diagonal'
      exact h_3.1
    · intro j hj
      cases' hj with hj hj
      · rw [transform_diagonal_gcd',transform_diagonal_fix']
        apply dvd_trans (EuclideanDomain.gcd_dvd_left _ _)
        apply h_3.2
        exact hj
        exact h_3.1
        · simp
          have haux := RangeCursor.prefix_in_tolist h_1 hj
          simp [mi] at haux
          omega
        · exact h_3.1
      · cases hj
        rw [transform_diagonal_gcd',transform_diagonal_lcm']
        · apply dvd_trans (EuclideanDomain.gcd_dvd_left _  _ ) (EuclideanDomain.dvd_lcm_left _ _ )
        · exact h_3.1
        · exact h_3.1
  · expose_names
    fconstructor
    · exact h_3.1
    · intro j hj
      cases' hj  with hj hj
      · apply h_3.2
        exact hj
      · cases hj
        simp [Ai,Aj] at h_2
        exact h_2
  · assumption
  · expose_names
    fconstructor
    · apply h_1.1
    · intro j hji hjn hjm
      apply h_1.2
      any_goals omega

lemma fix_diagonal_aux_prev (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m)  (hij : j < i)
  (hd : is_diagonal _ D) :
    Aget (fix_diagonal_aux _ D i hin him).M ⟨j,by omega⟩ ⟨j,by omega⟩ =
      Aget D.M ⟨j,by omega⟩ ⟨j,by omega⟩ := by
  generalize h : (fix_diagonal_aux A D i hin him) = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ => ⌜is_diagonal _ letMuts ∧
    Aget letMuts.M ⟨j, by omega⟩ ⟨j, by omega⟩ = Aget D.M ⟨j, by omega⟩ ⟨j, by omega⟩⌝
  with mleave
  · expose_names
    fconstructor
    · apply transform_diagonal_diagonal'
      exact h_3.1
    · rw [transform_diagonal_fix']
      · exact h_3.2
      · exact h_3.1
      · simp
        fconstructor
        · omega
        · intro hn
          have haux := RangeCursor.current_in_tolist h_1
          simp [mi] at haux
          omega
  · expose_names
    apply h_1.2

lemma fix_diagonal_aux_prev_dvd (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m)  (hij : j < i)
  (hd : is_diagonal _ D) (hjdv : ∀ k, (hik : k ≥ i) → (hkn : k < n) → (hkm : k < m) →
  Aget D.M ⟨j,by omega⟩ ⟨j,by omega⟩ ∣ Aget (D).M ⟨k,hkn⟩ ⟨k,hkm⟩ ):
     ∀ k, (hik : k ≥ i) → (hkn : k < n) → (hkm : k < m) →
    Aget D.M ⟨j,by omega⟩ ⟨j,by omega⟩ ∣ Aget (fix_diagonal_aux _ D i hin him).M ⟨k,hkn⟩ ⟨k,hkm⟩  := by
  generalize h : (fix_diagonal_aux _ D i hin him) = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ =>
    ⌜is_diagonal _ letMuts ∧
          ∀ (k : ℕ) (hik : k ≥ i) (hkn : k < n) (hkm : k < m),
            Aget D.M ⟨j, by omega⟩ ⟨j,by omega⟩ ∣ Aget letMuts.M ⟨k, hkn⟩ ⟨k, hkm⟩⌝
  with mleave
  · expose_names
    cases' h_3 with h3 h4
    fconstructor
    · apply transform_diagonal_diagonal'
      exact h3
    · intro k hki hkn hkm
      by_cases hcas : k = cur
      · cases hcas
        rw [transform_diagonal_lcm']
        · apply dvd_trans ?_  (EuclideanDomain.dvd_lcm_left _ _ )
          apply h4
          omega
        exact h3
      · by_cases hcas2 : k = i
        · cases hcas2
          rw [transform_diagonal_gcd']
          · apply EuclideanDomain.dvd_gcd
            · apply h4
              simp
            · apply h4
              have haux := RangeCursor.current_in_tolist h_1
              omega
          · exact h3
        · rw [transform_diagonal_fix']
          · apply h4
            exact hki
          · exact h3
          · simp
            simp [hcas]
            exact hcas2
  · expose_names
    cases' h_1 with h1 h2
    apply h2

lemma fix_diagonal_aux_pivot (D : LUM A) (i j : ℕ) (hin : i < n) (him : i < m)
  (hd : is_diagonal _ D) :
    Aget (fix_diagonal_aux _ D i hin him).M ⟨i,hin⟩ ⟨i,him⟩ ∣
      Aget D.M ⟨i,hin⟩ ⟨i,him⟩ := by
  generalize h : (fix_diagonal_aux A D i hin him) = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ => ⌜is_diagonal _ letMuts ∧
    Aget letMuts.M ⟨i,hin⟩ ⟨i,him⟩ ∣ Aget D.M ⟨i,hin⟩ ⟨i,him⟩⌝
  with mleave
  · expose_names
    fconstructor
    · apply transform_diagonal_diagonal'
      exact h_3.1
    · rw [transform_diagonal_gcd']
      · apply dvd_trans (EuclideanDomain.gcd_dvd_left _ _ ) h_3.2
      · exact h_3.1
  · expose_names
    apply h_1.2

def fix_diagonal (D : LUM A) : LUM A := Id.run do
  let mut result := D
  let mi := min n m
  for hi : i in [0:mi - 1] do
    result := fix_diagonal_aux _ result i (by simp [mi] at hi; omega) (by simp [mi] at hi; omega)
  return result

lemma fix_diagonal_diagonal (D : LUM A) (hd : is_diagonal _ D) :
    is_diagonal _ (fix_diagonal _ D) := by
  generalize h : fix_diagonal _ D = res
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ => ⌜is_diagonal A letMuts⌝
  with mleave
  · expose_names
    have haux := fix_diagonal_aux_prop _ b cur ?_ ?_ h_2
    · apply haux.1
      · have haux : cur ∈ [:mi - 1].toList
        · rw [h_1]
          simp
        simp [mi] at haux
        omega
      · have haux : cur ∈ [:mi - 1].toList
        · rw [h_1]
          simp
        simp [mi] at haux
        omega

lemma fix_diagonal_dvd (D : LUM A) (hd : is_diagonal _ D) :
  ∀ (i j : ℕ), (hin : i < n) → (him : i < m) → (hjn : j < n) → (hjm : j < m) → (hij : i < j) →
    (Aget (fix_diagonal _ D).M ⟨i,hin⟩ ⟨i,him⟩)∣ (Aget (fix_diagonal _ D).M ⟨j,hjn⟩ ⟨j,hjm⟩) := by
  generalize h : fix_diagonal _ D = result
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, res⟩ => ⌜(is_diagonal _ res) ∧ ∀ i, (hi : i ∈ xs.prefix) →
     ∀ j, (hij : j > i) → (hjn : j < n) → (hjm : j < m) →
    Aget res.M ⟨i, by omega⟩ ⟨i, by omega⟩ ∣ Aget res.M ⟨j,hjn⟩ ⟨j,hjm⟩⌝
  with mleave
  · expose_names
    have hcur : cur < mi
    · suffices hsuf : cur ∈ [:mi-1].toList
      · simp at hsuf
        omega
      simp [h_1]
    simp [mi] at hcur
    fconstructor
    · have haux := fix_diagonal_aux_prop _ b cur hcur.1 hcur.2  h_2.1
      exact haux.1
    · intro i hi
      simp at hi
      cases' hi with hi hi
      · intro j hj hjn hjm
        rw [fix_diagonal_aux_prev]
        · by_cases hcas : j ≥ cur
          · apply fix_diagonal_aux_prev_dvd
            · exact h_2.1
            · intro k hk hkn hkm
              apply h_2.2
              · exact hi
              · have haux := RangeCursor.prefix_in_tolist h_1 hi
                omega
            · exact hcas
            · have haux := RangeCursor.prefix_in_tolist h_1 hi
              omega
          · simp at hcas
            rw [fix_diagonal_aux_prev]
            · apply h_2.2
              exact hi
              exact hj
            · exact hcas
            · exact h_2.1
        · have haux := RangeCursor.prefix_in_tolist h_1 hi
          omega
        · exact h_2.1
      · cases hi
        intro j hjc hjn hjm
        have haux :=  fix_diagonal_aux_prop _ b cur (by omega) (by omega) h_2.1
        apply haux.2
        exact hjc
  · simp
    exact hd
  · expose_names
    cases' h_1 with h1 h2
    intro i j hin him hjn hjm hij
    apply h2
    · simp [mi]
      omega
    · assumption

def SmithForm (A : Mat n m R) : LUM A := fix_diagonal A (diagonalize A (triv_LUM A))

end AMat
