import Smith.MatOperations

open AMat

set_option linter.style.cases false
set_option linter.flexible false

variable {m n l : ℕ}
variable {R : Type}

open Matrix Nat Array

namespace AMat

variable (A : Mat n m R) (B : Mat m l R)
variable [ED : EuclideanDomain R]
variable [DecidableEq R]


open Std.Do

set_option mvcgen.warning false

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

lemma first_nonzero_i_row_prop_2 (A : Mat n m R) (i b c: ℕ) (h : first_nonzero_i_row A i = some b) :
    ∀ (h : c < b), i ≤ c → Aget A ⟨i,by grind⟩ ⟨c,by grind⟩ = 0 := by
  have him := first_nonzero_i_row_inter A i b h
  suffices hsuf : first_nonzero_i_row A i = some b → ∀ (h : c < b), i ≤ c → Aget A ⟨i,by grind⟩ ⟨c,by grind⟩ = 0
  · apply hsuf h
  generalize hA : first_nonzero_i_row A i = res
  apply Id.of_wp_run_eq hA
  mvcgen invariants
  · Invariant.withEarlyReturn (onReturn := fun r letMuts =>
      ⌜r = some b → ∀ (h : c < b), i ≤ c → Aget A ⟨i, by grind⟩ ⟨c, by grind⟩ = 0⌝) (onContinue :=
      fun xs letMuts => ⌜(hxs : 0 < xs.suffix.length) →  ∀ d, (hd : d < (xs.current hxs)) → (i ≤ d) →  Aget A ⟨i, by grind⟩ ⟨d,by grind⟩ = 0⌝)
  with mleave
  · simp
  · expose_names
    right
    cases' h_4 with h4 h4
    · cases' h4 with h4 h5
      simp at h5
      simp
      intro hcur
      cases hcur
      apply h5
    · simp_all
  · simp_all
    expose_names
    intro hxs d hd
    cases' h_4 with h4 h5
    · by_cases hcas : d = cur
      · cases hcas
        intro
        exact h_3
      · apply h5
        have hcur' : cur ∈ cur :: suff := by simp
        rw [Std.Range.toList] at h_2
        simp at h_2
        rw  [RangeCursor.mem_suff i _ cur pref  (cur :: suff) h_2.symm ] at hcur'
        rw [List.append_cons] at h_2
        have hcur : cur ∈ pref ++ [cur] := by simp
        rw [RangeCursor.mem_preff _ _ _ _ _ h_2.symm] at hcur
        simp at hcur
        cases' hcur with hcur1 hcur2
        cases' hcur' with hcur3 hcur4
        have hsuf0 := RangeCursor.suffix0 i (m - i) _ _ h_2.symm hxs
        simp at hsuf0
        omega
  · simp_all
  · simp
  · simp_all

lemma first_nonzero_i_row_prop_3 (A : Mat n m R) (i : ℕ) (hi : i < n) (him : i < m)
    (h : first_nonzero_i_row A i = none)
  :
    ∀ d , (hdi : i ≤ d) → (hdm : d < m) → Aget A ⟨ i,hi⟩ ⟨d,hdm⟩ = 0 := by
  revert h
  generalize hA : first_nonzero_i_row A i = res
  apply Id.of_wp_run_eq hA
  mvcgen invariants
  · Invariant.withEarlyReturn
      (onReturn := fun r letMuts => ⌜∃ k : Fin m, (r = some k ∧ i ≤ k ∧ Aget A ⟨i,hi⟩ k ≠ 0)⌝)
      (onContinue :=  fun xs letMuts => ⌜∀ k, (hk : k ∈ xs.prefix) →
        Aget A ⟨i,hi⟩ ⟨k, by grind [RangeCursor.prefix_in_range]⟩ = 0⌝)
  with mleave
  · omega
  · simp_all
    grind
  · simp_all
    expose_names
    intro k hk
    cases' hk with hk hk
    · apply h_3.2
      exact hk
    · cases hk
      exact h_2
  · simp_all
  · expose_names
    simp [h_1] at h_2
    grind
  · simp_all
    expose_names
    choose k  hk hk2 using h_2
    grind

lemma first_nonzero_i_row_prop_if (A : Mat n m R) (i : ℕ) (hi : i < n) (him : i < m) (b : ℕ)
  (hbi : i ≤ b) (hbm : b < m)
  (h1 : Aget A ⟨i, hi⟩ ⟨b, hbm⟩ ≠ 0)
  (h2 : ∀ k, (hik : i ≤ k) → (hbk : k < b) → Aget A ⟨i, hi⟩ ⟨k, by grind⟩ = 0) :
    first_nonzero_i_row A i = some b := by
  by_cases hcas : first_nonzero_i_row A i = none
  · grind [first_nonzero_i_row_prop_3]
  · have haux : ∃ k, first_nonzero_i_row A i = some k
    · exact Option.ne_none_iff_exists'.mp hcas
    choose k hk using haux
    specialize h2 k (by grind)
    have haux := first_nonzero_i_row_prop_1 _ _ _ hk
    rw [hk]
    simp
    suffices hsuf : ¬ k < b ∧ ¬ b < k
    · omega
    fconstructor
    · grind
    · intro hbk
      have haux2 := first_nonzero_i_row_prop_2 A i k b hk hbk hbi
      grind

@[simp]
lemma first_nonzero_i_row_prop_some_iff (A : Mat n m R) (i : ℕ) (hi : i < n) (him : i < m) (b : ℕ) :
  first_nonzero_i_row A i = some b ↔
    i ≤ b ∧ b < m ∧
    ((hbm : b < m) →  (Aget A ⟨i, hi⟩ ⟨b, hbm⟩ ≠ 0 ∧ ∀ k, (hik : i ≤ k) → (hbk : k < b) →
      Aget A ⟨i, hi⟩ ⟨k, by grind⟩ = 0)) := by
  fconstructor
  · grind [first_nonzero_i_row_prop_1,first_nonzero_i_row_prop_2]
  · intro h1
    simp at h1
    rcases h1 with ⟨h1,h2,h3⟩
    simp [h2] at h3
    cases' h3 with h3 h4
    apply first_nonzero_i_row_prop_if
    all_goals assumption

@[simp]
lemma first_nonzero_i_row_prop_none_iff (A : Mat n m R) (i : ℕ) (hi : i < n) (him : i < m) :
    first_nonzero_i_row A i = none ↔
      ∀ k, (hik : i ≤ k) →  (hkm : k < m) → Aget A ⟨i, hi⟩ ⟨k, by grind⟩ = 0 := by
  fconstructor
  · apply first_nonzero_i_row_prop_3 _ _ _ him
  · intro h
    by_contra hneg
    have haux : ∃ b, first_nonzero_i_row A i = some b
    · rw [← @Option.ne_none_iff_exists']
      exact hneg
    choose b hb using haux
    grind [first_nonzero_i_row_prop_1]

def first_nonzero_i_col (A : Mat n m R) (i : ℕ) : Option ℕ := Id.run do
  if hi : n ≤ i ∨ m ≤ i then return none else
  let ki : Fin m := ⟨i,by simp at hi; tauto⟩
  for h : k in [i:n] do
    if Aget A ⟨k,Membership.get_elem_helper h rfl⟩ ki ≠ 0 then
      return some k
    else
      continue
  return none

@[grind →]
lemma first_nonzero_i_col_inter (A : Mat n m R) (i b : ℕ) :
    first_nonzero_i_col A i = some b → (i < n ∧ i < m ∧ i ≤ b ∧ b < n) := by
  generalize hA : first_nonzero_i_col A i = res
  apply Id.of_wp_run_eq hA
  mvcgen invariants
  · ⇓⟨xs, out⟩ => ⌜(out.1 = some (some b) →
        (i < n ∧ i < m ∧ i ≤ b ∧ b < n)) ∧ ∀ k_idx, k_idx ∈ xs.prefix → i ≤ k_idx⌝
  with mleave
  · tauto
  · expose_names
    simp_all
    fconstructor
    · intro hcur
      have haux : b ∈ [i:n].toList
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

lemma first_nonzero_i_col_prop_1 (A : Mat n m R) (i b : ℕ) (h : first_nonzero_i_col A i = some b) :
    Aget A ⟨b,by grind⟩ ⟨i,by grind⟩ ≠ 0 := by
  have him := first_nonzero_i_col_inter A i b h
  suffices hsuf : first_nonzero_i_col A i = some b → Aget A ⟨b,by grind⟩ ⟨i,by grind⟩ ≠ 0
  · apply hsuf h
  generalize hA : first_nonzero_i_col A i = res
  apply Id.of_wp_run_eq hA
  mvcgen invariants
  · ⇓⟨xs, out⟩ => ⌜(out.1 = some (some b) → Aget A ⟨b,by grind⟩ ⟨i,by grind⟩ ≠ 0)⌝
  with simp_all
  · grind

lemma first_nonzero_i_col_prop_2 (A : Mat n m R) (i b c : ℕ)
  (h : first_nonzero_i_col A i = some b) :
    ∀ (h : c < b), i ≤ c → Aget A ⟨c,by grind⟩ ⟨i,by grind⟩ = 0 := by
  have him := first_nonzero_i_col_inter A i b h
  suffices hsuf : first_nonzero_i_col A i = some b →
    ∀ (h : c < b), i ≤ c → Aget A ⟨c,by grind⟩ ⟨i,by grind⟩ = 0
  · apply hsuf h
  generalize hA : first_nonzero_i_col A i = res
  apply Id.of_wp_run_eq hA
  mvcgen invariants
  · Invariant.withEarlyReturn (onReturn := fun r letMuts =>
      ⌜r = some b → ∀ (h : c < b), i ≤ c → Aget A ⟨c, by grind⟩ ⟨i, by grind⟩ = 0⌝) (onContinue :=
      fun xs letMuts => ⌜(hxs : 0 < xs.suffix.length) →  ∀ d, (hd : d < (xs.current hxs)) →
        (i ≤ d) →  Aget A ⟨d, by grind⟩ ⟨i,by grind⟩ = 0⌝)
  with mleave
  · simp
  · expose_names
    right
    cases' h_4 with h4 h4
    · cases' h4 with h4 h5
      simp at h5
      simp
      intro hcur
      cases hcur
      apply h5
    · simp_all
  · simp_all
    expose_names
    intro hxs d hd
    cases' h_4 with h4 h5
    · by_cases hcas : d = cur
      · cases hcas
        intro
        exact h_3
      · apply h5
        have hcur' : cur ∈ cur :: suff := by simp
        rw [Std.Range.toList] at h_2
        simp at h_2
        rw  [RangeCursor.mem_suff i _ cur pref  (cur :: suff) h_2.symm ] at hcur'
        rw [List.append_cons] at h_2
        have hcur : cur ∈ pref ++ [cur] := by simp
        rw [RangeCursor.mem_preff _ _ _ _ _ h_2.symm] at hcur
        simp at hcur
        cases' hcur with hcur1 hcur2
        cases' hcur' with hcur3 hcur4
        have hsuf0 := RangeCursor.suffix0 i (n - i) _ _ h_2.symm hxs
        simp at hsuf0
        omega
  · simp_all
  · simp
  · simp_all

lemma first_nonzero_i_col_prop_3 (A : Mat n m R) (i : ℕ) (hi : i < n) (him : i < m)
    (h : first_nonzero_i_col A i = none)
  :
    ∀ d , (hdi : i ≤ d) → (hdm : d < n) → Aget A ⟨ d,hdm⟩ ⟨i,him⟩ = 0 := by
  revert h
  generalize hA : first_nonzero_i_col A i = res
  apply Id.of_wp_run_eq hA
  mvcgen invariants
  · Invariant.withEarlyReturn
      (onReturn := fun r letMuts => ⌜∃ k : Fin n, (r = some k ∧ i ≤ k ∧ Aget A k ⟨i,him⟩ ≠ 0)⌝)
      (onContinue :=  fun xs letMuts => ⌜∀ k, (hk : k ∈ xs.prefix) →
        Aget A ⟨k, by grind [RangeCursor.prefix_in_range]⟩ ⟨i,him⟩  = 0⌝)
  with mleave
  · omega
  · simp_all
    grind
  · simp_all
    expose_names
    intro k hk
    cases' hk with hk hk
    · apply h_3.2
      exact hk
    · cases hk
      exact h_2
  · simp_all
  · expose_names
    simp [h_1] at h_2
    grind
  · simp_all
    expose_names
    choose k  hk hk2 using h_2
    grind


lemma first_nonzero_i_col_prop_if (A : Mat n m R) (i : ℕ) (hi : i < n) (him : i < m) (b : ℕ)
  (hbi : i ≤ b) (hbm : b < n)
  (h1 : Aget A ⟨b, hbm⟩ ⟨i,him⟩ ≠ 0)
  (h2 : ∀ k, (hik : i ≤ k) → (hbk : k < b) → Aget A ⟨k, by grind⟩ ⟨i, him⟩ = 0) :
    first_nonzero_i_col A i = some b := by
  by_cases hcas : first_nonzero_i_col A i = none
  · grind [first_nonzero_i_col_prop_3]
  · have haux : ∃ k, first_nonzero_i_col A i = some k
    · exact Option.ne_none_iff_exists'.mp hcas
    choose k hk using haux
    specialize h2 k (by grind)
    have haux := first_nonzero_i_col_prop_1 _ _ _ hk
    rw [hk]
    simp
    suffices hsuf : ¬ k < b ∧ ¬ b < k
    · omega
    fconstructor
    · grind
    · intro hbk
      have haux2 := first_nonzero_i_col_prop_2 A i k b hk hbk hbi
      grind

@[simp]
lemma first_nonzero_i_col_prop_some_iff (A : Mat n m R) (i : ℕ) (hi : i < n) (him : i < m) (b : ℕ) :
  first_nonzero_i_col A i = some b ↔
    i ≤ b ∧  b < n ∧
    ((hbm : b < n) →  (Aget A ⟨b, hbm⟩ ⟨i, him⟩ ≠ 0 ∧ ∀ k, (hik : i ≤ k) → (hbk : k < b) →
      Aget A ⟨k, by grind⟩  ⟨i, him⟩ = 0)) := by
  fconstructor
  · grind [first_nonzero_i_col_prop_1,first_nonzero_i_col_prop_2]
  · intro h1
    simp at h1
    rcases h1 with ⟨h1,h2,h3⟩
    simp [h2] at h3
    cases' h3 with h3 h4
    apply first_nonzero_i_col_prop_if
    all_goals assumption

@[simp]
lemma first_nonzero_i_col_prop_none_iff (A : Mat n m R) (i : ℕ) (hi : i < n) (him : i < m) :
    first_nonzero_i_col A i = none ↔
     ∀ k, (hik : i ≤ k) →  (hkm : k < n) → Aget A ⟨k,hkm⟩ ⟨i,him⟩ = 0 := by
  fconstructor
  · grind [first_nonzero_i_col_prop_3]
  · intro h
    by_contra hneg
    have haux : ∃ b, first_nonzero_i_col A i = some b
    · rw [← @Option.ne_none_iff_exists']
      exact hneg
    choose b hb using haux
    grind [first_nonzero_i_col_prop_1]

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
    · simp only [mul_one, neg_neg]
      exact hc
    · grind [EuclideanDomain.gcd_eq_zero_iff]
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
        · rw [neg_mul,neg_mul]
          rw [mul_comm _ x,EuclideanDomain.mul_div_assoc]
          simp
        · simp
      rw [haux,ha,hb,hy]
      nth_rewrite 1 [hx]
      ring

@[grind =]
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

@[grind =]
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
lemma reduce_rows_gcd (A : Mat n m R) (i j : Fin n) (k : Fin m) :
    Aget (reduce_rows A i j k) i k = gcd (Aget A i k) (Aget A j k) := by
  simp [reduce_rows,def_lincom_rows,EuclideanDomain.gcd_eq_gcd_ab]
  ring

@[grind =]
lemma reduce_rows_zero (A : Mat n m R) (i j : Fin n) (k : Fin m) (hij : i ≠ j) :
    Aget (reduce_rows A i j k) j k = 0 := by
  have haux : j ≠ i := by tauto
  simp [reduce_rows,def_lincom_rows,haux,xgcdcompzero]

@[grind =]
lemma reduce_rows_other (A : Mat n m R) (i j : Fin n) (k : Fin m) (a : Fin n) (b : Fin m)
  (hai : a ≠ i) (haj : a ≠ j) :
    Aget (reduce_rows A i j k) a b = Aget A a b := by
  simp [reduce_rows,def_lincom_rows,hai,haj]

@[simp]
lemma reduce_cols_gcd (A : Mat n m R) (i j : Fin m) (k : Fin n) :
    Aget (reduce_cols A i j k) k i = gcd (Aget A k i) (Aget A k j) := by
  simp [reduce_cols,def_lincom_cols,EuclideanDomain.gcd_eq_gcd_ab]
  ring

@[grind =]
lemma  reduce_cols_zero (A : Mat n m R) (i j : Fin m) (k : Fin n) (hij : i ≠ j) :
    Aget (reduce_cols A i j k) k j = 0 := by
  have haux : j ≠ i := by tauto
  simp [reduce_cols,def_lincom_cols,haux,xgcdcompzero]

@[grind =]
lemma reduce_cols_other (A : Mat n m R) (i j : Fin m) (k : Fin n) (a : Fin n) (b : Fin m)
  (hbi : b ≠ i) (hbj : b ≠ j) :
    Aget (reduce_cols A i j k) a b = Aget A a b := by
  simp [reduce_cols,def_lincom_cols,hbi,hbj]

@[grind =]
lemma lincom_mul (A : Mat n m R) (B : Mat m l R) (i j : Fin m) (u v x y : R) (hij : i ≠ j)
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

lemma def_LUM_lincom_cols (D : LUM A) (i j : Fin m) (u v x y : R) (hij : i ≠ j) (h : u * y - v * x = 1) (a : Fin n) (b : Fin m) :
    Aget (LUM_lincom_cols A D i j u v x y hij h).M a b =
      if b = i then
        u * Aget D.M a i + v * Aget D.M a j
      else if b = j then
        x * Aget D.M a i + y * Aget D.M a j
      else
        Aget D.M a b := by
  simp [LUM_lincom_cols,def_lincom_cols]

lemma def_LUM_lincom_rows (D : LUM A) (i j : Fin n) (u v x y : R) (hij : i ≠ j) (h : u * y - v * x = 1) (a : Fin n) (b : Fin m) :
    Aget (LUM_lincom_rows A D i j u v x y hij h).M a b =
      if a = i then
        u * Aget D.M i b + v * Aget D.M j b
      else if a = j then
        x * Aget D.M i b + y * Aget D.M j b
      else
        Aget D.M a b := by
  simp [LUM_lincom_rows,def_lincom_rows]

def M : Mat 2 3 ℤ where
  Ar := #[3,0,5,6,7,8]
  hAr := by simp

def clean_row (A: Mat n m R) (i : ℕ) (hin : i < n) : Mat n m R := Id.run do
  match hb : first_nonzero_i_row A i with
  | none => return A
  | some b =>
    let mut res := A
    for h : k in [b + 1:m] do
      if Aget A ⟨i,hin⟩ ⟨k,Membership.get_elem_helper h rfl⟩ = 0
      then
        continue
      else
        res := reduce_cols res ⟨b,by grind⟩ ⟨k, Membership.get_elem_helper h rfl⟩ ⟨i,hin⟩
    return res

#eval M
#eval clean_row M 0 (by omega)



variable [DecidableRel ED.r]

end AMat
