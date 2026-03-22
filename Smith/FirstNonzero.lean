import Smith.MatOperations

open AMat

set_option linter.style.cases false
set_option linter.flexible false

variable {m n l : ℕ}
variable {R : Type}

open Matrix Nat Array

namespace AMat

open AMat

variable (A : Mat n m R)
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

lemma first_nonzero_i_row_prop_2 (A : Mat n m R) (i b c : ℕ)
  (h : first_nonzero_i_row A i = some b) :
    ∀ (h : c < b), i ≤ c → Aget A ⟨i,by grind⟩ ⟨c,by grind⟩ = 0 := by
  have him := first_nonzero_i_row_inter A i b h
  suffices hsuf : first_nonzero_i_row A i = some b →
    ∀ (h : c < b), i ≤ c → Aget A ⟨i,by grind⟩ ⟨c,by grind⟩ = 0
  · apply hsuf h
  generalize hA : first_nonzero_i_row A i = res
  apply Id.of_wp_run_eq hA
  mvcgen invariants
  · Invariant.withEarlyReturn (onReturn := fun r letMuts =>
      ⌜r = some b → ∀ (h : c < b), i ≤ c → Aget A ⟨i, by grind⟩ ⟨c, by grind⟩ = 0⌝) (onContinue :=
      fun xs letMuts => ⌜(hxs : 0 < xs.suffix.length) →  ∀ d, (hd : d < (xs.current hxs)) →
      (i ≤ d) →  Aget A ⟨i, by grind⟩ ⟨d,by grind⟩ = 0⌝)
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
  (h1 : Aget A ⟨b, hbm⟩ ⟨i, him⟩ ≠ 0)
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

end AMat
