import Mathlib.Tactic
import Std.Do

variable (i m k : ℕ) (xs : [i:m].toList.Cursor)

namespace RangeCursor

open List Std.Range

@[simp]
lemma mem_range : k ∈ [i:m].toList ↔ i ≤ k ∧ k < m := by
  grind

@[grind =]
lemma dropLastsum {α : Type} (P S : List α) (h : S ≠ []) :
    (P ++ S).dropLast = P ++ S.dropLast := dropLast_append_of_ne_nil h

@[grind →]
lemma mem_droplast {α : Type} (S : List α) (h : S ≠ []) (k : α) (hk : k ∈ S) :
    k ≠ S.getLast h → k ∈ (S.dropLast) := by
  revert k
  induction' S with x S hind
  · tauto
  · intro k hk hkl
    by_cases hcas : k = x
    · by_cases hcasS : S = []
      · simp [hcasS] at hkl
        tauto
      · rw [dropLast_cons_of_ne_nil hcasS]
        simp
        left
        exact hcas
    · simp [hcas] at hk
      specialize hind (by grind) k hk ?_
      · rw [getLast_cons (by grind)] at hkl
        exact hkl
      rw [dropLast_cons_of_ne_nil (by grind)]
      right
      exact hind


lemma range_succ : range' i ( m + 1) = [i] ++ range' (i + 1) m:= by
  rfl

@[simp]
lemma range_succ' : range' i ( m + 1) = (range' i m) ++ [i + m] := by
  revert i
  induction' m with m hm
  · simp
  · intro i
    rw [range_succ]
    nth_rewrite 2 [range_succ]
    simp [hm]
    ring

@[grind =]
lemma range_succ'' (h : i ≤ m) : [i:(m + 1)].toList = [i:m].toList ++ [m] := by
  unfold toList
  simp
  have haux : m + 1 - i = (m - i) + 1 := by omega
  rw [haux,range_succ']
  simp
  omega

lemma droplast_range' : (range' i (m + 1)).dropLast = range' i m := by
  simp


lemma mem_preff (P S : List ℕ ) (hPN : P ++ S = (range' i m)) : k ∈ P ↔ i ≤ k ∧ k < i + P.length := by
  revert P S hPN
  induction' m with m hind
  · intro P S hPN
    simp [range'] at hPN
    simp_all
  · intro P S hPS
    by_cases hcas : S = []
    · simp_all
      grind
    · specialize hind P S.dropLast ?_
      · have haux := dropLastsum  P S hcas
        rw [← haux]
        simp [hPS]
      exact hind


lemma preff_range (P S : List ℕ) (hPN : P ++ S = (range' i m)) : P = range' i P.length := by
  revert i m
  induction' P with x P hP
  · simp
  · intro i m hPN
    simp at hPN
    simp [-range_succ']
    rw [range']
    specialize hP (i + 1)
    have hm0 : 0 < m
    · by_contra hcon
      simp at hcon
      cases hcon
      simp at hPN
    simp
    fconstructor
    · cases' m with m
      · grind
      · rw [range'] at hPN
        simp at hPN
        exact hPN.1
    · cases' m with m
      · tauto
      · rw [range'] at hPN
        simp at hPN
        specialize hP m hPN.2
        exact hP

lemma mem_suff (P S : List ℕ ) (hPN : P ++ S = (range' i m)) : k ∈ S ↔ i + P.length ≤ k ∧ k < i + P.length + S.length := by
  revert P
  induction' S with x S hind
  · simp
  · intro P hP
    specialize hind (P ++ [x]) ?_
    · simp [hP]
    fconstructor
    · intro hkxS
      have h1 := mem_preff i m k _ _ hP
      have haux : (P ++ [x]) ++ S = range' i m
      · simp [hP]
      have h2 := mem_preff i m k _ _ haux
      have h3 : k ∈ range' i m
      · rw [← haux]
        grind
      simp at h3
      simp_all
      grind
    · intro h
      cases' h with h h2
      have h1 : k ∈ range' i m
      · simp_all
        grind
      rw [← hP] at h1
      simp at h1
      cases' h1 with h1 h1
      · rw [mem_preff i m k _ _ hP] at h1
        grind
      grind

lemma suffix0 (P S : List ℕ ) (hPN : P ++ S = (range' i m)) (h : 0 < S.length) : S[0]'(h) = i + P.length := by
  revert i m
  induction' P with x P hP
  · simp_all
  · intro i m hm
    cases' m with m
    · simp_all
    · cases' i with i
      · unfold range' at hm
        simp_all
        specialize hP 1
        ring_nf
        apply hP
        tauto
      · specialize hP (i + 2) m
        simp at hP ⊢
        ring_nf at hP ⊢
        apply hP
        have haux : 2 + i = (i + 1) + 1 := by ring
        unfold range' at hm
        simp at hm
        grind

@[grind =]
lemma mem_pref_cursor (xs : ([i:m].toList.Cursor)) (h : 0 < xs.suffix.length) :
    k ∈ xs.prefix ↔ i ≤ k ∧ k < xs.current h := by
  have haux := xs.property
  unfold Std.Range.toList at haux
  simp at haux
  rw [mem_preff i (m -i ) k xs.prefix xs.suffix  haux]
  unfold Cursor.current
  rw [suffix0 _ _ _ _ haux]

@[grind =]
lemma mem_suf_cursor  (xs : ([i:m].toList.Cursor)) (h : 0 < xs.suffix.length) :
    k ∈ xs.suffix ↔ xs.current h ≤ k ∧ k < m  := by
  have hPS := xs.property
  unfold Cursor.current
  simp [mem_suff _ _ _ _ _  hPS]
  rw [suffix0 _ _ _ _  hPS h]
  simp
  intro hk
  have haux : length (xs.prefix ++ xs.suffix) = length [i:m].toList
  · rw [hPS]
  simp at haux
  omega

@[grind =]
lemma cursor_length (xs : ([i:m].toList.Cursor)) :
    xs.prefix.length + xs.suffix.length = m - i := by
  have haux : length (xs.prefix ++ xs.suffix) = length [i:m].toList:= by rw [xs.property]
  simp at haux
  exact haux

@[simp]
lemma mem_pref_cursor' (xs : ([i:m].toList.Cursor)):
    k ∈ xs.prefix ↔ i ≤ k ∧ k < i + xs.prefix.length := by
  have haux := xs.property
  rw [mem_preff _ _ _ _ _ haux]

@[simp]
lemma mem_suf_cursor' (xs : ([i:m].toList.Cursor)) :
    k ∈ xs.suffix ↔ i + xs.prefix.length ≤ k ∧ k < m := by
  rw [mem_suff _ _ _ _ _ xs.property]
  simp
  grind [cursor_length]

@[simp]
lemma cursor_current (xs : ([i:m].toList.Cursor)) (h : 0 < xs.suffix.length) :
    xs.current h = xs.suffix[0] := by
  rfl

@[grind →]
lemma cursor_in_range (xs : ([i:m].toList.Cursor)) (h : 0 < xs.suffix.length) :
    i ≤ xs.current h ∧ xs.current h < m := by
  suffices hsuf : xs.current h ∈ xs.suffix
  · rw [mem_suf_cursor']  at hsuf
    grind
  simp

@[grind →]
lemma prefix_in_range (xs : ([i:m].toList.Cursor)) (h : k ∈ xs.prefix) :
    i ≤ k ∧ k < m := by
  grind [mem_pref_cursor',cursor_length]

@[grind →]
lemma suffix_in_range (xs : ([i:m].toList.Cursor)) (h : k ∈ xs.suffix) :
    i ≤ k ∧ k < m := by
  grind [mem_suf_cursor',cursor_length]


end RangeCursor
