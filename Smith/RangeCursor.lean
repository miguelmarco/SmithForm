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







  revert P S hPN
  induction' m with m hind
  · simp
  · intro P S hPS
    simp at hPS
    by_cases hcas : S = []
    · cases hcas
      simp_all
      grind
    · specialize hind P S.dropLast ?_
      · rw [← dropLastsum P S hcas,hPS]
        simp
      fconstructor
      · intro hk
        by_cases hkS : k ∈ S.dropLast
        · rw [hind] at hkS
          grind
        · have hauxkl : k = S.getLast hcas
          · grind
          rw [hind] at hkS
          push_neg at hkS






end RangeCursor
