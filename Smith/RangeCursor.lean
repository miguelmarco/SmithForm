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

lemma mem_suff


end RangeCursor
