import Smith.FirstNonzero

open AMat

set_option linter.style.cases false
set_option linter.flexible false

variable {m n l : ℕ}
variable {R : Type} [ED : EuclideanDomain R] [DecidableEq R]

open Matrix Nat Array

namespace AMat

open AMat

open EuclideanDomain

def xgcdcompu (a b : R) : R := -b / (gcd a b)

def xgcdcompv (a b : R) : R := a / (gcd a b)

lemma def_xgcdcompv (a b : R) : a = (xgcdcompv a b) * (gcd a b) := by
  by_cases ha : a = 0
  · simp [ha,xgcdcompv]
  · rw [xgcdcompv,mul_comm,EuclideanDomain.mul_div_cancel']
    · intro h
      rw [EuclideanDomain.gcd_eq_zero_iff] at h
      grind
    · exact EuclideanDomain.gcd_dvd_left a b

lemma def_xgcdcompu (a b : R) : b = -(xgcdcompu a b) * (gcd a b) := by
  by_cases hb : b = 0
  · simp [hb,xgcdcompu]
  · rw [xgcdcompu,mul_comm]
    have haux : (gcd a b ) ∣ b
    · exact EuclideanDomain.gcd_dvd_right a b
    choose c hc using haux
    have haux2 : -b = -c * gcd a b
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
      have haux : ((-b )/ (gcd a b)) * a = - ((b / gcd a b) * a)
      · nth_rewrite 1 3 [hy]
        rw [← mul_neg,mul_comm _ (-y),EuclideanDomain.mul_div_assoc]
        · rw [neg_mul,neg_mul]
          rw [mul_comm _ y,EuclideanDomain.mul_div_assoc]
          simp
        · simp
      rw [haux,ha,hb,hy]
      nth_rewrite 1 [hx]
      ring

@[grind =]
lemma xgcdcompone (a b : R) (hb : a ≠ 0) :
    gcdA a b * xgcdcompv a b - gcdB a b * xgcdcompu a b =  1 := by
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
    gcdA a b * xgcdcompv a b - gcdB a b * xgcdcompu a b =  1 := by
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

instance inst_ED_lt : LT R where
  lt := fun a b => a ∣ b ∧ ¬ b ∣ a

open BigOperators

instance : WellFounded (@inst_ED_lt R).lt := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  rw [@isEmpty_subtype]
  intro f hf
  have hnoet : IsNoetherian R R
  · exact isNoetherian_of_isNoetherianRing_of_finite R R
  rw [← set_has_maximal_iff_noetherian] at hnoet
  specialize hnoet { (Ideal.span {f n} ) | n : ℕ} ?_
  · rw  [Set.nonempty_def]
    use Ideal.span {f 0}
    simp
  choose M hM1 hM2 using hnoet
  choose x hx using hM1
  specialize hM2 (Ideal.span {f (x + 1)}) ?_
  · simp
  apply hM2
  simp [LT.lt]
  fconstructor
  · rw [← hx]
    rw [@Ideal.span_singleton_le_span_singleton]
    specialize hf x
    exact hf.1
  · rw [← hx]
    rw [@Ideal.span_singleton_le_span_singleton]
    specialize hf x
    apply hf.2













end AMat
