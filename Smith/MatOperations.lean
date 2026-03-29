import Smith.MatArrayBasic

open AMat

set_option linter.style.cases false
set_option linter.flexible false

variable {m n l : ℕ}
variable {R : Type}

open Matrix Nat Array

namespace AMat

variable (A : Mat n m R) (B : Mat m l R)

variable [ED : EuclideanDomain R]

infixl:50 " ≺ " => EuclideanDomain.r

def TM (i j : Fin n) : Matrix (Fin n) (Fin n) R := fun a b =>
  if a = j then (if b = i then 1 else 0) else
    if a = i then (if b = j then 1 else 0) else
    if a = b then 1 else 0

def AM (i j : Fin n) (k : R) : Matrix (Fin n) (Fin n) R := fun a b =>
  if a = j ∧ b = i then k else
    if a = b then 1 else 0

def RM : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun a b =>
  if a = ⟨n, by grind⟩ then
    if b = 0 then 1 else 0
  else
    if b = a + 1 then 1 else 0

@[grind →]
lemma abmn (a b m n : ℕ) (ha : a < n) (hb : b < m) : a * m + b <  n * m := by
  have hn : 1 ≤ n
  · grind
  have hm : 0 < m
  · grind
  have ha : a ≤  n - 1
  · grind
  have hm : m ≤ n * m
  · nth_grewrite 1 [← one_mul m,Nat.mul_le_mul_right_iff ]
    · exact hn
    exact hm
  calc a * m + b ≤  (n - 1) * m + b := by simp [Nat.mul_le_mul_right m ha]
       _ < (n - 1) * m + m := by grind
       _ = n * m := by rw [Nat.sub_mul,one_mul, Nat.sub_add_cancel]; exact hm

def Mat_mul (A : Mat n m R) (B : Mat m l R) : Mat n l R where
  Ar := Array.ofFn (fun (a : Fin (n * l)) => ∑ (j : Fin m),
    (Aget A ⟨(a.1 / l),imn _ _ _  a.2⟩  j) * (Aget B j ⟨a.1 % l,by grind⟩))
  hAr := size_ofFn

instance hmul_inst : HMul (Mat n m R) (Mat m l R) (Mat n l R) where
  hMul := Mat_mul

lemma def_Mat_mul (A : Mat n m R) (B : Mat m l R) (a : Fin n) (b : Fin l) :
    Aget (A * B) a b = ∑ (j : Fin m), (Aget A a j) * (Aget B j b) := by
  cases' a with a ha
  cases' b with b hb
  have haux : l > 0 := by omega
  have haux1 : (a * l + b) / l = a
  · rw [mul_comm,Nat.mul_add_div haux]
    simp
    grind
  simp [hmul_inst,Mat_mul,def_Aget,haux1,Nat.mod_eq_of_lt hb]

theorem mul_hom (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin l) R) :
    (frommatrix A) * (frommatrix B) = frommatrix (A * B) := by
  ext i j
  rw [def_Mat_mul]
  simp [def_frommatrix]
  rw [mul_apply]

theorem mul_hom' (A : Mat n m R) (B : Mat m l R) :
    tomatrix (A * B) = tomatrix A * (tomatrix B) := by
  apply_fun frommatrix
  · rw [← mul_hom]
    simp
  · intro a b hab
    rw [← tofrommatrix a, ← tofrommatrix b, hab]

@[simp]
theorem mul_assoc (s : ℕ) (A : Mat n m R) (B : Mat m l R) (C : Mat l s R) :
    A * (B * C) = A * B * C := by
  apply_fun tomatrix
  · simp [mul_hom']
    rw [Matrix.mul_assoc]
  · intro a b ha
    rw [← fromtomatrix a, ← fromtomatrix b, ha]

def add_multiple_row (A : Mat n m R) (i j : Fin n) (l : R) : (Mat n m R) := Id.run do
  let mut res := A
  for h : k in [:m] do
    let fk : Fin m := ⟨k,Membership.get_elem_helper h rfl⟩
    res := Aset res j fk ((Aget A j fk ) + l * (Aget A i fk))
  return res

open Std.Do

lemma def_add_multiple_row (A : Mat n m R) (i j : Fin n) (l : R) (a : Fin n) (b : Fin m) :
    Aget (add_multiple_row A i j l) a b =
      if a = j then
        Aget A j b + l * Aget A i b
      else
        Aget A a b := by
  generalize h : add_multiple_row A i j l = result
  apply Id.of_wp_run_eq h
  mvcgen
  · exact ⇓⟨xs, out⟩ => ⌜(xs.prefix.length ≤ b.1 ∧ ∀ a, Aget out a b = Aget A a b) ∨
    (b.1 < xs.prefix.length ∧ ∀ a, Aget out a b =
      if a = j then Aget A j b + l * Aget A i b  else  Aget A a b)⌝
  all_goals mleave
  · expose_names
    cases' h_2 with h2 h2
    · cases' h2 with h3 h4
      simp
      by_cases hcas : pref.length + 1 ≤ b
      · left
        fconstructor
        · omega
        · simp [res,def_Aset]
          intro a
          split_ifs with hja
          any_goals grind
      · right
        fconstructor
        · omega
        · simp [res,def_Aset]
          intro a
          split_ifs with hj1 hj2 hj3
          any_goals grind
    · cases' h2 with h2 h3
      simp [res,def_Aset]
      right
      fconstructor
      · omega
      · intro a
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

def add_multiple_col (A : Mat n m R) (i j : Fin m) (l : R) : (Mat n m R) := Id.run do
  let mut res := A
  for h : k in [:n] do
    let fk : Fin n := ⟨k,Membership.get_elem_helper h rfl⟩
    res := Aset res fk j ((Aget A fk j ) + l * (Aget A fk i))
  return res

lemma def_add_multiple_col (A : Mat n m R) (i j : Fin m) (l : R) (a : Fin n) (b : Fin m) :
    Aget (add_multiple_col A i j l) a b =
      if b = j then
        Aget A a j + l * Aget A a i
      else
        Aget A a b := by
  generalize h : add_multiple_col A i j l = result
  apply Id.of_wp_run_eq h
  mvcgen
  · exact ⇓⟨xs, out⟩ => ⌜(xs.prefix.length ≤ a.1 ∧ ∀ b, Aget out a b = Aget A a b) ∨
    (a.1 < xs.prefix.length ∧ ∀ b, Aget out a b =
      if b = j then Aget A a j + l * Aget A a i else  Aget A a b)⌝
  all_goals mleave
  · expose_names
    cases' h_2 with h2 h2
    · cases' h2 with h3 h4
      simp
      by_cases hcas : pref.length + 1 ≤ a
      · left
        fconstructor
        · omega
        · simp [res,def_Aset]
          intro b
          split_ifs with hja
          any_goals grind
      · right
        fconstructor
        · omega
        · simp [res,def_Aset]
          intro b
          split_ifs with hj1 hj2 hj3
          any_goals grind
    · cases' h2 with h2 h3
      simp [res,def_Aset]
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

lemma mul_swap_row (A : Mat n m R) (B : Mat m l R) (i j : Fin n) :
    (swap_row A i j) * B = swap_row (A * B) i j := by
  ext a b
  simp [def_Mat_mul,def_swap_row]

lemma mul_swap_col (A : Mat n m R) (B : Mat m l R) (i j : Fin l) :
    A * (swap_col B i j) = swap_col (A * B) i j := by
  ext a b
  simp [def_Mat_mul,def_swap_col]

lemma mul_swap_row_col (A : Mat n m R) (B : Mat m l R) (i j : Fin m) :
    (swap_col A i j) * (swap_row B i j) = A * B := by
  ext a b
  simp [def_Mat_mul]
  rw [← Finset.sum_add_sum_compl {i,j}, ←Finset.sum_add_sum_compl {i,j}]
  have haux : ({i, j} : Finset (Fin m))  = {j, i} := by aesop
  nth_rewrite 1 [haux]
  congr 1
  · by_cases hcas : i = j
    · simp [hcas,def_swap_col,def_swap_row]
    · have haux2 : j ≠ i := by tauto
      simp [Finset.sum_pair hcas, Finset.sum_pair haux2, def_swap_row,def_swap_col,haux2]
  · apply Finset.sum_bijective (id : Fin m → Fin m)
    any_goals simp
    · intro k h1 h2
      simp [def_swap_col,def_swap_row,h1,h2]

lemma mul_TM_row (A : Mat n m R) (i j : Fin n) : (frommatrix (TM i j) :
    Mat n n R)  * A = swap_row A i j := by
  ext a b
  simp [def_swap_row,def_Mat_mul, TM]
  split_ifs
  any_goals grind

lemma mul_TM_row_tomatrix (A : Mat n m R) (i j : Fin n) :
    (TM i j) * tomatrix A = tomatrix (swap_row A i j) := by
  ext a b
  simp [def_tomatrix,mul_apply, TM,def_swap_row]
  split_ifs
  any_goals grind

lemma mul_TM_col (A : Mat n m R) (i j : Fin m) :
    A * (frommatrix (TM i j : Matrix (Fin m) (Fin m) R)) = swap_col A i j := by
  ext a b
  simp [def_swap_col,def_Mat_mul, TM]
  split_ifs with h1 h2 h3
  · cases h1
    cases h2
    simp [Finset.sum_ite]
    have haux : ∑ x ∈ {x | ¬x = i} with x = i, Aget A a x = 0
    · apply Finset.sum_eq_zero
      simp
    simp [haux]
    apply Finset.sum_eq_single_of_mem i
    any_goals grind
  · cases h1
    rw [Finset.sum_ite,Finset.sum_eq_single_of_mem j]
    · simp
      apply Finset.sum_eq_zero
      simp
      grind
    any_goals grind
  · cases h3
    simp [Finset.sum_ite]
    rw [Finset.sum_eq_single i]
    any_goals grind
  · simp [Finset.sum_ite]
    grind

lemma mul_TM_col_tomatrix (A : Mat n m R) (i j : Fin m) :
    tomatrix A* (TM i j)  = tomatrix (swap_col A i j) := by
  apply_fun frommatrix
  · simp [← mul_hom,mul_TM_col]
  · intro a b hab
    rw [← tofrommatrix a,← tofrommatrix b, hab]

lemma mul_add_multiple_row (A : Mat n m R) (B : Mat m l R) (i j : Fin n) (d : R) :
    (add_multiple_row A i j d) * B = add_multiple_row (A * B) i j d := by
  ext a b
  simp [def_add_multiple_row,def_Mat_mul]
  split_ifs with h1
  · cases h1
    have haux : ∑ x, Aget A j x * Aget B x b + d * ∑ x, Aget A i x * Aget B x b =
         ∑ x, (Aget A j x * Aget B x b + d * Aget A i x * Aget B x b)
    · rw [← Set.toFinset_univ,Finset.sum_add_distrib,Finset.mul_sum]
      simp
      grind
    rw [haux]
    grind
  · grind

lemma mul_add_multiple_col (A : Mat n m R) (B : Mat m l R) (i j : Fin l) (d : R) :
    A * (add_multiple_col B i j d)  = add_multiple_col (A * B) i j d := by
  ext a b
  simp [def_add_multiple_col,def_Mat_mul]
  split_ifs with h1
  · cases h1
    have haux :  ∑ x, Aget A a x * Aget B x j + d * ∑ x, Aget A a x * Aget B x i =
        ∑ x, (Aget A a x * Aget B x j + d * Aget A a x * Aget B x i)
    · rw [← Set.toFinset_univ,mul_comm d _, Finset.sum_mul,Finset.sum_add_distrib]
      simp [mul_comm _ d]
      grind
    rw [haux]
    grind
  · grind

lemma mul_add_multiple_row_eq (A : Mat n m R) (B : Mat m l R) (i j : Fin m) (h : i ≠ j) (d : R) :
    (add_multiple_col A i j d) * (add_multiple_row B j i (-d)) = A * B := by
  ext a b
  simp [def_add_multiple_col,def_add_multiple_row,def_Mat_mul]
  rw [← Finset.sum_add_sum_compl {i,j}, ←Finset.sum_add_sum_compl {i,j}]
  congr 1
  · simp [Finset.sum_pair h, h]
    split_ifs
    · grind
    · ring
  · rw [Finset.sum_bijective id]
    · simp
    · simp
    · intro x hx
      simp at hx
      simp [hx]

structure LUM (A : Mat n m R) : Type where
  (IL: Mat n n R)
  (IR : Mat m m R)
  (L : Mat n n R)
  (M : Mat n m R)
  (R : Mat m m R)
  (h : L * M * R = A)
  (hIL : L * IL = frommatrix 1)
  (hIR : IR * R = frommatrix 1)

instance [Repr R] : ToString (LUM A) where
  toString := fun D => reprStr (tomatrix D.IL) ++ "  " ++ reprStr (tomatrix D.L ) ++ "  " ++ reprStr (tomatrix D.M) ++ "  " ++ reprStr (tomatrix D.R) ++ "  " ++ reprStr (tomatrix D.IR)


def triv_LUM (A : Mat n m R) : LUM A where
  IL := frommatrix 1
  IR := frommatrix 1
  L := frommatrix 1
  M := A
  R := frommatrix 1
  h := by
    apply_fun tomatrix
    · simp [mul_hom']
    · intro a b hab
      rw [← fromtomatrix a, ← fromtomatrix b, hab]
  hIL := by
    apply_fun tomatrix
    · simp [mul_hom']
    · intro a b hab
      rw [← fromtomatrix a, ← fromtomatrix b, hab]
  hIR := by
    apply_fun tomatrix
    · simp [mul_hom']
    · intro a b hab
      rw [← fromtomatrix a, ← fromtomatrix b, hab]

def LUM_swap_row (D : LUM A) (i j : Fin n) : LUM A where
  IL := swap_row D.IL i j
  IR := D.IR
  L := swap_col D.L i j
  M := swap_row D.M i j
  R := D.R
  h := by
    rw [@mul_swap_row_col,D.h]
  hIL := by
    rw [@mul_swap_row_col,D.hIL]
  hIR := D.hIR

def LUM_swap_col (D : LUM A) (i j : Fin m) : LUM A where
  IL := D.IL
  IR := swap_col D.IR i j
  L := D.L
  M := swap_col D.M i j
  R := swap_row D.R i j
  h := by rw [← mul_assoc, mul_swap_row_col, mul_assoc,D.h]
  hIL := D.hIL
  hIR := by rw [mul_swap_row_col,D.hIR]

def LUM_add_multiple_col (D : LUM A) (i j : Fin m) (h : i ≠ j) (d : R) : LUM A where
  IL := D.IL
  IR := add_multiple_col D.IR i j d
  L := D.L
  M := add_multiple_col D.M i j d
  R := add_multiple_row D.R j i (-d)
  h := by
    rw [← mul_assoc,mul_add_multiple_row_eq _ _ _ _ h,mul_assoc]
    exact D.h
  hIL := D.hIL
  hIR := by rw [mul_add_multiple_row_eq _ _ _ _ h,D.hIR]

def LUM_add_multiple_row (D : LUM A) (i j : Fin n) (h : j ≠ i) (d : R) : LUM A where
  IL := add_multiple_row D.IL i j d
  IR := D.IR
  L := add_multiple_col D.L j i (-d)
  M := add_multiple_row D.M i j d
  R := D.R
  h := by
    nth_rewrite  2 [← neg_neg d]
    rw [mul_add_multiple_row_eq _ _ _ _ h (-d)]
    exact D.h
  hIL := by
    nth_rewrite  2 [← neg_neg d]
    rw [mul_add_multiple_row_eq _ _ _ _ h (-d)]
    exact D.hIL
  hIR := D.hIR

end AMat
