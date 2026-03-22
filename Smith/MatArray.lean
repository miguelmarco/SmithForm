import Smith.XGCD

set_option linter.style.cases false
set_option linter.flexible false

variable {m n l : ℕ}
variable {R : Type} [ED : EuclideanDomain R]

open Matrix Nat Array Std.Do AMat

namespace AMat

variable (A : Mat n m R)

set_option mvcgen.warning false
set_option linter.unusedTactic false

open EuclideanDomain

/--
Substitute two columns in a matrix by a linear combination of them.
-/
def lincom_cols (A : Mat n m R) (i j : Fin m) (u v x y : R) : Mat n m R := Id.run do
  let mut res := A
  for h : k in [:n] do
    let fk : Fin n := ⟨k,Membership.get_elem_helper h rfl⟩
    let a := Aget res fk i
    let b := Aget res fk j
    res := Aset res fk j (x * a + y * b)
    res := Aset res fk i (u * a + v * b)
  return res

/--
Entries on the result of `lincom_cols`
-/
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

/--
Substitute two rows in a matrix by a linear combination of them
-/
def lincom_rows (A : Mat n m R) (i j : Fin n) (u v x y : R) : Mat n m R := Id.run do
  let mut res := A
  for h : k in [:m] do
    let fk : Fin m := ⟨k,Membership.get_elem_helper h rfl⟩
    let a := Aget res i fk
    let b := Aget res j fk
    res := Aset res j fk (x * a + y * b)
    res := Aset res i fk (u * a + v * b)
  return res

/--
Entries on the result of `lincom_rows`
-/
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

/--
If the coefficients of the linear combinations have determinant one, performing
the linear combination on the columns on one matrix, and the inverse in the rows of the other,
respects their product.
-/
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

/--
Apply a linear combination to two rows of a LUM, respecting the product.
-/
def LUM_lincom_rows (D : LUM A) (i j : Fin n) (u v x y : R) (hij : i ≠ j)
  (h : u * y - v * x = 1) : LUM A where
  L := lincom_cols D.L i j y (-x) (-v) u
  M := lincom_rows D.M i j u v x y
  R := D.R
  h := by
    have haux := lincom_mul D.L D.M i j y (-x) (-v) u hij (by grind)
    simp at haux
    rw [haux]
    exact D.h

/--
Apply a linear combination to two columns of a LUM, respecting the product.
-/
def LUM_lincom_cols (D : LUM A) (i j : Fin m) (u v x y : R) (hij : i ≠ j)
  (h : u * y - v * x = 1) : LUM A where
  L := D.L
  M := lincom_cols D.M i j u v x y
  R := lincom_rows D.R i j y (-x) (-v) u
  h := by
    have haux := lincom_mul D.M D.R i j u v x y hij h
    rw [← mul_assoc,haux,mul_assoc]
    exact D.h

/--
The entries for the result of `LUM_lincom_cols`.
-/
lemma def_LUM_lincom_cols (D : LUM A) (i j : Fin m) (u v x y : R) (hij : i ≠ j)
  (h : u * y - v * x = 1) (a : Fin n) (b : Fin m) :
    Aget (LUM_lincom_cols A D i j u v x y hij h).M a b =
      if b = i then
        u * Aget D.M a i + v * Aget D.M a j
      else if b = j then
        x * Aget D.M a i + y * Aget D.M a j
      else
        Aget D.M a b := by
  simp [LUM_lincom_cols,def_lincom_cols]

/--
The entries for the result of `LUM_lincom_rows`.
-/
lemma def_LUM_lincom_rows (D : LUM A) (i j : Fin n) (u v x y : R) (hij : i ≠ j)
  (h : u * y - v * x = 1) (a : Fin n) (b : Fin m) :
    Aget (LUM_lincom_rows A D i j u v x y hij h).M a b =
      if a = i then
        u * Aget D.M i b + v * Aget D.M j b
      else if a = j then
        x * Aget D.M i b + y * Aget D.M j b
      else
        Aget D.M a b := by
  simp [LUM_lincom_rows,def_lincom_rows]

variable [DecidableEq R]

/--
Apply `lincom_rows` with the coefficients comming from the xgcd.
-/
def reduce_rows (A : Mat n m R) (i j : Fin n) (k : Fin m) : Mat n m R:=
  lincom_rows A i j (gcdA (Aget A i k) (Aget A j k)) (gcdB (Aget A i k) (Aget A j k))
  (xgcdcompu (Aget A i k) (Aget A j k)) (xgcdcompv (Aget A i k) (Aget A j k))

/--
Apply `lincom_cols` with the coefficients comming from the xgcd.
-/
def reduce_cols (A : Mat n m R) (i j : Fin m) (k : Fin n) : Mat n m R:=
  lincom_cols A i j (gcdA (Aget A k i) (Aget A k j)) (gcdB (Aget A k i) (Aget A k j))
  (xgcdcompu (Aget A k i) (Aget A k j)) (xgcdcompv (Aget A k i) (Aget A k j))

/--
The result of `reduce_rows` in the first row is the gcd of the corresponfing entries.
-/
@[simp]
lemma reduce_rows_gcd (A : Mat n m R) (i j : Fin n) (k : Fin m) :
    Aget (reduce_rows A i j k) i k = gcd (Aget A i k) (Aget A j k) := by
  simp [reduce_rows,def_lincom_rows,EuclideanDomain.gcd_eq_gcd_ab]
  ring

/--
The result of `reduce_rows` in the second row is zero.
-/
@[grind =]
lemma reduce_rows_zero (A : Mat n m R) (i j : Fin n) (k : Fin m) (hij : i ≠ j) :
    Aget (reduce_rows A i j k) j k = 0 := by
  have haux : j ≠ i := by tauto
  simp [reduce_rows,def_lincom_rows,haux,xgcdcompzero]

/--
The result of `reduce_rows` in other rows is not changed.
-/
@[grind =]
lemma reduce_rows_other (A : Mat n m R) (i j : Fin n) (k : Fin m) (a : Fin n) (b : Fin m)
  (hai : a ≠ i) (haj : a ≠ j) :
    Aget (reduce_rows A i j k) a b = Aget A a b := by
  simp [reduce_rows,def_lincom_rows,hai,haj]

/--
The result of `reduce_cols` in the first column is the gcd of the corresponfing entries.
-/
@[simp]
lemma reduce_cols_gcd (A : Mat n m R) (i j : Fin m) (k : Fin n) :
    Aget (reduce_cols A i j k) k i = gcd (Aget A k i) (Aget A k j) := by
  simp [reduce_cols,def_lincom_cols,EuclideanDomain.gcd_eq_gcd_ab]
  ring

/--
The result of `reduce_cols` in the second column is zero.
-/
@[grind =]
lemma reduce_cols_zero (A : Mat n m R) (i j : Fin m) (k : Fin n) (hij : i ≠ j) :
    Aget (reduce_cols A i j k) k j = 0 := by
  have haux : j ≠ i := by tauto
  simp [reduce_cols,def_lincom_cols,haux,xgcdcompzero]

/--
The result of `reduce_cols` in other columns is not changed.
-/
@[grind =]
lemma reduce_cols_other (A : Mat n m R) (i j : Fin m) (k : Fin n) (a : Fin n) (b : Fin m)
  (hbi : b ≠ i) (hbj : b ≠ j) :
    Aget (reduce_cols A i j k) a b = Aget A a b := by
  simp [reduce_cols,def_lincom_cols,hbi,hbj]

/--
Apply a `reduce_cols` on a LUM.
-/
def LUM_reduce_cols (D : LUM A) (i j : Fin m) (k : Fin n) (hij : i ≠ j)
  (h0 : Aget D.M k i ≠ 0) :
    LUM A :=
  LUM_lincom_cols _ D i j (EuclideanDomain.gcdA (Aget D.M k i) (Aget D.M k j))
    (EuclideanDomain.gcdB (Aget D.M k i) (Aget D.M k j))
    (xgcdcompu  (Aget D.M k i) (Aget D.M k j))
    (xgcdcompv (Aget D.M k i) (Aget D.M k j))
    hij (xgcdcompone _ _ h0)

/--
Apply a `reduce_rows` on a LUM.
-/
def LUM_reduce_rows (D : LUM A) (i j : Fin n) (k : Fin m) (hij : i ≠ j)
  (h0 : Aget D.M i k ≠ 0) :
    LUM A  :=
  LUM_lincom_rows _ D i j (EuclideanDomain.gcdA (Aget D.M i k) (Aget D.M j k))
    (EuclideanDomain.gcdB (Aget D.M i k) (Aget D.M j k))
    (xgcdcompu  (Aget D.M i k) (Aget D.M j k))
    (xgcdcompv (Aget D.M i k) (Aget D.M j k))
    hij (xgcdcompone _ _ h0)

/--
The result of `LUM_reduce_cols` coincides with `reduce_cols`.
-/
@[simp]
lemma LUM_reduce_cols_eq_M (D : LUM A) (i j : Fin m) (k : Fin n) (hij : i ≠ j)
  (h0 : Aget D.M k i ≠ 0) :
    (LUM_reduce_cols A D i j k hij h0).M = reduce_cols D.M i j k := by
  rfl

/--
The result of `LUM_reduce_rows` coincides with `reduce_rows`.
-/
@[simp]
lemma LUM_reduce_rows_eq_M (D : LUM A) (i j : Fin n) (k : Fin m) (hij : i ≠ j)
  (h0 : Aget D.M i k ≠ 0) :
    (LUM_reduce_rows A D i j k hij h0).M = reduce_rows D.M i j k := by
  rfl

/--
Formula for the entries of `LUM_reduce_cols`.
-/
lemma def_LUM_reduce_cols (D : LUM A) (i j : Fin m) (k : Fin n) (b : Fin m) (hij : i ≠ j)
  (h0 : Aget D.M k i ≠ 0) :
    Aget (LUM_reduce_cols A D i j k hij h0).M k b =
      if b = i then
        EuclideanDomain.gcd (Aget D.M k i) (Aget D.M k j)
      else if b = j then
        0
      else
        Aget D.M k b := by
  simp [LUM_reduce_cols]
  split_ifs with h1 h2
  · simp [def_LUM_lincom_cols,h1,EuclideanDomain.gcd_eq_gcd_ab]
    ring
  · simp [def_LUM_lincom_cols,h1,xgcdcompzero]
    tauto
  · simp [def_LUM_lincom_cols,h1]
    tauto

/--
Formula for the entries of `LUM_reduce_rows`.
-/
lemma def_LUM_reduce_rows (D : LUM A) (i j : Fin n) (k : Fin m) (a : Fin n) (hij : i ≠ j)
  (h0 : Aget D.M i k ≠ 0) :
    Aget (LUM_reduce_rows A D i j k hij h0).M a k =
      if a = i then
        EuclideanDomain.gcd (Aget D.M i k) (Aget D.M j k)
      else if a = j then
        0
      else
        Aget D.M a k := by
  simp [LUM_reduce_rows,def_LUM_lincom_rows]
  split_ifs with h1 h2
  · simp [EuclideanDomain.gcd_eq_gcd_ab]
    ring
  · apply xgcdcompzero
  · rfl

structure LUM_nonzero (i : Fin n) (j : Fin m) : Type where
  D : LUM A
  hD : Aget D.M i j ≠ 0

/--
Perform column operations to get zeros at the right of a given entry
-/
def LUM_clean_row_after (D : LUM A) (i b : ℕ) (hin : i < n) (hb : b < m)
  (hb0 : Aget D.M ⟨i, hin⟩ ⟨b, hb⟩ ≠ 0) : LUM A:= Id.run do
  let mut res : LUM_nonzero A ⟨i,hin⟩ ⟨b,hb⟩ := {
    D := D
    hD := hb0
  }
  for h : k in [b + 1:m] do
    if Aget res.D.M ⟨i,hin⟩ ⟨k,Membership.get_elem_helper h rfl⟩ = 0
    then
      continue
    else
      res := {
        D := LUM_reduce_cols _ res.D ⟨b,by simp at h; omega⟩ ⟨k, Membership.get_elem_helper h rfl⟩
         ⟨i,hin⟩ (by simp at h ⊢ ; omega) (res.hD)
        hD := by
          simp [EuclideanDomain.gcd_eq_zero_iff,res.hD]
      }
  return res.D

/--
Preform row operations to get zeros under a given entry
-/
def LUM_clean_col_after (D : LUM A) (i b : ℕ) (hin : i < m) (hb : b < n)
  (hb0 : Aget D.M ⟨b, hb⟩ ⟨i, hin⟩ ≠ 0) : LUM A:= Id.run do
  let mut res : LUM_nonzero A ⟨b,hb⟩ ⟨i,hin⟩ := {
    D := D
    hD := hb0
  }
  for h : k in [b + 1:n] do
    if Aget res.D.M ⟨k,Membership.get_elem_helper h rfl⟩ ⟨i,hin⟩ = 0
    then
      continue
    else
      res := {
        D := LUM_reduce_rows _ res.D ⟨b,hb⟩ ⟨k, Membership.get_elem_helper h rfl⟩
          ⟨i,hin⟩ (by simp at h ⊢ ; omega) (res.hD)
        hD := by
          simp [EuclideanDomain.gcd_eq_zero_iff,res.hD]
      }
  return res.D

/--
The entries at the right are made zero by `LUM_clean_row_after`.
-/
lemma LUM_prop_clean_row_after (D : LUM A) (i b : ℕ) (hin : i < n) (hb : b < m)
  (hb0 : Aget D.M ⟨i, hin⟩ ⟨b, hb⟩ ≠ 0) :
    ∀ k, b < k → (hkm : k < m) →  Aget (LUM_clean_row_after _ D i b hin hb hb0).M
      ⟨i, hin⟩ ⟨k, hkm⟩ = 0 := by
  generalize h : LUM_clean_row_after _ D i b hin hb hb0 = resu
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ =>
    ⌜∀ k, (hk : k ∈ xs.prefix) → Aget letMuts.D.M ⟨i,hin⟩ ⟨k,by grind⟩ = 0⌝
  with mleave
  · simp_all
    expose_names
    intro k hk
    cases' hk with hk hk
    · apply h_3
      exact hk
    · cases hk
      exact h_2
  · simp_all
    expose_names
    intro k hk
    cases' hk with hk hk
    · rw [reduce_cols_other]
      · apply h_3
        exact hk
      · simp
        intro hkb
        cases hkb
        have haux : b ∈ [b + 1:m].toList
        · rw [h_1]
          grind
        simp at haux
      · grind
    · cases hk
      grind [reduce_cols_zero]
  · simp_all
  · grind

/--
The entries under a given one are made zero by `LUM_clean_col_after`.
-/
lemma LUM_prop_clean_col_after (D : LUM A) (i b : ℕ) (hin : i < m) (hb : b < n)
  (hb0 : Aget D.M ⟨b, hb⟩ ⟨i, hin⟩ ≠ 0) :
    ∀ k, b < k → (hkm : k < n) →  Aget (LUM_clean_col_after _ D i b hin hb hb0).M
      ⟨k, hkm⟩ ⟨i, hin⟩ = 0 := by
  generalize h : LUM_clean_col_after _ D i b hin hb hb0 = resu
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ =>
    ⌜∀ k, (hk : k ∈ xs.prefix) → Aget letMuts.D.M  ⟨k,by grind⟩ ⟨i,hin⟩ = 0⌝
  with mleave
  · simp_all
    expose_names
    intro k hk
    cases' hk with hk hk
    · apply h_3
      exact hk
    · cases hk
      exact h_2
  · simp_all
    expose_names
    intro k hk
    cases' hk with hk hk
    · rw [reduce_rows_other]
      · apply h_3
        exact hk
      · simp
        intro hkb
        cases hkb
        have haux : b ∈ [b + 1:n].toList
        · rw [h_1]
          grind
        simp at haux
      · grind
    · cases hk
      grind [reduce_rows_zero]
  · simp_all
  · grind

/--
The entries to the left are unchanged by `LUM_clean_row_after`.
-/
lemma LUM_prop_clean_row_after' (D : LUM A) (i j b : ℕ) (hin : i < n) (hjn : j < n) (hb : b < m)
  (hb0 : Aget D.M ⟨i, hin⟩ ⟨b, hb⟩ ≠ 0) :
    ∀ k, (hkb : k < b)  →  Aget (LUM_clean_row_after _ D i b hin hb hb0).M ⟨j, hjn⟩ ⟨k,by omega⟩ =
      Aget D.M ⟨j, hjn⟩ ⟨k, by omega⟩ := by
  generalize h : LUM_clean_row_after _ D i b hin hb hb0 = resu
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ =>
    ⌜∀ k, (hkb : k < b)  →  Aget letMuts.D.M ⟨j, hjn⟩ ⟨k, by omega⟩ =
      Aget D.M ⟨j, hjn⟩ ⟨k,by omega⟩⌝
  with mleave
  · simp_all
    expose_names
    intro k hk
    rw [reduce_cols_other,h_3]
    any_goals grind
  · tauto

/--
The entries over the pivot are unchanged by `LUM_clean_col_after`.
-/
lemma LUM_prop_clean_col_after' (D : LUM A) (i j b : ℕ) (hin : i < m) (hjn : j < m) (hb : b < n)
  (hb0 : Aget D.M ⟨b, hb⟩ ⟨i, hin⟩ ≠ 0) :
    ∀ k, (hkb : k < b) → Aget (LUM_clean_col_after _ D i b hin hb hb0).M ⟨k,by omega⟩ ⟨j, hjn⟩  =
      Aget D.M ⟨k, by omega⟩ ⟨j, hjn⟩  := by
  generalize h : LUM_clean_col_after _ D i b hin hb hb0 = resu
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ =>
    ⌜∀ k, (hkb : k < b)  →  Aget letMuts.D.M ⟨k, by omega⟩ ⟨j, hjn⟩  =
      Aget D.M ⟨k,by omega⟩ ⟨j, hjn⟩⌝
  with mleave
  · simp_all
    expose_names
    intro k hk
    rw [reduce_rows_other,h_3]
    any_goals grind
  · tauto

/--
If the entries in a diifferent row, at the column of the pivot or to its left, are zero,
they remain zero after `LUM_clean_row_after`.
-/
lemma LUM_prop_clean_row_after'' (D : LUM A) (i j b : ℕ) (hin : i < n) (hjn : j < n) (hb : b < m)
  (hb0 : Aget D.M ⟨i, hin⟩ ⟨b, hb⟩ ≠ 0)
  (h : ∀ k, (hkb : b ≤ k) → (hkm : k < m) → Aget D.M ⟨j, hjn⟩ ⟨k, hkm⟩ = 0) :
    ∀ k, (hkb : b ≤ k) → (hkm : k < m) → Aget (LUM_clean_row_after _ D i b hin hb hb0).M
      ⟨j, hjn⟩ ⟨k, hkm⟩ = 0 := by
  generalize h : LUM_clean_row_after _ D i b hin hb hb0 = resu
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, letMuts⟩ => ⌜∀ k, (hkb : b ≤ k) → (hkm : k < m) → Aget letMuts.D.M ⟨j,hjn⟩ ⟨k,hkm⟩ = 0⌝
  with mleave
  · expose_names
    intro k hbk hkm
    have h4 := h_4 b (by omega)
    have h5 := h_4 cur (by grind) (by grind)
    rw [LUM_reduce_cols,def_LUM_lincom_cols,h4,h5]
    simp
    intro h1 h2
    apply h_4
    exact hbk

/--
If the entries in a diifferent column, at the row of the pivot or under it, are zero,
they remain zero after `LUM_clean_col_after`.
-/
lemma LUM_prop_clean_col_after'' (D : LUM A) (i j b : ℕ) (hin : i < m) (hjn : j < m) (hb : b < n)
(hb0 : Aget D.M ⟨b, hb⟩ ⟨i, hin⟩ ≠ 0)
(h : ∀ k, (hkb : b ≤ k) → (hkm : k < n) → Aget D.M ⟨k, hkm⟩ ⟨j, hjn⟩ = 0) :
  ∀ k, (hkb : b ≤ k) → (hkm : k < n) → Aget (LUM_clean_col_after _ D i b hin hb hb0).M
    ⟨k, hkm⟩ ⟨j, hjn⟩ = 0 := by
generalize h : LUM_clean_col_after _ D i b hin hb hb0 = resu
apply Id.of_wp_run_eq h
mvcgen invariants
· ⇓⟨xs, letMuts⟩ => ⌜∀ k, (hkb : b ≤ k) → (hkm : k < n) → Aget letMuts.D.M ⟨k,hkm⟩ ⟨j,hjn⟩ = 0⌝
with mleave
· expose_names
  intro k hbk hkm
  have h4 := h_4 b (by omega)
  have h5 := h_4 cur (by grind) (by grind)
  rw [LUM_reduce_rows,def_LUM_lincom_rows,h4,h5]
  simp
  intro h1 h2
  apply h_4
  exact hbk

/--
Make zeros in a row at the right of the diagonal.
-/
def LUM_clean_row (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m) : LUM A :=
  match h : first_nonzero_i_row D.M i with
  | none => D
  | some b => if hib : i = b then LUM_clean_row_after _ D i i hin him
    (by cases hib; exact first_nonzero_i_row_prop_1 D.M i i h)
    else
      LUM_swap_col _ (LUM_clean_row_after _ D i b hin (by grind)
        (first_nonzero_i_row_prop_1 D.M i b h))  ⟨i,him⟩ ⟨b, by grind⟩

/--
Make zeros in a column under the diagonal.
-/
def LUM_clean_col (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m) : LUM A :=
  match h : first_nonzero_i_col D.M i with
  | none => D
  | some b => if hib : i = b then LUM_clean_col_after _ D i i him hin
    (by cases hib; exact first_nonzero_i_col_prop_1 D.M i i h)
    else
      LUM_swap_row _ (LUM_clean_col_after _ D i b him (by grind)
        (first_nonzero_i_col_prop_1 D.M i b h))  ⟨i,hin⟩ ⟨b, by grind⟩

/--
If everything is zero at the pivot or its right, `LUM_clean_row` does nothing.
-/
@[grind =]
lemma LUM_clean_row_none (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m)
  (hnz : first_nonzero_i_row D.M i = none) :
    LUM_clean_row _ D i hin him = D := by
  unfold LUM_clean_row
  grind

/--
If everything is zero at the pivot or under it, `LUM_clean_col` does nothing.
-/
@[grind =]
lemma LUM_clean_col_none (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m)
  (hnz : first_nonzero_i_col D.M i = none) :
    LUM_clean_col _ D i hin him = D := by
  unfold LUM_clean_col
  grind

/--
Formula for the result of `LUM_clean_row` if there are nonzero entries.
-/
@[grind →]
lemma LUM_clean_row_some (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m) (b : ℕ)
  (h : first_nonzero_i_row D.M i = some b) :
    LUM_clean_row _ D i hin him =
      if hib : i = b
      then
        LUM_clean_row_after _ D i i hin him
          (by rw [←hib] at h; exact first_nonzero_i_row_prop_1 _ _ _ h)
      else
        LUM_swap_col A (LUM_clean_row_after _ D i b hin
        (first_nonzero_i_row_inter D.M i b h).2.2.2 (first_nonzero_i_row_prop_1 D.M i b h))
        ⟨i,him⟩ ⟨b,(first_nonzero_i_row_inter D.M i b h).2.2.2⟩ := by
  unfold LUM_clean_row
  grind

/--
Formula for the result of `LUM_clean_col` if there are nonzero entries.
-/
@[grind →]
lemma LUM_clean_col_some (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m) (b : ℕ)
  (h : first_nonzero_i_col D.M i = some b) :
    LUM_clean_col _ D i hin him =
      if hib : i = b
      then
        LUM_clean_col_after _ D i i him hin
          (by rw [←hib] at h; exact first_nonzero_i_col_prop_1 _ _ _ h)
      else
        LUM_swap_row A (LUM_clean_col_after _ D i b him
        (first_nonzero_i_col_inter _ _ _ h).2.2.2 (first_nonzero_i_col_prop_1 _ _ _ h))
        ⟨i,hin⟩ ⟨b,(first_nonzero_i_col_inter _ _ _ h).2.2.2⟩ := by
  unfold LUM_clean_col
  grind

/--
`LUM_clean_row` leaves zeros at the right of the diagonal in the given row.
-/
@[grind =]
lemma LUM_clean_row_prop (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m) :
    ∀ k, i < k → (hk : k < m) → Aget (LUM_clean_row A D i hin him).M ⟨i,hin⟩ ⟨k,hk⟩ = 0 := by
  intro k hkn hkm
  match hnz : (first_nonzero_i_row D.M i) with
  | none => rw [LUM_clean_row_none]
            · rw [first_nonzero_i_row_prop_none_iff] at hnz
              · apply hnz
                any_goals omega
              · exact hin
              · exact him
            · exact hnz
  | some b => rw [LUM_clean_row_some A D i hin him b hnz]
              rw [first_nonzero_i_row_prop_some_iff _ _ hin him _ ] at hnz
              cases' hnz with hn1 hn2
              cases' hn2 with hn3 hn4
              specialize hn4 hn3
              cases' hn4 with hn4 hn6
              split_ifs with h1
              · apply LUM_prop_clean_row_after
                any_goals omega
              · simp [LUM_swap_col,def_swap_col]
                split_ifs with h2 h3
                · omega
                · rw [LUM_prop_clean_row_after']
                  any_goals aesop
                · by_cases hcas : k < b
                  · rw [LUM_prop_clean_row_after']
                    · apply hn6
                      any_goals omega
                    exact hcas
                  · apply LUM_prop_clean_row_after
                    any_goals omega

/--
`LUM_clean_col` leaves zeros at under the diagonal in the given column.
-/
@[grind =]
lemma LUM_clean_col_prop (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m) :
    ∀ k, i < k → (hk : k < n) → Aget (LUM_clean_col A D i hin him).M ⟨k,hk⟩ ⟨i,him⟩ = 0 := by
  intro k hkn hkm
  match hnz : (first_nonzero_i_col D.M i) with
  | none => rw [LUM_clean_col_none]
            · rw [first_nonzero_i_col_prop_none_iff] at hnz
              · apply hnz
                any_goals omega
              · exact hin
              · exact him
            · exact hnz
  | some b => rw [LUM_clean_col_some A D i hin him b hnz]
              rw [first_nonzero_i_col_prop_some_iff _ _ hin him _ ] at hnz
              cases' hnz with hn1 hn2
              cases' hn2 with hn3 hn4
              specialize hn4 hn3
              cases' hn4 with hn4 hn6
              split_ifs with h1
              · apply LUM_prop_clean_col_after
                any_goals omega
              · simp [LUM_swap_row,def_swap_row]
                split_ifs with h2 h3
                · omega
                · rw [LUM_prop_clean_col_after']
                  any_goals aesop
                · by_cases hcas : k < b
                  · rw [LUM_prop_clean_col_after']
                    · apply hn6
                      any_goals omega
                    exact hcas
                  · apply LUM_prop_clean_col_after
                    any_goals omega

/--
If there are zeros in another row, there are still zeros after `LUM_clean_row`.
-/
lemma LUM_clean_row_prop_other (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m)
  (hjn : j < n) (hj : ∀ c, (hc : c < m) → (i ≤ c) → Aget D.M ⟨j, hjn⟩ ⟨c, hc⟩ = 0) :
    ∀ c, (hc : c < m) → (i ≤ c) → Aget (LUM_clean_row _ D i hin him).M ⟨j,hjn⟩ ⟨c,hc⟩ = 0 := by
  intro c hcm hic
  match  h : first_nonzero_i_row D.M i with
  | none => grind
  | some b => rw [LUM_clean_row_some _ _ i hin him b h]
              rw [first_nonzero_i_row_prop_some_iff] at h
              · cases' h with hc1 hc2
                cases' hc2 with hc2 hc3
                · split_ifs with h1
                  · apply LUM_prop_clean_row_after''
                    any_goals omega
                    intro k hk hkm
                    apply hj
                    exact hk
                  · simp [LUM_swap_col,def_swap_col]
                    split_ifs with hco1 hco2
                    · apply LUM_prop_clean_row_after''
                      any_goals omega
                      intro k hkb hkm
                      apply hj
                      any_goals omega
                    · rw [LUM_prop_clean_row_after']
                      · apply hj
                        omega
                      any_goals omega
                    · by_cases hcasc : c < b
                      · rw [LUM_prop_clean_row_after']
                        any_goals omega
                        · apply hj
                          any_goals omega
                      · apply LUM_prop_clean_row_after''
                        any_goals omega
                        intro k hk1 hk2
                        apply hj
                        omega
              any_goals omega

/--
If there are zeros in another column, there are still zeros after `LUM_clean_col`.
-/
lemma LUM_clean_col_prop_other (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m)
  (hjn : j < m) (hj : ∀ c, (hc : c < n) → (i ≤ c) → Aget D.M ⟨c, hc⟩ ⟨j, hjn⟩ = 0) :
    ∀ c, (hc : c < n) → (i ≤ c) → Aget (LUM_clean_col _ D i hin him).M ⟨c,hc⟩ ⟨j,hjn⟩ = 0 := by
  intro c hcm hic
  match  h : first_nonzero_i_col D.M i with
  | none => grind
  | some b => rw [LUM_clean_col_some _ _ i hin him b h]
              rw [first_nonzero_i_col_prop_some_iff] at h
              · cases' h with hc1 hc2
                cases' hc2 with hc2 hc3
                · split_ifs with h1
                  · apply LUM_prop_clean_col_after''
                    any_goals omega
                    intro k hk hkm
                    apply hj
                    exact hk
                  · simp [LUM_swap_row,def_swap_row]
                    split_ifs with hco1 hco2
                    · apply LUM_prop_clean_col_after''
                      any_goals omega
                      intro k hkb hkm
                      apply hj
                      any_goals omega
                    · rw [LUM_prop_clean_col_after']
                      · apply hj
                        omega
                      any_goals omega
                    · by_cases hcasc : c < b
                      · rw [LUM_prop_clean_col_after']
                        any_goals omega
                        · apply hj
                          any_goals omega
                      · apply LUM_prop_clean_col_after''
                        any_goals omega
                        intro k hk1 hk2
                        apply hj
                        omega
              any_goals omega

/--
The pivot of `LUM_clean_row` divides the original pivot.
-/
lemma LUM_clean_row_dvd (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m)
  (h1 : Aget D.M ⟨i, hin⟩ ⟨i, him⟩ ≠ 0) :
    Aget (LUM_clean_row _ D i hin him).M ⟨i,hin⟩ ⟨i,him⟩ ∣ Aget D.M ⟨i,hin⟩ ⟨i,him⟩  := by
  have hb : first_nonzero_i_row D.M i = i
  · grind [first_nonzero_i_row_prop_some_iff D.M i hin him i]
  have haux :  LUM_clean_row _ D i hin him = LUM_clean_row_after _ D i i hin him h1
  · grind
  rw [haux]
  generalize h : (LUM_clean_row_after _ D i i hin him h1) = result
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, res⟩ => ⌜Aget res.D.M ⟨i, hin⟩ ⟨i, him⟩ ∣ Aget D.M ⟨i, hin⟩ ⟨i, him⟩⌝
  with mleave
  any_goals simp_all
  · expose_names
    apply dvd_trans _ h_3
    apply EuclideanDomain.gcd_dvd_left

/--
The pivot of `LUM_clean_col` divides the original pivot.
-/
lemma LUM_clean_col_dvd (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m)
  (h1 : Aget D.M ⟨i, hin⟩ ⟨i, him⟩ ≠ 0) :
    Aget (LUM_clean_col _ D i hin him).M ⟨i,hin⟩ ⟨i,him⟩ ∣ Aget D.M ⟨i,hin⟩ ⟨i,him⟩  := by
  have hb : first_nonzero_i_col D.M i = i
  · grind [first_nonzero_i_col_prop_some_iff D.M i hin him i]
  have haux :  LUM_clean_col _ D i hin him = LUM_clean_col_after _ D i i him hin h1
  · grind
  rw [haux]
  generalize h : (LUM_clean_col_after _ D i i him hin h1) = result
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, res⟩ => ⌜Aget res.D.M ⟨i, hin⟩ ⟨i, him⟩ ∣ Aget D.M ⟨i, hin⟩ ⟨i, him⟩⌝
  with mleave
  any_goals simp_all
  · expose_names
    apply dvd_trans _ h_3
    apply EuclideanDomain.gcd_dvd_left

/--
The pivot of `LUM_clean_row` divides all the entries at the right of the pivot in the original LUM.
-/
lemma LUM_clean_row_dvd' (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m)
  (h1 : Aget D.M ⟨i, hin⟩ ⟨i, him⟩ ≠ 0) :
    ∀ k, (hik : i < k) → (hkm : k < m) →
    Aget (LUM_clean_row _ D i hin him).M ⟨i,hin⟩ ⟨i,him⟩ ∣ Aget D.M ⟨i,hin⟩ ⟨k,hkm⟩ := by
  have hb : first_nonzero_i_row D.M i = i
  · grind [first_nonzero_i_row_prop_some_iff D.M i hin him i]
  have haux :  LUM_clean_row _ D i hin him = LUM_clean_row_after _ D i i hin him h1
  · grind
  rw [haux]
  generalize h : (LUM_clean_row_after _ D i i hin him h1) = result
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, res⟩ => ⌜(∀ k, (hk: k ∈ xs.prefix) →
      (Aget res.D.M ⟨i,hin⟩ ⟨i,him⟩ ∣ Aget D.M ⟨i,hin⟩ ⟨k,by grind⟩))
    ∧
    (∀ k, (hk : k ∈ xs.suffix) →
      Aget res.D.M ⟨i,hin⟩ ⟨k, by grind⟩ = Aget D.M ⟨i,hin⟩ ⟨k, by grind⟩ ) ⌝
  with mleave
  any_goals simp_all
  · expose_names
    cases' h_3 with h3 h4
    intro k hk
    cases' hk with hk hk
    · specialize h3 _ hk
      exact h3
    · cases hk
      rw [h_2]
      simp
  · expose_names
    cases' h_3 with h3 h4
    fconstructor
    · intro k hk
      cases' hk with hk hk
      · specialize h3 k hk
        apply dvd_trans _ h3
        apply EuclideanDomain.gcd_dvd_left
      · cases hk
        apply EuclideanDomain.gcd_dvd_right
    · intro k hk
      rw [reduce_cols_other]
      · apply h4
        right
        exact hk
      · simp
        grind
      · simp
        grind
  · expose_names
    intro k hik hkm
    apply h_1
    · omega
    · exact hkm

/--
The pivot of `LUM_clean_col` divides all the entries under the pivot in the original LUM.
-/
lemma LUM_clean_col_dvd' (D : LUM A) (i : ℕ) (hin : i < n) (him : i < m)
  (h1 : Aget D.M ⟨i, hin⟩ ⟨i, him⟩ ≠ 0) :
    ∀ k, (hik : i < k) → (hkm : k < n) →
    Aget (LUM_clean_col _ D i hin him).M ⟨i,hin⟩ ⟨i,him⟩ ∣ Aget D.M ⟨k,hkm⟩ ⟨i,him⟩  := by
  have hb : first_nonzero_i_col D.M i = i
  · grind [first_nonzero_i_col_prop_some_iff D.M i hin him i]
  have haux :  LUM_clean_col _ D i hin him = LUM_clean_col_after _ D i i him hin h1
  · grind
  rw [haux]
  generalize h : (LUM_clean_col_after _ D i i him hin h1) = result
  apply Id.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, res⟩ => ⌜(∀ k, (hk: k ∈ xs.prefix) →
      (Aget res.D.M ⟨i,hin⟩ ⟨i,him⟩ ∣ Aget D.M ⟨k,by grind⟩ ⟨i,him⟩ ))
    ∧
    (∀ k, (hk : k ∈ xs.suffix) →
      Aget res.D.M ⟨k, by grind⟩ ⟨i,him⟩  = Aget D.M ⟨k, by grind⟩ ⟨i,him⟩ ) ⌝
  with mleave
  any_goals simp_all
  · expose_names
    cases' h_3 with h3 h4
    intro k hk
    cases' hk with hk hk
    · specialize h3 _ hk
      exact h3
    · cases hk
      rw [h_2]
      simp
  · expose_names
    cases' h_3 with h3 h4
    fconstructor
    · intro k hk
      cases' hk with hk hk
      · specialize h3 k hk
        apply dvd_trans _ h3
        apply EuclideanDomain.gcd_dvd_left
      · cases hk
        apply EuclideanDomain.gcd_dvd_right
    · intro k hk
      rw [reduce_rows_other]
      · apply h4
        right
        exact hk
      · simp
        grind
      · simp
        grind
  · expose_names
    intro k hik hkm
    apply h_1
    · omega
    · exact hkm



def M : Mat 2 3 ℤ where
  Ar := #[3,0,5,6,7,8]
  hAr := by simp
#eval (triv_LUM M)
#eval LUM_clean_row _ (LUM_clean_row M (triv_LUM M) 0  (by omega) (by omega)) 1 (by omega) (by omega)




variable [DecidableRel ED.r]

end AMat
