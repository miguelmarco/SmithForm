


variable {n m : ℕ} {R : Type} [DER : EuclideanDomain R] [DecidableRel DER.r] [DecidableEq R]

instance : DecidableRel Int.euclideanDomain.r := fun a b =>
  if ha : a.natAbs < b.natAbs then
    isTrue ha
  else isFalse ha

def TM (i j : Fin n): Matrix (Fin n) (Fin n) R := fun a b =>
  if a = j then (if b = i then 1 else 0) else
    if a = i then (if b = j then 1 else 0) else
    if a = b then 1 else 0

def AM  (i j : Fin n) (k : R): Matrix (Fin n) (Fin n) R := fun a b =>
  if a = j ∧ b = i then k else
    if a = b then 1 else 0

def RM : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun a b =>
  if a = ⟨n, by grind⟩ then
    if b = 0 then 1 else 0
  else
    if b = a + 1 then 1 else 0

@[grind →]
lemma amn (a m n : ℕ) (ha : a < n *m) : a / m < n := by
  apply Nat.div_lt_of_lt_mul
  grind

@[grind →]
lemma amn' (a m n : ℕ) (ha : a < n * m) : a % m < m := by
  apply Nat.mod_lt a
  grind

-- convert the matrix to an array
def toarray (M : Matrix (Fin n) (Fin m) R) : Array R :=
  Array.ofFn (fun (a : Fin (n*m)) => M ⟨a.1 / m, by grind⟩ ⟨a % m, by grind⟩)

lemma lentoarray (M : Matrix (Fin n) (Fin m) R) : Array.size (toarray M) = n * m := by
  unfold toarray
  exact Array.size_ofFn

@[grind →]
lemma abmn (a b m n :  ℕ ) (ha : a < n) (hb : b < m) : a * m + b <  n * m := by
  have hn : 1 ≤ n
  · grind
  have hm : 0 < m
  · grind
  have ha : a ≤  n - 1
  · grind
  have hm : m ≤ n * m
  · nth_grewrite 1 [← one_mul m,Nat.mul_le_mul_right_iff ]
    exact hn
    exact hm
  calc a * m + b ≤  (n - 1) * m + b := by simp [Nat.mul_le_mul_right m ha]
       _ < (n - 1) * m + m := by grind
       _ = n * m := by rw [Nat.sub_mul,one_mul, Nat.sub_add_cancel]; exact hm

@[simp]
lemma def_toarray (M : Matrix (Fin n) (Fin m) R) (a : Fin n) (b : Fin m) : (toarray M)[a * m + b]'(by rw [lentoarray]; grind) = M a b := by
  unfold toarray
  simp
  congr
  · cases' a with a ha
    cases' b with b hb
    simp
    rw [@Nat.div_eq_sub_mod_div]
    simp
    rw [Nat.mod_eq_of_lt hb]
    simp
    grind [Nat.mul_div_cancel]
  · grind [Nat.mod_eq_of_lt]

def fromarray (A : Array R) (h : A.size = n * m) : Matrix (Fin n) (Fin m) R := fun a b =>
  A[a.1* m+b.1]'(by
    rw [h]
    apply abmn _ _ _ _ a.2 b.2
    )

@[simp]
lemma fromtoarray (M : Matrix (Fin n) (Fin m) R) : fromarray (toarray M) (lentoarray _) = M := by
  ext a b
  simp [fromarray]

@[simp]
lemma tofromarray (A : Array R) (hA : A.size = n * m) : toarray (fromarray A hA) = A := by
  ext i hi hi2
  · rw [hA,lentoarray]
  · simp [toarray,fromarray]
    congr
    exact Nat.div_add_mod' i m

def Aget (A : Array R) (hA : A.size = n * m) (i : Fin n) (j : Fin m) : R := A[i.1*m + j.1]'(by rw [hA]; exact abmn _ _ _ _ i.2 j.2)


def mulArray {l : ℕ} (A : Array R) (hA : A.size = n * m) (B : Array R) (hB : B.size = m * l) : Array R :=
  Array.ofFn (fun (a : Fin (n * l)) => ∑ (j : Fin m), (Aget A hA ⟨(a.1 / l),amn _ _ _  a.2⟩  j) * (Aget B hB j ⟨a.1 % l,by grind⟩))

@[simp]
theorem lenmularray  {l : ℕ} (A : Array R) (hA : A.size = n * m) (B : Array R) (hB : B.size = m * l) :
    (mulArray A hA B hB).size = n * l := by
  simp [mulArray]

theorem mul_hom {l : ℕ} (M : Matrix (Fin n) (Fin m) R) (N : Matrix (Fin m) (Fin l) R) :
    mulArray (toarray M) (lentoarray M) (toarray N) (lentoarray N) = toarray (M * N) := by
  by_cases hcas : 0 < m ∧ 0 < l ∧ 0 < n
  cases' hcas with hcas hcas2
  cases' hcas2 with hcas2 hcas3
  · ext i hi hi2
    · simp [toarray]
    · have haux : (toarray (M * N))[i]'(hi2) = (toarray (M * N))[(i / l) * l + i % l]'(by rw [Nat.div_add_mod']; exact hi2)
      · simp [Nat.div_add_mod']
      have haux2 := def_toarray (M * N) ⟨(i / l), by rw [lentoarray] at hi2; exact amn i l n hi2 ⟩  ⟨i % l, by rw [lentoarray] at hi2;exact amn' i l n hi2 ⟩
      rw [haux,haux2]
      simp [mulArray,Aget]
      simp [Matrix.mul_apply,toarray]
      congr
      ext j
      cases' j with j hj
      rw [lentoarray] at hi2
      simp [Nat.mod_eq_of_lt hj]
      have haux3 : ((i / l) * m + j) / m = i / l
      · rw [Nat.add_div]
        simp
        split_ifs with h2
        · rw [Nat.mod_eq_of_lt hj] at h2
          grind
        · rw [← Nat.div_eq_zero_iff_lt] at hj
          rw [hj]
          rw [Nat.mul_div_cancel]
          simp
          exact hcas
          exact hcas
        · exact hcas
      simp [haux3]
      left
      congr
      rw [Nat.add_div]
      simp
      split_ifs with h2
      · grind
      · simp [hcas2]
      exact hcas2
  · push_neg at hcas
    have hcas2 : m = 0 ∨ l = 0 ∨ n = 0
    · grind
    cases' hcas2 with hcas2 hcas2
    cases hcas2
    simp
    ext h1 h2 h3
    · simp [lentoarray]
    · simp [mulArray,toarray]
    cases' hcas2 with hcas2 hcas2
    · cases hcas2
      simp [mulArray]
      rfl
    · cases hcas2
      ext h1 h2 h3
      · simp [lentoarray]
      · simp [lentoarray] at h3


def A1 (n : ℕ) : Array R := Array.ofFn (fun (i : Fin (n * n)) => if i.1 / n = i.1 % n then 1 else 0)

theorem toarrayone (n : ℕ) : toarray (1 : Matrix (Fin n) (Fin n) R) = (A1 n) := by
  ext h1 h2 h3
  · simp [lentoarray, A1]
  · simp [lentoarray] at h2
    let a := h1 / n
    let b := h1 % n
    have ha : a < n
    · grind
    have hb : b < n
    · grind
    let af : Fin n := ⟨a,ha⟩
    let bf : Fin n := ⟨b,hb⟩
    have hh1 : h1 = (af  * n + bf)
    · exact Eq.symm (Nat.div_add_mod' h1 n)
    simp [hh1,A1,Matrix.one_apply]
    split_ifs with  h2 h3 h4
    · rfl
    · rw [h2] at h3
      have haux : (b * n + b) / n = b % n
      · rw [← Nat.mod_eq_iff_lt]  at hb
        rw [hb]
        rw [mul_comm,Nat.mul_add_div]
        rw [Nat.mod_eq_iff_lt,← Nat.div_eq_zero_iff_lt] at hb
        rw [hb]
        simp
        grind
        grind
        grind
        grind
      · tauto
    · change (a * n + b) / n = b % n at h4
      rw [← Nat.mod_eq_iff_lt] at hb
      rw [hb] at h4
      rw [Nat.mod_eq_iff_lt] at hb
      rw [← Nat.div_eq_zero_iff_lt] at hb
      rw [mul_comm ,Nat.mul_add_div, hb] at h4
      simp at h4
      by_contra
      apply h2
      ext
      exact h4
      grind
      grind
      grind
      grind
    · rfl

lemma move_row_aux_1 (m n : ℕ) (hm : m ≠ 0) (i : Fin n) : i.1 < n * m := by
  cases' i with i hi
  simp only
  have haux : 1 ≤ m
  · omega
  exact lt_mul_of_lt_of_one_le hi haux

lemma move_row_aux_2 (m n l: ℕ) (hm : m ≠ 0) (i : Fin n) : i.1 + n * (m - (l+1)) < n * m := by
  cases' i with i hi
  simp only
  have haux : 1 ≤ m
  · omega
  have haux2 : m - (l+1) < m := by omega
  exact Nat.add_mul_lt_mul_of_lt_of_lt hi haux2


def move_row_aux (A : Array R) (ha : A.size = n * m) (i : Fin n) (j : Fin n) (k : ℕ) : Array R :=
  if hm : m = 0 then A else match k with
  | 0 => A.swap (i.1) (j.1) (by rw [ha]; apply move_row_aux_1; exact hm;) (by rw [ha]; apply move_row_aux_1; exact hm)
  | l + 1 => move_row_aux (A.swap (i.1 + n * (m - (l+1))) (j.1 + n * (m - (l+1))) (by rw  [ha]; apply move_row_aux_2; exact hm;) (by rw  [ha]; apply move_row_aux_2; exact hm;)) (by simp [ha]) i j l

def move_row (A : Array R) (ha : A.size = n * m) (i : Fin n) (j : Fin n) := move_row_aux A ha i j (m + 1)


def move_row'  (A : Array R) (ha : A.size = n * m) (i : Fin n) (j : Fin n) := Id.run do
  let mut run := A
  let mut hrun : run.size = n * m := by rw [ha]
  for h : l in [:m] do
    have h1 : l + i.1 * m < run.size := by cases' i with i hi; rw [hrun]; cases' h with h1 h2; grind

    run := Array.swap run (i.1 + l * m) (j.1 + l * m) (by sorry) (by sorry)
  return run

















open Matrix EuclideanDomain

def tolist (M :  Matrix (Fin n) (Fin m) R) : Array (Array R) := (Array.finRange n).map (fun a => (Array.finRange m).map (fun b => M a b))

def fix (M :  Matrix (Fin n) (Fin m) R) :  Matrix (Fin n) (Fin m) R := fun a b =>
  ((tolist M)[a]'(by simp [tolist];))[b]'(by grind[tolist])

theorem fix_eq (M :  Matrix (Fin n) (Fin m) R) : fix M = M := by
  ext a b
  simp [fix,tolist]

def EX := (AM 0 2 7  : Matrix (Fin 3) (Fin 3) ℤ )


@[simp]
def RM_def_left (i : Fin (n + 1)) (j : Fin m) (M : Matrix (Fin (n + 1)) (Fin (m)) R)  :
    ((RM : Matrix (Fin (n + 1)) (Fin (n + 1)) R ) * M ) i j =
    if h : i.val = n then
      M 0 j
    else
      M ⟨i + 1, by grind⟩ j := by
  unfold RM
  simp [Matrix.mul_apply]
  split_ifs with h1 h2 h3
  · rfl
  · cases h1
    simp at h2
  · by_contra hn
    grind
  · cases' i with i hi
    simp at h1 h3
    have haux : (⟨i, hi⟩ : Fin (n+1)) + 1 = ⟨↑(⟨i, hi⟩ : Fin (n +1)) + 1, by grind⟩
    · rw [@Fin.add_def,Fin.eq_mk_iff_val_eq]
      simp
      grind
    rw [haux]


@[simp]
lemma TM_def_left' {i j : Fin n} (M : Matrix (Fin n) (Fin m) R) (k : Fin m) : ((TM i j : Matrix (Fin n) (Fin n) R) * M) i k = M j k := by
  unfold TM
  simp [Matrix.mul_apply]
  tauto

@[simp]
lemma TM_def_left'' {i j : Fin n} (M : Matrix (Fin n) (Fin m) R) (k : Fin m) : ((TM i j : Matrix (Fin n) (Fin n) R) * M) j k = M i k := by
  unfold TM
  simp [Matrix.mul_apply]

@[simp]
lemma TM_def_right' {i j : Fin m} (M : Matrix (Fin n) (Fin m) R) (k : Fin n) : ( M * (TM i j : Matrix (Fin m) (Fin m) R) ) k i = M k j := by
  unfold TM
  simp [Matrix.mul_apply]
  simp [Finset.sum_ite,Finset.sum_eq_single_of_mem]
  intro h
  cases h
  simp [@Finset.filter_filter]

@[simp]
lemma TM_def_right'' {i j : Fin m} (M : Matrix (Fin n) (Fin m) R) (k : Fin n) : ( M * (TM i j : Matrix (Fin m) (Fin m) R) ) k j = M k i := by
  unfold TM
  simp [Matrix.mul_apply]
  simp [Finset.sum_ite,Finset.sum_eq_single_of_mem]
  split_ifs with h1 h2
  · cases h1
    simp [@Finset.filter_filter]
  · have haux : ∑ x ∈ {x | ¬x = j} with x = i, M k x = ∑ x ∈ {x | x = i}, M k x
    · simp [@Finset.filter_filter]
      have haux2 : (fun a => ¬a = j ∧ a = i) = (fun x => x = i)
      · ext a
        grind
      simp [Finset.filter,haux2]
    rw [haux]
    simp [Finset.sum_eq_single_of_mem]

@[grind]
lemma TM_def_right'''  {i j : Fin m} (M : Matrix (Fin n) (Fin m) R) (k : Fin n) (l : Fin m) (hl : l ≠ j) (hl2 : l ≠ i): ( M * (TM i j : Matrix (Fin m) (Fin m) R) ) k l = M k l := by
  unfold TM
  simp [Matrix.mul_apply]
  simp [Finset.sum_ite,Finset.sum_eq_single_of_mem]
  grind

@[grind]
lemma TM_def_left'''  {i j : Fin n} (M : Matrix (Fin n) (Fin m) R) (k : Fin n) (l : Fin m) (hl : k ≠ j) (hl2 : k ≠ i): ((TM i j : Matrix (Fin n) (Fin n) R) * M) k l = M k l := by
  unfold TM
  simp [Matrix.mul_apply]
  grind

@[simp]
lemma TM_def_left {i j : Fin n} (M : Matrix (Fin n) (Fin m) R) (k : Fin n) (l : Fin m) : ((TM i j : Matrix (Fin n) (Fin n) R) * M) k l = (if k = i then M j l else if k = j then M i l else M k l) := by
  by_cases h1 : k = i
  · simp only [h1, TM_def_left', ↓reduceIte]
  · by_cases h2 : k = j
    · cases h2
      rw [TM_def_left'']
      simp [h1]
    · grind

@[simp]
lemma TM_def_right {i j : Fin m} (M : Matrix (Fin n) (Fin m) R) (k : Fin n) (l : Fin m) : ( M * (TM i j : Matrix (Fin m) (Fin m) R) ) k l = if l = i then M k j else if l = j then M k i else M k l := by
  by_cases h1 : l = i
  · simp [h1]
  · by_cases h2 : l = j
    · cases h2
      simp [h1]
    · grind




lemma AM_inv (i j : Fin n) (k : R) (hi : i ≠ j): (AM i j k) * (AM i j (-k)) = 1 := by
  ext a b
  unfold AM
  simp [Matrix.mul_apply]
  simp [Finset.sum_ite]
  rw [one_apply]
  split_ifs at * with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  any_goals
    simp
    grind
  any_goals
    simp at *
    left
    rw [Finset.card_eq_zero.mpr ?_]
    · simp
    · grind

@[simp]
lemma Finset.sum_eq.{u_1, u_3} {ι : Type u_1} [Fintype ι ] [DecidableEq ι] {M : Type u_3} [AddCommMonoid M] (i : ι) (f : ι → M) :
    ∑ x with (x = i), f x = f i := by
  have haux : ∑ x with x = i, f x = ∑ x ∈ {i}, f x
  · refine Finset.sum_equiv (Equiv.refl _)  ?_ ?_
    · simp
    · simp
  simp [haux]

@[simp]
lemma Finset.sum_eq_neq.{u_1, u_3} {ι : Type u_1} [Fintype ι ] [DecidableEq ι] {M : Type u_3} [AddCommMonoid M] (i j : ι) (f : ι → M) (hij : i ≠ j):
    ∑ x ∈ {x | ¬x = i} with j = x, f x = f j := by
  have haux2 : ∑ x ∈ {x | ¬x = i} with j = x, f x = ∑ x ∈ {x | x = j}, f x
  · refine Finset.sum_equiv (Equiv.refl _)  ?_ ?_
    · simp
      grind
    · simp
  rw [haux2]
  simp

@[simp]
lemma Finset.sum_eq_neq'.{u_1, u_3} {ι : Type u_1} [Fintype ι ] [DecidableEq ι] {M : Type u_3} [AddCommMonoid M] (i j : ι) (f : ι → M) (hij : i ≠ j):
    ∑ x ∈ {x | ¬x = j} with x = i, f x = f i := by
  have haux2 : ∑ x ∈ {x | ¬x = j} with x = i, f x = ∑ x ∈ {x | x = i}, f x
  · refine Finset.sum_equiv (Equiv.refl _)  ?_ ?_
    · simp
      grind
    · simp
  rw [haux2]
  simp


@[simp]
lemma AM_def_left {i j : Fin n} (hij : i ≠ j) (M : Matrix (Fin n) (Fin m) R) ( l : R) (k : Fin m) : ((AM i j l : Matrix (Fin n) (Fin n) R) * M) j k = M j k + l * (M i k) := by
  unfold AM
  simp [Matrix.mul_apply]
  rw [Finset.sum_ite,Finset.sum_ite]
  simp [hij]
  grind

 @[simp]
 lemma AM_def_right {i j : Fin m} (hij : i ≠ j) (M : Matrix (Fin n) (Fin m) R) (l : R) (k : Fin n) : (M * (AM i j l : Matrix (Fin m) (Fin m) R) ) k i = l * M k j + M k i := by
  unfold AM
  simp [Matrix.mul_apply]
  rw [Finset.sum_ite,Finset.sum_ite]
  simp [hij]
  grind

lemma TM_inv (i j : Fin n) (h : i ≠ j): (TM i j) * (TM i j : Matrix (Fin n) (Fin n) R) = 1 := by
  ext a b
  unfold TM
  simp [Matrix.mul_apply]
  simp [Finset.sum_ite]
  rw [one_apply]
  split_ifs at *
  any_goals grind

def recorta  (M : Matrix (Fin n) (Fin m) R ) :  Matrix (Fin (n - 1)) (Fin (m - 1)) R := fun a b =>
  M ⟨a + 1,by grind⟩ ⟨b + 1, by grind⟩

def completa (M : Matrix (Fin n) (Fin m) R ) (l : R) : Matrix (Fin (n + 1)) (Fin (m + 1)) R  := by
  intro a b
  cases n with
  | zero => exact (if b = 0 then l else 0)
  | succ nn => cases m with
    | zero => exact (if a = 0 then l else 0)
    | succ mm => exact if a = 0 then (if b = 0 then l  else 0) else
      if b = 0 then 0 else (M ⟨(↑a - 1), by grind⟩ ⟨(b - 1), by grind⟩)

def recortafila  (M : Matrix (Fin (n + 1)) (Fin m) R ) : Matrix (Fin n) (Fin m) R  := fun a b =>
  M ⟨a + 1, by grind⟩ b

def completafilazero  (M : Matrix (Fin n) (Fin m) R ) :  Matrix (Fin (n + 1)) (Fin m) R := fun a b =>
  if h : a.val < n then
    M ⟨a.val, h⟩ b
  else
    0

lemma completarecortafilazero (M : Matrix (Fin (n + 1)) (Fin m) R ) (h : ∀ b, M 0 b = 0) :
    completafilazero (recortafila M) = (RM )  * M := by
  ext a b
  simp [completafilazero,recortafila]
  split_ifs with i1 i2 i3
  · grind
  · rfl
  · rw [h]
  · grind


@[simp]
lemma completa_zero_zero (M : Matrix (Fin 0) (Fin 0) R ) (l : R) (a b : Fin 1) : completa M l a b = l := by
  simp [completa]
  grind

@[simp]
lemma completa_zero (M : Matrix (Fin 0) (Fin m) R ) (l : R) (a : Fin 1) (b : Fin (m + 1)) :
    completa M l a b = (if b = 0 then l else 0) := by
  simp [completa]

@[simp]
lemma completa_zero' (M : Matrix (Fin n) (Fin 0) R ) (l : R) (a : Fin (n + 1)) (b : Fin 1) :
    completa M l a b = (if a = 0 then l else 0) := by
  simp [completa, Nat.casesAuxOn]
  cases' n with n hn
  · simp
    grind
  · simp

@[simp]
lemma completa_succ (M : Matrix (Fin (n + 1)) (Fin (m + 1) ) R ) (l : R) (a : Fin (n + 2)) ( b : Fin (m + 2))  :
    completa M l a b = (if a = 0 then (if b = 0 then l else 0) else  if b = 0 then 0 else M (⟨a - 1, by grind⟩) (⟨b - 1, by grind⟩ )) := by
  simp [completa]

lemma recorta_completa (M : Matrix (Fin n) (Fin m) R) (l : R) : recorta (completa M l)  = M := by
  ext a b
  dsimp [recorta,completa,Nat.casesAuxOn]
  cases' n with nn
  · simp only [Nat.reduceAdd, Nat.rec_zero]
    cases' a with a ha
    ring_nf at ha
    grind
  · cases' m with mm
    · cases b
      grind
    · simp


lemma mul_completa (A : Matrix (Fin n) (Fin n) R) (M : Matrix (Fin n) (Fin m) R) (l : R) :
    completa (A * M) l = (completa A 1) * (completa M l) := by
  ext a b
  cases' n with n
  · simp [mul_apply]
  · cases' m with m
    · simp [mul_apply]
    · simp [mul_apply]
      split_ifs with h1 h2 h3
      · simp
      · simp
      · simp
      · simp [Finset.sum_fin_eq_sum_range,Finset.sum_range_succ']

lemma completa_transpose  (M : Matrix (Fin n) (Fin m) R) (l : R) : transpose (completa M l) = completa (transpose M) l := by
  ext a b
  cases' n with n
  · simp
  · cases' m with m
    · simp
    · simp
      split_ifs with h1 h2 h3
      · rfl
      · rfl
      · rfl
      · simp

lemma mul_completa'  (M : Matrix (Fin n) (Fin m) R) (A : Matrix (Fin m) (Fin m) R) (l : R) :
    completa (M * A) l = (completa M l) * (completa A 1) := by
  ext a b
  cases' n with n
  · simp [mul_apply]
    cases' m with m
    · simp
      grind
    · simp
  · cases' m with m
    · simp [mul_apply]
    · simp [mul_apply]
      split_ifs with h1 h2 h3
      · simp
      · simp
      · simp
      · simp [Finset.sum_fin_eq_sum_range,Finset.sum_range_succ']

def is_pivot (M : Matrix (Fin n) (Fin m) R) (i : Fin n) (j : Fin m) : Bool :=
  decide (M i j ≠ 0 ∧ ((∃ l, l ≠ j ∧ M i l ≠ 0) ∨ (∃ l, l ≠ i ∧ M l j ≠ 0)))



def all_pivots (M : Matrix (Fin n) (Fin m) R) : List (Fin n × Fin m) :=
  (((List.finRange m).map
    (fun j => (List.finRange n
              ).map (fun i => (i,j)))
    ).flatten
    ).filter (fun a => is_pivot M a.1 a.2)

@[simp]
lemma all_pivots_mem_TM_left (M : Matrix (Fin n) (Fin m) R) (a i j: Fin n) (b : Fin m)  (h1 : a ≠ i) (h2 : a ≠ j) :
    ((a, b) ∈ all_pivots (TM i j  * M)) ↔ (a, b) ∈ (all_pivots M) := by
  unfold all_pivots at *
  simp [is_pivot,h1,h2]
  grind

@[simp]
lemma all_pivots_mem_TM_left'  (M : Matrix (Fin n) (Fin m) R) (i j: Fin n) (b : Fin m) :
    (i, b) ∈ all_pivots (TM i j  * M) ↔ (j, b) ∈ all_pivots M := by
  unfold all_pivots
  simp [is_pivot]
  grind

@[simp]
lemma all_pivots_mem_TM_left''  (M : Matrix (Fin n) (Fin m) R) (i j: Fin n) (b : Fin m)  :
    (j, b) ∈ all_pivots (TM i j  * M) ↔  (i, b) ∈ all_pivots M := by
  unfold all_pivots
  simp [is_pivot]
  grind

instance : LE R where
  le := EuclideanDomain.r

instance : LE (R × Fin n × Fin m) where
  le := Prod.Lex EuclideanDomain.r (Prod.Lex LT.lt LT.lt)

@[grind =]
lemma def_le_prod (a b : (R × Fin n × Fin m)) : a ≤ b ↔ Prod.Lex EuclideanDomain.r (Prod.Lex LT.lt LT.lt) a b := by
  rfl


instance : DecidableRel (LE.le : R → R → Prop) := DecEuclideanDomain.decidable_r

instance : DecidableRel (LE.le : (R × Fin n × Fin m) → (R × Fin n × Fin m) → Prop) := Prod.Lex.instDecidableRelOfDecidableEq

instance : Min R := minOfLe

instance : Min (R × Fin n × Fin m) := minOfLe

instance : IsWellFounded _ (LE.le :  R → R  → Prop) where
  wf := EuclideanDomain.r_wellFounded

-- instance : IsWellFounded (Fin n) (LT.lt ) := Finite.to_wellFoundedLT

-- instance : IsWellFounded _ (Prod.Lex (LT.lt : Fin n → Fin n → Prop) (LT.lt : Fin n → Fin n → Prop)) := Prod.Lex.instIsWellFounded

instance : IsWellFounded _ (LE.le : (R × Fin n × Fin m) → (R × Fin n × Fin m)  → Prop) := Prod.Lex.instIsWellFounded

def smallest_pivot (M : Matrix (Fin n) (Fin m) R) : Option (R × Fin n × Fin m) :=
  ((all_pivots M).map (fun i => (M i.1 i.2, i))).min?

example (L : List (R × Fin n × Fin m)) (a : R × Fin n × Fin m) : L.min? = some a ↔ L = [a] ∨ (∃ l, ∃ c, l.min? = some c ∧ L = a :: l ∧ a = min a c)
  := by
  induction' L with t L2 hL
  · simp
  · induction' L2 with s L3 hL3
    · simp [List.min?]
    · simp [List.min?, foldl] at *


def reorg_smallest_pivot (M : Matrix (Fin (n + 1)) (Fin (m + 1)) R) (sp : R × Fin (n + 1) × Fin (m + 1)) (hM : smallest_pivot M = some sp) :
    smallest_pivot ((TM ⟨0,by grind⟩ sp.2.1 : Matrix _ _ R) * M ) = some (sp.1,⟨0, by grind⟩,  sp.2.2)  := by
  by_cases hcas : sp.2.1 = 0
  · rw [hcas]
    simp
    have haux : (TM 0 0 ) * M = M
    · ext a b
      simp
      split_ifs with h1
      · rw [h1]
      · rfl
    rw [haux,hM,← hcas]
  · unfold smallest_pivot at hM ⊢
    unfold List.min? at hM ⊢


    · rw [List.min?_eq_some_iff] at hM ⊢
      cases' hM with hM1 hM2
      simp at hM1
      choose a b ha hb using hM1
      rw [← hb] at hM2 ⊢
      fconstructor
      · simp
        exact ha
      · simp only [Prod.mk.injEq]
        simp
        intro V a1 b1 a2 b2 ha2b2 h3 h4 h5
        cases h4
        cases h5
        by_cases ha1 : a1 = 0
        · rw [ha1] at ha2b2
          simp at ha2b2
          simp [ha1] at  h3  ⊢
          have hM2' := hM2 (M a b1, a, b1)
          simp at hM2'
          specialize hM2' ha2b2
          cases h3
          grind
        · simp [ha1] at h3
          by_cases ha' : a1 = a
          · cases ha'
            simp at h3
            cases h3
            simp [ha1] at ha2b2
            specialize hM2 (M 0 b1, 0 ,b1)
            simp at hM2
            specialize hM2 ha2b2
            grind
          · simp [ha'] at h3
            simp [ha1,ha'] at ha2b2
            cases h3
            specialize hM2 (M a1 b1, a1, b1)
            simp at hM2
            specialize hM2 ha2b2
            grind
      · refine Std.IsLinearOrder.of_le ?_ ?_ ?_
        · fconstructor
          · intro a b ha hb
            cases' a with R1 a1
            cases' b with R2 a2
            cases' a1 with a1 b1
            cases' a2 with a2 b2
            cases' ha with _ _ _ _ h5 h9 h10 h11 h12 h6
            cases' hb with _ _ _ _ h7 _ _ _ h13 h8
            have h3 := DER.r_wellFounded
            by_contra hneg
            have h4 := h3.asymmetric
            exact h4 _ _ h5 h7
            have h3 := DER.r_wellFounded
            by_contra hneg
            have h4 := h3.asymmetric
            exact h4 _ _ h5 h5
            cases' hb with _ _ _ _ h7 _ _ _ h13 h8
            have h3 := DER.r_wellFounded
            by_contra hneg
            have h4 := h3.asymmetric
            exact h4 _ _ h7 h7
            grind
        · fconstructor
          intro a b c h1 h2
          cases' a with R1 a1
          cases' b with R2 a2
          cases' a1 with a1 b1
          cases' a2 with a2 b2
          cases' c with R3 a3
          cases' a3 with a3 b3
          cases' h1 with _ _ _ _ h5 _ _ _ _ h6
          cases' h2 with _ _ _ _ h7 _ _ _ _ h8
          fconstructor
          · apply?








































#eval smallest_pivot !![(-2: ℤ ), 3 , 0; -5 , -3  , 2]


def nonzeros_first_row (M : Matrix (Fin (n + 1)) (Fin (m + 1)) R) : List (Fin (m + 1)) :=
  (List.finRange (m + 1)).filter (fun a => decide (M 0 a ≠ 0))

def nonzeros_first_column (M : Matrix (Fin (n + 1)) (Fin (m + 1)) R) : List (Fin (n + 1)) :=
  (List.finRange (n + 1)).filter (fun a => decide (M a 0 ≠ 0))

def nonzero_values_first_row (M : Matrix (Fin (n + 1)) (Fin (m + 1)) R) : List R :=
  (nonzeros_first_row M).map (fun a => M 0 a)

def nonzero_values_first_column (M : Matrix (Fin (n + 1)) (Fin (m + 1)) R) : List R :=
  (nonzeros_first_column M).map (fun a => M a  0)

def reduce_first_row (M : Matrix (Fin (n + 1)) (Fin (m + 1)) R) : (Matrix (Fin (n + 1)) (Fin (m + 1)) R) :=
  match (nonzeros_first_row M) with
  | [] =>  M
  | c :: [] => if decide (c = 0) then M else M * (TM 0 c)
  | c :: (d :: e) => if decide ((M 0 c) ≺ (M 0 d)) then
      M * (AM  d c  (- (M 0 d / M 0 c)))
    else
      M * (AM c d  (- (M 0 c / M 0 d)))


def Lvalue (L : List R) : ℕ × R × R :=
  match L with
  | [] => (0,0,0)
  | _ :: [] => (1,0,0)
  | c :: (d :: L) => ((Lvalue L).1 + 2, c ,d)

instance : WellFoundedRelation (ℕ × R × R) := Prod.lex {
  rel := _
  wf := wellFounded_lt
} (Prod.lex {
  rel := _
  wf := EuclideanDomain.r_wellFounded
} {
  rel := _
  wf := EuclideanDomain.r_wellFounded
})




def zero_first_row  (M : Matrix (Fin (n + 1)) (Fin (m + 1)) R) : (Matrix (Fin (n + 1)) (Fin (m + 1)) R) :=
  let nz := nonzeros_first_row M
  if hnz : nz.length < 2 then M
  else
    let M' := reduce_first_row M
    zero_first_row M'
termination_by (Lvalue (nonzero_values_first_row M))
decreasing_by
  simp at hnz
  have hznem : nz ≠ []
  · grind
  have hnzlen : 1 ≤ nz.tail.length
  · grind
  have hznem' : nz.tail ≠ []
  · grind
  let i := nz.head hznem
  let j := nz.tail.head hznem'
  have hi : M 0 i ≠ 0
  · grind [nonzeros_first_row]
  have hj : M 0 j ≠ 0
  · grind [nonzeros_first_row]
  have hij : j ≠ i
  · sorry

  by_cases hcas : M 0 i ≺ M 0 j
  · have hMj : M' 0 j = (M 0 j) % (M 0 i)
    · simp [M',reduce_first_row,nz]
      have haux : nonzeros_first_row M = nz := rfl
      rw [haux]
      have hnzaux : nz = i :: j :: nz.tail.tail
      · grind
      rw [hnzaux]
      simp [hcas]
      simp [hij]
      have haix := div_add_mod (M 0 j) (M 0 i)
      grind




























variable ( a b : R)



def smallestpivot (M : Matrix (Fin n) (Fin m) R) : Option (Fin n × Fin m) :=
  (all_pivots M).foldl
    ((fun acc p =>
      match acc with
      | none => some p
      | some q =>
          if M p.1 p.2 ≺  M q.1 q.2  then
            some p
          else
            some q))
    none
