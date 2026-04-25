import Smith.Basic
import Smith.Polynomials.Polynomial

open APolynomial

def readRat (S : String) :  ℚ :=
  let P := S.splitOn "/"
  if h : P.length < 2 then
    match S.toInt? with
    | none =>  0
    | some a => a
  else
    let a := (P[0]'(by omega)).toInt?
    let b := (P[1]'(by omega)).toInt?
    match a, b with
    | some c, some d => (c : ℚ) / (d: ℚ)
    | _ , _ => 0

def readPoly (S : String) : Poly ℚ :=
  { Ar := clean_zeros (((S.splitOn " ").filter (· ≠ "")).map readRat).toArray,
    hAr := by apply clean_zeros_prop
  }


def readAllInput : IO ( ℕ × ℕ × List (Poly ℚ)) := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let tokens := (input.splitOn "\n").filter ( · ≠ "")
  match tokens with
  | [] => return (0, (0, []))
  | [n]  => match n.toNat? with
            | none => return (0, (0, []))
            | some a => return (a, (0, []))
  | n :: m :: rest => match n.toNat?, m.toNat? with
                      | some a , some b => return (a ,(b, rest.map readPoly))
                      | _ , _ => return (0, 0, [])
open AMat

def main : IO Unit := do
  let allInts ← readAllInput
  match allInts with
  | (0, _) => IO.eprintln "Error: No se recibió n"
  | (_ , (0 ,_)) => IO.eprintln "Error: No se recibió m"
  | (_, (_, [])) => IO.eprintln "Error: No se recibieron coeficientes"
  | (n, (m, polys)) =>
    if hlen : polys.length ≠ n * m then
      IO.eprintln s!"Error: Not {n*m} entries in {polys}"
    else
      let flatArray := polys |>.toArray
      let A : Mat n m (Poly ℚ)  := {
        Ar := flatArray
        hAr := by grind
      }
      let result := SmithForm A
      for hi: i in [:n] do
        let mut rowStr := ""
        for hj: j in [:n] do
          let val := Aget result.IL ⟨i, Membership.get_elem_helper hi rfl⟩
            ⟨j, Membership.get_elem_helper hj rfl⟩
          rowStr := rowStr ++ s!"{val} "
        IO.println rowStr
      IO.println ""
      for hi: i in [:n] do
        let mut rowStr := ""
        for hj: j in [:n] do
          let val := Aget result.L ⟨i, Membership.get_elem_helper hi rfl⟩
            ⟨j, Membership.get_elem_helper hj rfl⟩
          rowStr := rowStr ++ s!"{val} "
        IO.println rowStr
      IO.println ""
      for hi: i in [:n] do
        let mut rowStr := ""
        for hj: j in [:m] do
          let val := Aget result.M ⟨i, Membership.get_elem_helper hi rfl⟩
            ⟨j, Membership.get_elem_helper hj rfl⟩
          rowStr := rowStr ++ s!"{val} "
        IO.println rowStr
      IO.println ""
      for hi: i in [:m] do
        let mut rowStr := ""
        for hj: j in [:m] do
          let val := Aget result.R ⟨i, Membership.get_elem_helper hi rfl⟩
            ⟨j, Membership.get_elem_helper hj rfl⟩
          rowStr := rowStr ++ s!"{val} "
        IO.println rowStr
      IO.println ""
      for hi: i in [:m] do
        let mut rowStr := ""
        for hj: j in [:m] do
          let val := Aget result.IR ⟨i, Membership.get_elem_helper hi rfl⟩
            ⟨j, Membership.get_elem_helper hj rfl⟩
          rowStr := rowStr ++ s!"{val} "
        IO.println rowStr
