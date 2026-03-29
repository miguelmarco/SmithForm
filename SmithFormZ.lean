import Smith.Basic

def readAllInts : IO (List ℤ) := do
  let stdin ← IO.getStdin
  let input ← stdin.readToEnd
  let tokens := input.splitOn " " |>.filter (· ≠ "") |>.flatMap (·.splitOn "\n") |>.filter (· ≠ "")
  return tokens.filterMap String.toInt?

open AMat

def main : IO Unit := do
  let allInts ← readAllInts
  match allInts with
  | [] => IO.eprintln "Error: No se recibió n"
  | [n] => IO.eprintln "Error: No se recibió m"
  | n_int :: m_int :: rest =>
    let n := n_int.toNat
    let m := m_int.toNat
    if hlen : rest.length ≠ n * m then
      IO.eprintln s!"Error: Not {n*m} entries"
    else
      -- 1. Construimos la matriz LUM
      let flatArray := rest |>.toArray
      let A : Mat n m ℤ  := {
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
