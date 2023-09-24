import DArray

def main := do
  let a := DArray.ex0 |>.push 1 |>.set ⟨0, by simp⟩ 42
  IO.println a 
  IO.println a.size
  IO.println a.size'
  IO.println $ a.get ⟨0, by simp⟩
  IO.println $ DArray.ex0 |>.push 1 |>.set ⟨0, by simp⟩ 42 -- |>.get ⟨0, by simp⟩

  IO.println $ ArrayPair.empty |>.push (1, "One")


