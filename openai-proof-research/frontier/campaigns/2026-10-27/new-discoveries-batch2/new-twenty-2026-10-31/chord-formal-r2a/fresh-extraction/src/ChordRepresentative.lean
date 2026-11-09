import ChordCore
namespace Chord

def blockMate (i : Nat) : Nat :=
  if i < 3 then i+3 else if i < 6 then i-3
  else if i % 2 = 0 then i+1 else i-1

theorem blockMate_lt (n i : Nat) (hn : 3 ≤ n) (hi : i < 2*n) : blockMate i < 2*n := by
  unfold blockMate
  repeat' (first | omega | split)

theorem blockMate_involutive (i : Nat) : blockMate (blockMate i) = i := by
  unfold blockMate
  repeat' (first | omega | split)

theorem blockMate_ne (i : Nat) : blockMate i ≠ i := by
  unfold blockMate
  repeat' (first | omega | split)

def r3Block (n : Nat) (hn : 3 ≤ n) : Diagram n where
  partner i := ⟨blockMate i.val, blockMate_lt n i.val hn i.isLt⟩
  involutive i := Fin.ext (blockMate_involutive i.val)
  noFixed i h := blockMate_ne i.val (congrArg Fin.val h)

theorem representative_spec (n : Nat) (hn : 3 ≤ n) : IsRepresentative (r3Block n hn) := by
  intro i
  rfl

end Chord
