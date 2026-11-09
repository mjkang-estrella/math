import ChordSanity
namespace Chord
set_option maxRecDepth 10000
set_option maxHeartbeats 6000000
/-- Literal source/reviewer word 12341234. -/
def exception3 : Diagram 4 where
  partner i := ⟨([4,5,6,7,0,1,2,3].getD i.val 0) % 8, Nat.mod_lt _ (by decide)⟩
  involutive := by decide
  noFixed := by decide
def side83 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Sides 4 := fun i : Fin 8 => if i.val=0 then b0 else if i.val=1 then b1 else if i.val=2 then b2 else if i.val=3 then b3 else if i.val=4 then b4 else if i.val=5 then b5 else if i.val=6 then b6 else b7
theorem side83_complete (c : Sides 4) : c = side83 (c ⟨0,by decide⟩) (c ⟨1,by decide⟩) (c ⟨2,by decide⟩) (c ⟨3,by decide⟩) (c ⟨4,by decide⟩) (c ⟨5,by decide⟩) (c ⟨6,by decide⟩) (c ⟨7,by decide⟩) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i =>
            cases i using Fin.cases with
            | zero => rfl
            | succ i =>
              cases i using Fin.cases with
              | zero => rfl
              | succ i =>
                have : i = 0 := Fin.eq_zero i
                subst i
                rfl
end Chord
