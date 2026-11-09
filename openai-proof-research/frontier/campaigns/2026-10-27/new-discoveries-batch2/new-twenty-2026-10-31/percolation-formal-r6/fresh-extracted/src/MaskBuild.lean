import MaskRUP
import Lean
open Lean Elab Command
namespace Percolation.MaskRUP
-- Construct expressions only. addDecl and the standalone checker validate the proofs.
elab "mask_data " data:str : command => do
  let nat := mkConst ``Nat
  let bool := mkConst ``Bool
  let mask := mkConst ``Mask
  let unit := mkApp2 (mkConst ``Prod [.zero,.zero]) nat bool
  let opt := mkApp (mkConst ``Option [.zero]) unit
  let hint := mkConst ``Hint
  let mkPair := fun (a b x y : Expr) => mkApp4 (mkConst ``Prod.mk [.zero,.zero]) a b x y
  let mkMask := fun (p n : String) => mkPair nat nat (mkNatLit p.toNat!) (mkNatLit n.toNat!)
  for row in data.getString.splitOn "\n" do
    if row.isEmpty then continue
    let cols := row.splitOn "|"
    let idx := cols[0]!
    let c := mkMask cols[1]! cols[2]!
    let mut hs := mkApp (mkConst ``List.nil [.zero]) hint
    let pieces := (cols[3]!.splitOn ";").reverse
    for item in pieces do
      let vals := item.splitOn ","
      let m := mkMask vals[0]! vals[1]!
      let u := if vals[2]! == "x" then mkApp (mkConst ``Option.none [.zero]) unit
        else mkApp2 (mkConst ``Option.some [.zero]) unit
          (mkPair nat bool (mkNatLit vals[2]!.toNat!)
            (mkConst (if vals[3]! == "1" then ``Bool.true else ``Bool.false)))
      let h := mkPair mask opt m u
      hs := mkApp3 (mkConst ``List.cons [.zero]) hint h hs
    let ck := Name.str `Percolation.MaskRUP ("rawCheck" ++ idx)
    let value := mkApp2 (mkConst ``Eq.refl [.succ .zero]) bool (mkConst ``Bool.true)
    let type := mkApp3 (mkConst ``Eq [.succ .zero]) bool
      (mkApp2 (mkConst ``check) c hs) (mkConst ``Bool.true)
    liftCoreM <| addDecl (.thmDecl {name := ck, levelParams := [], type, value})
    let snd := Name.str `Percolation.MaskRUP ("rawSound" ++ idx)
    let proof := mkApp3 (mkConst ``check_sound) c hs (mkConst ck)
    let ty ← liftTermElabM <| Meta.inferType proof
    liftCoreM <| addDecl (.thmDecl {name := snd, levelParams := [], type := ty, value := proof})
end Percolation.MaskRUP
