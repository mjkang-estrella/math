import MaskCNF
import Normalize
import Lean
open Lean Elab Command
namespace Percolation.MaskChain
abbrev Entails (c : MaskRUP.Mask) : Prop :=
  ∀ v : SatVar → Bool, (∀ d ∈ normalizedCNF5, CNF.Holds v d) →
    MaskRUP.Holds (v ∘ decodeVar) c
theorem input_sound (c : CNF.NClause) (m : MaskRUP.Mask)
    (eq : MaskRUP.encode c = m)
    (hc : ∀ v : SatVar → Bool, (∀ d ∈ normalizedCNF5, CNF.Holds v d) →
      CNF.Holds (v ∘ decodeVar) c) : Entails m := by
  intro v hv
  rw [← eq]
  exact (MaskRUP.encode_cnf _ _).mpr (hc v hv)
theorem nil_hints (v : Nat → Bool) :
    ∀ h ∈ ([] : List MaskRUP.Hint), MaskRUP.Holds v h.1 := by simp
theorem cons_hints (v : Nat → Bool) (h : MaskRUP.Hint) (hs : List MaskRUP.Hint)
    (hc : MaskRUP.Holds v h.1)
    (ht : ∀ d ∈ hs, MaskRUP.Holds v d.1) :
    ∀ d ∈ h :: hs, MaskRUP.Holds v d.1 := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hc
  · exact ht d hd
private def pairE (a b x y : Expr) : Expr :=
  mkApp4 (mkConst ``Prod.mk [.zero,.zero]) a b x y
private def maskE (p n : String) : Expr :=
  pairE (mkConst ``Nat) (mkConst ``Nat) (mkNatLit p.toNat!) (mkNatLit n.toNat!)
elab "mask_input " data:str : command => do
  let cols := data.getString.splitOn "|"
  let idx := cols[0]!
  let c := mkConst (Name.str `Percolation.MaskChain ("inputClause" ++ idx))
  let m := maskE cols[1]! cols[2]!
  let eq := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``MaskRUP.Mask) m
  let proof := mkApp4 (mkConst ``input_sound) c m eq
    (mkConst (Name.str `Percolation.MaskChain ("inputList" ++ idx)))
  let ty ← liftTermElabM <| Meta.inferType proof
  let nm := Name.str `Percolation.MaskChain ("clause" ++ idx)
  liftCoreM <| addDecl (.thmDecl {name := nm, levelParams := [], type := ty, value := proof})
elab "mask_chain " data:str : command => do
  let nat := mkConst ``Nat
  let bool := mkConst ``Bool
  let mask := mkConst ``MaskRUP.Mask
  let unit := mkApp2 (mkConst ``Prod [.zero,.zero]) nat bool
  let hint := mkConst ``MaskRUP.Hint
  let mkName := fun s => Name.str `Percolation.MaskChain s
  for row in data.getString.splitOn "\n" do
    if row.isEmpty then continue
    let cols := row.splitOn "|"
    let idx := cols[0]!
    let c := maskE cols[1]! cols[2]!
    let mut hs := mkApp (mkConst ``List.nil [.zero]) hint
    let mut entries : Array (String × Expr × Expr) := #[]
    for item in (cols[3]!.splitOn ";").reverse do
      let vals := item.splitOn ","
      let m := maskE vals[1]! vals[2]!
      let u := if vals[3]! == "x" then mkApp (mkConst ``Option.none [.zero]) unit
        else mkApp2 (mkConst ``Option.some [.zero]) unit
          (pairE nat bool (mkNatLit vals[3]!.toNat!)
            (mkConst (if vals[4]! == "1" then ``Bool.true else ``Bool.false)))
      let h := pairE mask (mkApp (mkConst ``Option [.zero]) unit) m u
      entries := entries.push (vals[0]!, h, hs)
      hs := mkApp3 (mkConst ``List.cons [.zero]) hint h hs
    let ck := mkName ("check" ++ idx)
    let value := mkApp2 (mkConst ``Eq.refl [.succ .zero]) bool (mkConst ``Bool.true)
    let type := mkApp3 (mkConst ``Eq [.succ .zero]) bool
      (mkApp2 (mkConst ``MaskRUP.check) c hs) (mkConst ``Bool.true)
    liftCoreM <| addDecl (.thmDecl {name := ck, levelParams := [], type, value})
    let proof ← liftTermElabM do
      Meta.withLocalDeclD `v (← mkArrow (mkConst ``SatVar) bool) fun v => do
        let premise ← Meta.mkAppM ``Entails #[c]
        let ty ← Meta.whnf premise
        let .forallE _ _ tail _ := ty | throwError "expected entails"
        let .forallE _ ht _ _ := tail.instantiate1 v | throwError "expected hypothesis"
        Meta.withLocalDeclD `hv ht fun hv => do
          let val ← Meta.mkAppM ``Function.comp #[v, mkConst ``decodeVar]
          let mut hp := mkApp (mkConst ``nil_hints) val
          for (id,h,tail) in entries do
            let hc := mkApp2 (mkConst (mkName ("clause" ++ id))) v hv
            hp := mkApp5 (mkConst ``cons_hints) val h tail hc hp
          let result := mkApp5 (mkConst ``MaskRUP.check_sound) c hs (mkConst ck) val hp
          Meta.mkLambdaFVars #[v,hv] result
    let type := mkApp (mkConst ``Entails) c
    liftCoreM <| addDecl (.thmDecl {name := mkName ("clause" ++ idx), levelParams := [], type, value := proof})
end Percolation.MaskChain
