import Mathlib.Data.List.FinRange
namespace Nut8
/-- Row-major bit encoding of a labelled simple graph. -/
def graphBit (n code i j : Nat) : Bool := code.testBit (i*n+j)
/-- A certificate gives the original vertex at each target position. -/
def graphIsoCheck (n a b : Nat) (p : List Nat) : Bool :=
  decide (p.Perm (List.range n)) &&
  (List.range n).all (fun i => (List.range n).all (fun j =>
    graphBit n b i j == graphBit n a (p[i]?.getD n) (p[j]?.getD n)))

theorem graphIsoCheck_sound (n a b : Nat) (p : List Nat)
    (h : graphIsoCheck n a b p = true) :
    p.Perm (List.range n) ∧ ∀ i ∈ List.range n, ∀ j ∈ List.range n,
      graphBit n b i j = graphBit n a (p[i]?.getD n) (p[j]?.getD n) := by
  simp only [graphIsoCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at h
  exact h
def graphDegree (n a i : Nat) : Nat :=
  ((List.range n).filter (fun j => graphBit n a i j)).length

def eligibleNeighbors (n a mask : Nat) : Bool :=
  let ns := (List.range n).filter (fun i => mask.testBit i)
  decide (1 ≤ ns.length ∧ ns.length ≤ 3) && ns.all (fun i => decide (graphDegree n a i < 3))

def extendGraph (n a mask : Nat) : Nat :=
  ((List.range (n+1)).flatMap (fun i => (List.range (n+1)).map (fun j =>
    if i = n then (if j = n then 0 else if mask.testBit j then 2^(i*(n+1)+j) else 0)
    else if j = n then (if mask.testBit i then 2^(i*(n+1)+j) else 0)
    else if graphBit n a i j then 2^(i*(n+1)+j) else 0))).sum

/-- Check every possible neighbor mask, with explicit witnesses for eligible masks. -/
def extensionClosed (n a : Nat) (targets : List Nat) (cs : List (Nat × Nat × List Nat)) : Bool :=
  (List.range (2^n)).all (fun mask => !eligibleNeighbors n a mask ||
    cs.any (fun c => mask == c.1 && decide (c.2.1 ∈ targets) &&
      graphIsoCheck (n+1) (extendGraph n a mask) c.2.1 c.2.2))

theorem extensionClosed_sound (n a : Nat) (targets : List Nat)
    (cs : List (Nat × Nat × List Nat)) (h : extensionClosed n a targets cs = true)
    (mask : Nat) (hm : mask ∈ List.range (2^n)) (he : eligibleNeighbors n a mask = true) :
    ∃ c ∈ cs, mask = c.1 ∧ c.2.1 ∈ targets ∧
      graphIsoCheck (n+1) (extendGraph n a mask) c.2.1 c.2.2 = true := by
  have h' := List.all_eq_true.mp h mask hm
  simp only [he, Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq] at h'
  obtain ⟨c, hc, ⟨hmask, ht⟩, hi⟩ := h'
  exact ⟨c, hc, hmask, ht, hi⟩
end Nut8
