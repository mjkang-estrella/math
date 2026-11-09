import ArithmeticBase
namespace EBC337062
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def tableAdjacent (x y : ℕ) : Prop :=
  (y + 32 - x) % 32 ∈ ([1,7,9,23,25,31] : List ℕ)
instance (x y : ℕ) : Decidable (tableAdjacent x y) :=
  inferInstanceAs (Decidable (_ ∈ (_ : List ℕ)))

/-- Exact BFS layer certificate, not a claim about graph paths yet. -/
def BFSLocalCertificate : Prop :=
  distance0 0 = 0 ∧ count0 0 = 1 ∧
  ∀ x : Fin 32, x.val ≠ 0 →
    (∃ p : Fin 32, tableAdjacent x.val p.val ∧ distance0 p.val + 1 = distance0 x.val) ∧
    (∀ p : Fin 32, tableAdjacent x.val p.val → distance0 x.val ≤ distance0 p.val + 1) ∧
    count0 x.val = ((List.range 32).map (fun p =>
      if tableAdjacent x.val p ∧ distance0 p + 1 = distance0 x.val
      then count0 p else 0)).sum

theorem bfs_local_certificate : BFSLocalCertificate := by unfold BFSLocalCertificate; decide

/-- General arithmetic layer recursion, defined through Nat.rec to avoid generated helpers. -/
def layerCounts (vertices : List ℕ) (adj : ℕ → ℕ → Bool)
    (distance : ℕ → ℕ) (source : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (fun x => if x = source then 1 else 0)
    (fun k prev x => if distance x = k + 1 then
      (vertices.map (fun p => if adj p x then prev p else 0)).sum else 0)

theorem layerCounts_zero (vs adj d s x) :
    layerCounts vs adj d s 0 x = if x = s then 1 else 0 := rfl

theorem layerCounts_succ (vs adj d s k x) :
    layerCounts vs adj d s (k+1) x = if d x = k+1 then
      (vs.map (fun p => if adj p x then layerCounts vs adj d s k p else 0)).sum else 0 := rfl
end EBC337062
