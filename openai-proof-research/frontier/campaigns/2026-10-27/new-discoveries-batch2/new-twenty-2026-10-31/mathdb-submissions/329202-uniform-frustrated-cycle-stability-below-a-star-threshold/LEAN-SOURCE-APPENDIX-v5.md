# Literal production Lean dependency closure v5

All local imports needed by AuditV5, in build order. Upstream standard Lean/mathlib plus eight libraries are read-only and pinned in PINS.json. No failed version is in this appendix.

<!-- LEAN-SOURCE-BEGIN Pilot SHA256 93c482babb1814f962ede7552c9d73fd2b1f28b3d1864ed9bc4ab1843e2c109d BYTES 10733 -->
```lean
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup

namespace Frustrated

structure Graph (V : Type) where
  edge : V → V → Bool
  symm : ∀ a b, edge a b = edge b a
  loopless : ∀ a, edge a a = false

def complement {V} [DecidableEq V] (G : Graph V) : Graph V where
  edge a b := if a = b then false else !(G.edge a b)
  symm a b := by
    by_cases h : a = b
    · subst b; simp
    · have h' : b ≠ a := Ne.symm h
      simp [h, h', G.symm]
  loopless a := by simp

def cut {V} (U : V → Bool) : Graph V where
  edge a b := xor (U a) (U b)
  symm a b := by cases U a <;> cases U b <;> rfl
  loopless a := by cases U a <;> rfl

def switch {V} (G : Graph V) (U : V → Bool) : Graph V where
  edge a b := xor (G.edge a b) ((cut U).edge a b)
  symm a b := by rw [G.symm, (cut U).symm]
  loopless a := by simp [G.loopless, (cut U).loopless]

/-- A single edit toggles one unordered pair, separately from switching. -/
def edit {V} [DecidableEq V] (G : Graph V) (u v : V) : Graph V where
  edge a b := xor (G.edge a b) (decide (u ≠ v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))))
  symm a b := by
    have h : (u ≠ v ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ↔
      (u ≠ v ∧ ((b = u ∧ a = v) ∨ (b = v ∧ a = u))) := by tauto
    simp only [h, G.symm a b]
  loopless a := by
    have h : ¬(u ≠ v ∧ ((a = u ∧ a = v) ∨ (a = v ∧ a = u))) := by
      rintro ⟨hne, hh⟩
      rcases hh with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> exact hne rfl
    simp [h, G.loopless]

def star (n s : Nat) : Graph (Fin n) where
  edge a b := decide ((a.val = 0 ∧ 1 ≤ b.val ∧ b.val ≤ s) ∨
    (b.val = 0 ∧ 1 ≤ a.val ∧ a.val ≤ s))
  symm a b := by simp only [or_comm]
  loopless a := by simp; omega

def editDistance (n : Nat) (G H : Graph (Fin n)) : Nat :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => p.1 < p.2 ∧ G.edge p.1 p.2 ≠ H.edge p.1 p.2)).card

def NearCut (n t : Nat) (G : Graph (Fin n)) : Prop :=
  ∃ U : Fin n → Bool, editDistance n G (cut U) ≤ t

/-- Rooted, oriented ambient cycles: injectivity excludes repeated vertices. -/
abbrev Ambient (n k : Nat) := Fin k ↪ Fin n

noncomputable def tupleCount (n k : Nat) (G : Graph (Fin n)) : Nat := by
  classical
  exact ((Finset.univ : Finset (Ambient n k)).filter (fun c =>
    ((Finset.univ.filter (fun i : Fin k => G.edge (c i)
      (c ⟨(i.val + 1) % k, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩))).card % 2 = 1))).card

def tupleOdd {n k} (G : Graph (Fin n)) (c : Ambient n k) : Prop :=
  ((Finset.univ.filter (fun i : Fin k => G.edge (c i)
    (c ⟨(i.val + 1) % k, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩))).card % 2 = 1)

/-- One rotation or reversed rotation. Quot takes the equivalence closure. -/
def dihedralStep {n k} (c d : Ambient n k) : Prop :=
  ∃ r : Fin k,
    (∀ i j : Fin k, j.val = (i.val + r.val) % k → d i = c j) ∨
    (∀ i j : Fin k, j.val = (r.val + k - i.val) % k → d i = c j)

/-- Unoriented frustrated ambient cycles, modulo rotation and reversal.
The uniform 2*k fiber theorem is NOT yet proved. -/
noncomputable def cycleCount (n k : Nat) (G : Graph (Fin n)) : Nat :=
  Nat.card (Quot (fun c d : {c : Ambient n k // tupleOdd G c} =>
    dihedralStep c.val d.val))

/-- Literal target interface, not a theorem. Empty cut parts are allowed. -/
def Conjecture19 : Prop :=
  ∀ k : Nat, 3 ≤ k → ∀ t : Nat, ∃ N : Nat, t + 2 ≤ N ∧
    ∀ n : Nat, N ≤ n → ∀ G : Graph (Fin n),
      cycleCount n k G < cycleCount n k (star n (t+1)) →
      NearCut n t G ∨ NearCut n t (complement G)

/-- Following a list of vertices; all pairs are ambient, not graph-walk edges. -/
def pathParity {V} (G : Graph V) : V → List V → Bool
  | _, [] => false
  | a, b :: l => xor (G.edge a b) (pathParity G b l)

def cycleParity {V} (G : Graph V) : List V → Bool
  | [] => false
  | a :: l => pathParity G a (l ++ [a])

structure ListCycle (V : Type) (k : Nat) where
  vertices : List V
  length_eq : vertices.length = k
  distinct : vertices.Nodup

/-- No claimed scaling bridge from this list representation to tupleCount. -/
def frustrated {V k} (G : Graph V) (C : ListCycle V k) : Prop :=
  cycleParity G C.vertices = true

/-- Exact witness hypotheses: a,b,c,d and the internal path vertices are distinct. -/
structure Witness (V : Type) where
  a : V
  b : V
  c : V
  d : V
  internal : List V
  distinct : (a :: internal ++ [c,b,d]).Nodup

def Witness.first {V} (w : Witness V) := w.a :: w.internal ++ [w.c,w.b]
def Witness.second {V} (w : Witness V) := w.a :: w.internal ++ [w.c,w.d]

theorem path_append {V} (G : Graph V) (a : V) (p : List V) (c : V) (q : List V) :
    pathParity G a (p ++ c :: q) =
      xor (pathParity G a (p ++ [c])) (pathParity G c q) := by
  induction p generalizing a with
  | nil => simp [pathParity]
  | cons b p ih =>
    simp only [List.cons_append, pathParity, ih]
    cases G.edge a b <;> cases pathParity G b (p ++ [c]) <;>
      cases pathParity G c q <;> rfl

/-- Common-path cancellation for the actual two cyclic orderings in proof step 1. -/
theorem witness_parity {V} (G : Graph V) (w : Witness V) :
    xor (cycleParity G w.first) (cycleParity G w.second) =
      cycleParity G [w.a,w.b,w.c,w.d] := by
  simp only [Witness.first, Witness.second, cycleParity, List.append_assoc,
    List.cons_append, List.nil_append]
  rw [path_append G w.a w.internal w.c [w.b,w.a],
    path_append G w.a w.internal w.c [w.d,w.a]]
  simp only [pathParity]
  rw [G.symm w.c w.b, G.symm w.b w.a]
  cases pathParity G w.a (w.internal ++ [w.c]) <;>
    cases G.edge w.a w.b <;> cases G.edge w.b w.c <;>
    cases G.edge w.c w.d <;> cases G.edge w.d w.a <;> rfl

/-- The fiber over a fixed rooted/oriented first cycle injects into the remaining vertex. -/
theorem witness_first_fiber {V} (w z : Witness V)
    (h : w.first = z.first) (hd : w.d = z.d)
    (hlen : w.internal.length = z.internal.length) : w = z := by
  cases w with | mk a b c d p hp =>
    cases z with | mk a' b' c' d' p' hp' =>
      have ha : a = a' := (List.cons.inj h).1
      have hh : p ++ [c,b] = p' ++ [c',b'] := (List.cons.inj h).2
      subst a'
      have hs := List.append_inj hh hlen
      obtain ⟨he, ht⟩ := hs
      subst p'
      simp only [List.cons.injEq, and_true] at ht
      obtain ⟨hc,hb⟩ := ht
      subst c'; subst b'
      change d = d' at hd
      subst d'
      rfl

theorem first_nodup {V} (w : Witness V) : w.first.Nodup := by
  have h : (w.first ++ [w.d]).Nodup := by
    simpa [Witness.first, List.append_assoc] using w.distinct
  exact (List.nodup_append.mp h).1

theorem second_nodup {V} (w : Witness V) : w.second.Nodup := by
  have h := w.distinct
  simp only [List.nodup_cons, List.nodup_append, List.mem_cons] at h
  simp only [Witness.second, List.nodup_cons, List.nodup_append,
    List.mem_cons]
  simp_all

theorem exactly_one {V} (G : Graph V) (w : Witness V)
    (hq : cycleParity G [w.a,w.b,w.c,w.d] = true) :
    cycleParity G w.first ≠ cycleParity G w.second := by
  have h := witness_parity G w
  rw [hq] at h
  cases h1 : cycleParity G w.first <;>
    cases h2 : cycleParity G w.second <;> simp_all

theorem witness_first_recover {V} (w z : Witness V)
    (h : w.first = z.first) (hd : w.d = z.d) : w = z := by
  have hh := congrArg List.length h
  simp only [Witness.first, List.length_cons, List.length_append,
    List.length_nil] at hh
  apply witness_first_fiber w z h hd
  omega

/-- The rooted, oriented first-slot fiber has at most n witnesses, not 2*k*n.
The 2*k orientation/root bridge remains separate. -/
theorem first_fiber_card (n : Nat) (L : List (Fin n)) :
    Nat.card {w : Witness (Fin n) // w.first = L} ≤ n := by
  have inj : Function.Injective
      (fun w : {w : Witness (Fin n) // w.first = L} => w.val.d) := by
    intro w z h
    apply Subtype.ext
    exact witness_first_recover w.val z.val (w.property.trans z.property.symm) h
  simpa using Nat.card_le_card_of_injective _ inj

def Witness.firstCycle {V} (w : Witness V) : ListCycle V (w.internal.length + 3) where
  vertices := w.first
  length_eq := by simp [Witness.first]
  distinct := first_nodup w

def Witness.secondCycle {V} (w : Witness V) : ListCycle V (w.internal.length + 3) where
  vertices := w.second
  length_eq := by simp [Witness.second]
  distinct := second_nodup w

theorem witness_second_recover {V} (w z : Witness V)
    (h : w.second = z.second) (hb : w.b = z.b) : w = z := by
  cases w with | mk a b c d p hp =>
    cases z with | mk a' b' c' d' p' hp' =>
      have ha : a = a' := (List.cons.inj h).1
      have hh : p ++ [c,d] = p' ++ [c',d'] := (List.cons.inj h).2
      have hl := congrArg List.length hh
      simp only [List.length_append, List.length_cons, List.length_nil] at hl
      have hpLen : p.length = p'.length := by omega
      obtain ⟨he, ht⟩ := List.append_inj hh hpLen
      have hc : c = c' := (List.cons.inj ht).1
      have hd : d = d' := (List.cons.inj (List.cons.inj ht).2).1
      change b = b' at hb
      subst a'; subst b'; subst c'; subst d'; subst p'
      rfl

theorem second_fiber_card (n : Nat) (L : List (Fin n)) :
    Nat.card {w : Witness (Fin n) // w.second = L} ≤ n := by
  have inj : Function.Injective
      (fun w : {w : Witness (Fin n) // w.second = L} => w.val.b) := by
    intro w z h
    apply Subtype.ext
    exact witness_second_recover w.val z.val (w.property.trans z.property.symm) h
  simpa using Nat.card_le_card_of_injective _ inj

theorem path_switch {V} (G : Graph V) (U : V → Bool)
    (a b : V) (p : List V) :
    pathParity (switch G U) a (p ++ [b]) =
      xor (pathParity G a (p ++ [b])) (xor (U a) (U b)) := by
  induction p generalizing a with
  | nil => simp [pathParity, switch, cut]
  | cons c p ih =>
    simp only [List.cons_append, pathParity]
    rw [ih c]
    simp only [switch, cut]
    cases G.edge a c <;> cases U a <;> cases U c <;> cases U b <;>
      cases pathParity G c (p ++ [b]) <;> rfl

theorem cycle_switch {V} (G : Graph V) (U : V → Bool) (l : List V) :
    cycleParity (switch G U) l = cycleParity G l := by
  cases l with
  | nil => rfl
  | cons a p => simp [cycleParity, path_switch]

#eval Lean.versionString
#print axioms Witness.firstCycle
#print axioms Witness.secondCycle
#print axioms witness_second_recover
#print axioms second_fiber_card
#print axioms witness_first_recover
#print axioms first_fiber_card
#print axioms path_switch
#print axioms cycle_switch
#print axioms Conjecture19
#print axioms first_nodup
#print axioms second_nodup
#print axioms exactly_one
#print axioms witness_parity
#print axioms witness_first_fiber
end Frustrated
```
<!-- LEAN-SOURCE-END Pilot -->

<!-- LEAN-SOURCE-BEGIN Bridge SHA256 87248766cdc9fb8615381eca5a9adb44927a7d4fae4489ec81aef5a5cd8525e1 BYTES 3890 -->
```lean
import Pilot
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Rotate
namespace Frustrated

def ListCycle.toTuple {n k} (C : ListCycle (Fin n) k) : Ambient n k where
  toFun i := C.vertices.get (Fin.cast C.length_eq.symm i)
  inj' := by
    intro i j h
    have hh := (List.nodup_iff_injective_get.mp C.distinct) h
    apply Fin.ext
    simpa using congrArg (fun x : Fin C.vertices.length => x.val) hh

def tupleToList {n k} (c : Ambient n k) : ListCycle (Fin n) k where
  vertices := List.ofFn c
  length_eq := List.length_ofFn
  distinct := List.nodup_ofFn_ofInjective c.injective

theorem ListCycle.toTuple_toList {n k} (C : ListCycle (Fin n) k) :
    tupleToList C.toTuple = C := by
  cases C with | mk l h hd =>
    subst k
    simp [tupleToList, ListCycle.toTuple]

theorem tupleToList_toTuple {n k} (c : Ambient n k) :
    (tupleToList c).toTuple = c := by
  apply Function.Embedding.ext
  intro i
  change (List.ofFn c)[i.val]'(by simp) = c i
  simp only [List.getElem_ofFn]


def listTupleEquiv (n k : Nat) : ListCycle (Fin n) k ≃ Ambient n k where
  toFun := ListCycle.toTuple
  invFun := tupleToList
  left_inv := ListCycle.toTuple_toList
  right_inv := tupleToList_toTuple

theorem cycle_blocks {V} (G : Graph V) (a b : V) (p q : List V) :
    cycleParity G ((a :: p) ++ (b :: q)) =
      xor (pathParity G a (p ++ [b])) (pathParity G b (q ++ [a])) := by
  simp only [List.cons_append, cycleParity, List.append_assoc]
  exact path_append G a p b (q ++ [a])

theorem cycle_blocks_rotate {V} (G : Graph V) (a b : V) (p q : List V) :
    cycleParity G ((a :: p) ++ (b :: q)) =
      cycleParity G ((b :: q) ++ (a :: p)) := by
  rw [cycle_blocks, cycle_blocks]
  cases pathParity G a (p ++ [b]) <;> cases pathParity G b (q ++ [a]) <;> rfl

theorem path_reverse {V} (G : Graph V) (a b : V) (p : List V) :
    pathParity G a (p ++ [b]) = pathParity G b (p.reverse ++ [a]) := by
  induction p generalizing a b with
  | nil => simp [pathParity, G.symm]
  | cons c p ih =>
    simp only [List.cons_append, pathParity, List.reverse_cons, List.append_assoc, List.nil_append]
    rw [path_append G b p.reverse c [a], ← ih c b]
    simp only [pathParity]
    rw [G.symm c a]
    cases G.edge a c <;> cases pathParity G c (p ++ [b]) <;> rfl

theorem cycle_rotate_cons {V} (G : Graph V) (a : V) (p : List V) :
    cycleParity G (p ++ [a]) = cycleParity G (a :: p) := by
  cases p with
  | nil => rfl
  | cons b q => simpa using cycle_blocks_rotate G b a q []

theorem cycle_reverse {V} (G : Graph V) (l : List V) :
    cycleParity G l.reverse = cycleParity G l := by
  cases l with
  | nil => rfl
  | cons a p =>
    rw [List.reverse_cons, cycle_rotate_cons]
    exact (path_reverse G a a p).symm

theorem cycle_rotate {V} (G : Graph V) (l : List V) (r : Nat) :
    cycleParity G (l.rotate r) = cycleParity G l := by
  induction r generalizing l with
  | zero => simp
  | succ r ih =>
    cases l with
    | nil => simp
    | cons a p =>
      rw [List.rotate_cons_succ, ih, cycle_rotate_cons]

@[simp] theorem ListCycle.toTuple_get {n k} (C : ListCycle (Fin n) k) (i : Fin k) :
    C.toTuple i = C.vertices[i.val]'(by rw [C.length_eq]; exact i.isLt) := rfl

/-- The indexed edge uses precisely the successor of the original list, including wrap. -/
theorem ListCycle.successor_edge {n k} (G : Graph (Fin n))
    (C : ListCycle (Fin n) k) (i : Fin k) :
    G.edge (C.toTuple i)
      (C.toTuple ⟨(i.val + 1) % k, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩) =
    G.edge (C.vertices.get (Fin.cast C.length_eq.symm i))
      (C.vertices.get (Fin.cast C.length_eq.symm
        ⟨(i.val + 1) % k, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)) := rfl

#print axioms listTupleEquiv
#print axioms cycle_blocks_rotate
#print axioms path_reverse
#print axioms cycle_reverse
#print axioms cycle_rotate_cons
#print axioms cycle_rotate
#print axioms ListCycle.successor_edge
end Frustrated
```
<!-- LEAN-SOURCE-END Bridge -->

<!-- LEAN-SOURCE-BEGIN Parity SHA256 d9d2b30855a6f5f123b12a1637b8d9ac6379dacdf11681f6b95ce5e029c07a29 BYTES 2587 -->
```lean
import Bridge
namespace Frustrated

def bitParity : List Bool → Bool
  | [] => false
  | b :: l => xor b (bitParity l)

theorem bitParity_count (l : List Bool) :
    bitParity l = true ↔ l.count true % 2 = 1 := by
  induction l with
  | nil => simp [bitParity]
  | cons b l ih =>
    cases b <;> cases h : bitParity l <;>
      simp_all [bitParity] <;> omega

def pathBits {V} (G : Graph V) : V → List V → List Bool
  | _, [] => []
  | a, b :: l => G.edge a b :: pathBits G b l

theorem pathBits_parity {V} (G : Graph V) (a : V) (l : List V) :
    bitParity (pathBits G a l) = pathParity G a l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp [pathBits, bitParity, pathParity, ih]

theorem pathBits_zip {V} (G : Graph V) (a b : V) (p : List V) :
    pathBits G a (p ++ [b]) = List.zipWith G.edge (a :: p) (p ++ [b]) := by
  induction p generalizing a with
  | nil => rfl
  | cons c p ih => simp [pathBits, ih]

def cycleBits {V} (G : Graph V) (l : List V) : List Bool :=
  List.zipWith G.edge l (l.rotate 1)

theorem cycleBits_parity {V} (G : Graph V) (l : List V) :
    bitParity (cycleBits G l) = cycleParity G l := by
  cases l with
  | nil => rfl
  | cons a p =>
    simp only [cycleBits, List.rotate_cons_succ, List.rotate_zero]
    rw [← pathBits_zip, pathBits_parity]
    rfl

theorem cycleBits_ofFn {n k} (G : Graph (Fin n)) (c : Ambient n k) :
    cycleBits G (List.ofFn c) = List.ofFn (fun i : Fin k =>
      G.edge (c i) (c ⟨(i.val + 1) % k,
        Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩)) := by
  apply List.ext_getElem
  · simp [cycleBits]
  · intro i h1 h2
    simp only [cycleBits, List.getElem_zipWith, List.getElem_ofFn,
      List.getElem_rotate]
    congr 1
    congr 1
    apply Fin.ext
    simp

/-- A filtered Finset count is the true-bit count of its indexed list. -/
theorem ofFn_count {k} (p : Fin k → Bool) :
    (List.ofFn p).count true =
      ((Finset.univ : Finset (Fin k)).filter (fun i => p i)).card := by
  have h := (List.nodup_finRange k).card_eq_countP (P := fun i => p i = true)
  rw [List.toFinset_finRange] at h
  rw [List.ofFn_eq_map]
  simpa [List.count, List.countP_map, Function.comp_def] using h.symm

theorem tupleOdd_list {n k} (G : Graph (Fin n)) (c : Ambient n k) :
    tupleOdd G c ↔ cycleParity G (tupleToList c).vertices = true := by
  rw [← cycleBits_parity]
  change _ ↔ bitParity (cycleBits G (List.ofFn c)) = true
  rw [cycleBits_ofFn, bitParity_count, ofFn_count]
  rfl


#print axioms bitParity_count
#print axioms cycleBits_ofFn
#print axioms tupleOdd_list
end Frustrated
```
<!-- LEAN-SOURCE-END Parity -->

<!-- LEAN-SOURCE-BEGIN Orbit SHA256 3cdd3865ee06c492e64c1a6d52f8a3a78090f319f20ac2e22ff9dbdb5f7c08e1 BYTES 5471 -->
```lean
import Parity
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.Abel
namespace Frustrated

def rot {n k} [NeZero k] (c : Ambient n k) (r : Fin k) : Ambient n k where
  toFun i := c (i + r)
  inj' := fun _ _ h => add_right_cancel (c.injective h)

def refl {n k} [NeZero k] (c : Ambient n k) (r : Fin k) : Ambient n k where
  toFun i := c (r - i)
  inj' := fun _ _ h => sub_right_injective (c.injective h)

theorem dihedralStep_iff {n k} [NeZero k] (c d : Ambient n k) :
    dihedralStep c d ↔ ∃ r : Fin k, d = rot c r ∨ d = refl c r := by
  constructor
  · rintro ⟨r, h | h⟩
    · exact ⟨r, Or.inl (Function.Embedding.ext (fun i => h i (i+r) rfl))⟩
    · exact ⟨r, Or.inr (Function.Embedding.ext (fun i => h i (r-i) (by rw [Fin.val_sub]; congr 1; omega)))⟩
  · rintro ⟨r, rfl | rfl⟩
    · refine ⟨r, Or.inl ?_⟩
      intro i j h
      change c (i+r) = c j
      congr 1
      apply Fin.ext
      exact h.symm
    · refine ⟨r, Or.inr ?_⟩
      intro i j h
      change c (r-i) = c j
      congr 1
      apply Fin.ext
      rw [Fin.val_sub]
      convert h.symm using 2
      omega

theorem rot_zero {n k} [NeZero k] (c : Ambient n k) : rot c 0 = c := by
  ext i; simp [rot]

theorem rot_rot {n k} [NeZero k] (c : Ambient n k) (r s : Fin k) :
    rot (rot c r) s = rot c (s+r) := by
  apply Function.Embedding.ext
  intro i
  change c ((i+s)+r) = c (i+(s+r))
  rw [add_assoc]

theorem refl_refl {n k} [NeZero k] (c : Ambient n k) (r s : Fin k) :
    refl (refl c r) s = rot c (r-s) := by
  apply Function.Embedding.ext
  intro i
  change c (r - (s - i)) = c (i + (r-s))
  congr 1
  abel

theorem rot_refl {n k} [NeZero k] (c : Ambient n k) (r s : Fin k) :
    refl (rot c r) s = refl c (s+r) := by
  apply Function.Embedding.ext
  intro i
  change c ((s-i)+r) = c ((s+r)-i)
  congr 1
  abel

theorem refl_rot {n k} [NeZero k] (c : Ambient n k) (r s : Fin k) :
    rot (refl c r) s = refl c (r-s) := by
  apply Function.Embedding.ext
  intro i
  change c (r-(i+s)) = c ((r-s)-i)
  congr 1
  abel

theorem step_refl {n k} [NeZero k] (c : Ambient n k) : dihedralStep c c := by
  rw [dihedralStep_iff]
  exact ⟨0, Or.inl (rot_zero c).symm⟩

theorem step_symm {n k} [NeZero k] {c d : Ambient n k}
    (h : dihedralStep c d) : dihedralStep d c := by
  rw [dihedralStep_iff] at h ⊢
  obtain ⟨r, rfl | rfl⟩ := h
  · refine ⟨-r, Or.inl ?_⟩
    rw [rot_rot, neg_add_cancel, rot_zero]
  · refine ⟨r, Or.inr ?_⟩
    rw [refl_refl, sub_self, rot_zero]

theorem step_trans {n k} [NeZero k] {c d e : Ambient n k}
    (h : dihedralStep c d) (h' : dihedralStep d e) : dihedralStep c e := by
  rw [dihedralStep_iff] at h h' ⊢
  obtain ⟨r, rfl | rfl⟩ := h
  · obtain ⟨s, rfl | rfl⟩ := h'
    · exact ⟨s+r, Or.inl (rot_rot c r s)⟩
    · exact ⟨s+r, Or.inr (rot_refl c r s)⟩
  · obtain ⟨s, rfl | rfl⟩ := h'
    · exact ⟨r-s, Or.inr (refl_rot c r s)⟩
    · exact ⟨r-s, Or.inl (refl_refl c r s)⟩

theorem rot_parameter_injective {n k} [NeZero k] (c : Ambient n k) :
    Function.Injective (rot c) := by
  intro r s h
  have hh := congrArg (fun d : Ambient n k => d 0) h
  change c (0+r) = c (0+s) at hh
  simpa using c.injective hh

theorem refl_parameter_injective {n k} [NeZero k] (c : Ambient n k) :
    Function.Injective (refl c) := by
  intro r s h
  have hh := congrArg (fun d : Ambient n k => d 0) h
  change c (r-0) = c (s-0) at hh
  simpa using c.injective hh

theorem rot_ne_refl {n k} [NeZero k] (hk : 3 ≤ k) (c : Ambient n k)
    (r s : Fin k) : rot c r ≠ refl c s := by
  intro h
  have h0 := congrArg (fun d : Ambient n k => d 0) h
  change c (0+r) = c (s-0) at h0
  have hrs : r = s := by simpa using c.injective h0
  subst s
  have hh := congrArg (fun d : Ambient n k => d 1) h
  change c (1+r) = c (r-1) at hh
  have h1 := c.injective hh
  have htwo : (1 : Fin k) + 1 = 0 := by
    calc
      (1 : Fin k) + 1 = ((1+r)-r)+1 := by abel
      _ = ((r-1)-r)+1 := by rw [h1]
      _ = 0 := by abel
  have hv := congrArg Fin.val htwo
  norm_num [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (show 2 < k by omega)] at hv

def orbitMap {n k} [NeZero k] (c : Ambient n k) (p : Bool × Fin k) :
    {d : Ambient n k // dihedralStep c d} :=
  if p.1 then ⟨refl c p.2, (dihedralStep_iff _ _).mpr ⟨p.2, Or.inr rfl⟩⟩
  else ⟨rot c p.2, (dihedralStep_iff _ _).mpr ⟨p.2, Or.inl rfl⟩⟩

theorem orbitMap_bijective {n k} [NeZero k] (hk : 3 ≤ k) (c : Ambient n k) :
    Function.Bijective (orbitMap c) := by
  constructor
  · rintro ⟨b,r⟩ ⟨d,s⟩ h
    have hv := congrArg Subtype.val h
    cases b <;> cases d
    · have hh : r = s := rot_parameter_injective c hv
      subst s; rfl
    · exact False.elim (rot_ne_refl hk c r s hv)
    · exact False.elim (rot_ne_refl hk c s r hv.symm)
    · have hh : r = s := refl_parameter_injective c hv
      subst s; rfl
  · rintro ⟨d,hd⟩
    obtain ⟨r, hr | hr⟩ := (dihedralStep_iff c d).mp hd
    · refine ⟨(false,r), ?_⟩
      apply Subtype.ext
      exact hr.symm
    · refine ⟨(true,r), ?_⟩
      apply Subtype.ext
      exact hr.symm

theorem ambient_orbit_card {n k} [NeZero k] (hk : 3 ≤ k) (c : Ambient n k) :
    Nat.card {d : Ambient n k // dihedralStep c d} = 2*k := by
  rw [← Nat.card_congr (Equiv.ofBijective (orbitMap c) (orbitMap_bijective hk c))]
  simp

#print axioms ambient_orbit_card
#print axioms dihedralStep_iff
#print axioms step_trans
#print axioms rot_ne_refl
end Frustrated
```
<!-- LEAN-SOURCE-END Orbit -->

<!-- LEAN-SOURCE-BEGIN AdjacentNormalize SHA256 4d81757523f3a76dc30231c1c9fda7ca783137b27226982e009235d0ca587b34 BYTES 2990 -->
```lean
import Orbit
import Mathlib.Data.Sym.Sym2
namespace Frustrated
/-- An actual unordered consecutive edge of the ambient cycle tuple. -/
def HasCyclePair {n k} [NeZero k] (c : Ambient n k) (a b : Fin n) : Prop :=
  ∃ i : Fin k, s(c i,c (i+1)) = s(a,b)

theorem pair_positions {n k} [NeZero k] (c : Ambient n k) (a b : Fin n)
    (h : HasCyclePair c a b) :
    ∃ x y : Fin k, c x = a ∧ c y = b ∧ (y=x+1 ∨ x=y+1) := by
  obtain ⟨i,hi⟩ := h
  rcases Sym2.eq_iff.mp hi with h | h
  · exact ⟨i,i+1,h.1,h.2,Or.inl rfl⟩
  · exact ⟨i+1,i,h.2,h.1,Or.inr rfl⟩

/-- Two incident edges force a consecutive path; distinct endpoints rule out
    the two backtracking possibilities, including at k=3. -/
theorem adjacent_positions {n k} [NeZero k] (hk : 3 ≤ k) (c : Ambient n k)
    (a b d : Fin n) (had : a ≠ d)
    (h₁ : HasCyclePair c a b) (h₂ : HasCyclePair c b d) :
    ∃ x : Fin k, c x = a ∧
      ((c (x+1) = b ∧ c (x+2) = d) ∨
       (c (x-1) = b ∧ c (x-2) = d)) := by
  have ht : (2 : Fin k) = 1+1 := by
    apply Fin.ext
    norm_num [Fin.val_add, Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : 1<k),
      Nat.mod_eq_of_lt (by omega : 2<k)]
  obtain ⟨x,y,hx,hy,hxy⟩ := pair_positions c a b h₁
  obtain ⟨y',z,hy',hz,hyz⟩ := pair_positions c b d h₂
  have he : y'=y := c.injective (hy'.trans hy.symm)
  subst y'
  have hxz : x ≠ z := fun h => had (hx.symm.trans ((congrArg c h).trans hz))
  refine ⟨x,hx,?_⟩
  rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
  · left
    constructor
    · simpa only [hxy] using hy
    · have he : z=x+2 := by rw [hyz,hxy,ht]; abel
      simpa only [he] using hz
  · exact False.elim (hxz (add_right_cancel (hxy.symm.trans hyz)))
  · exact False.elim (hxz (hxy.trans hyz.symm))
  · right
    have he : y=x-1 := by rw [hxy]; abel
    have he' : z=x-2 := by rw [hxy,hyz,ht]; abel
    exact ⟨he ▸ hy,he' ▸ hz⟩

/-- Existence of an orbit representative with the specified ordered path. -/
theorem adjacent_normalize {n k} [NeZero k] (hk : 3 ≤ k)
    (c : Ambient n k) (q : Ambient n 3)
    (h₁ : HasCyclePair c (q 0) (q 1))
    (h₂ : HasCyclePair c (q 1) (q 2)) :
    ∃ d : Ambient n k, dihedralStep c d ∧
      d 0=q 0 ∧ d 1=q 1 ∧ d 2=q 2 := by
  have h02 : q 0 ≠ q 2 := by intro h; have := q.injective h; have := congrArg Fin.val this; norm_num at this
  obtain ⟨x,hx,ho⟩ := adjacent_positions hk c (q 0) (q 1) (q 2) h02 h₁ h₂
  rcases ho with ho | ho
  · refine ⟨rot c x,(dihedralStep_iff _ _).mpr ⟨x,Or.inl rfl⟩,?_,?_,?_⟩
    · change c (0+x) = q 0
      simpa using hx
    · change c (1+x) = q 1
      simpa only [add_comm] using ho.1
    · change c (2+x) = q 2
      simpa only [add_comm] using ho.2
  · refine ⟨refl c x,(dihedralStep_iff _ _).mpr ⟨x,Or.inr rfl⟩,?_,?_,?_⟩
    · change c (x-0) = q 0
      simpa using hx
    · exact ho.1
    · exact ho.2
#print axioms adjacent_positions
#print axioms adjacent_normalize
end Frustrated
```
<!-- LEAN-SOURCE-END AdjacentNormalize -->

<!-- LEAN-SOURCE-BEGIN AdjacentBijection SHA256 9b0d47e7f67c1d27da57307997995807cfe2cd51aa3b3f418a4d08a053381a49 BYTES 4514 -->
```lean
import AdjacentNormalize
namespace Frustrated
/-- Fixing two consecutive distinct vertices resolves the whole dihedral orbit. -/
theorem two_point_orbit_unique {n k : Nat} [NeZero k] (hk : 3 ≤ k) (c d : Ambient n k)
    (h0 : d 0 = c 0) (h1 : d 1 = c 1) (h : dihedralStep c d) : c = d := by
  obtain ⟨r,hr | hr⟩ := (dihedralStep_iff c d).mp h
  · have hh := congrArg (fun x : Ambient n k => x 0) hr
    change d 0 = c (0+r) at hh
    rw [zero_add,h0] at hh
    have hz : r=0 := (c.injective hh).symm
    simpa only [hz,rot_zero] using hr.symm
  · have hh := congrArg (fun x : Ambient n k => x 0) hr
    change d 0 = c (r-0) at hh
    rw [sub_zero,h0] at hh
    have hz : r=0 := (c.injective hh).symm
    have hh1 := congrArg (fun x : Ambient n k => x 1) hr
    change d 1 = c (r-1) at hh1
    rw [hz,h1] at hh1
    have he := c.injective hh1
    have hv := congrArg Fin.val he
    rw [Fin.val_sub] at hv
    change 1%k = (k-1%k+0)%k at hv
    have hmod : 1%k=1 := Nat.mod_eq_of_lt (by omega)
    rw [hmod,Nat.add_zero,Nat.mod_eq_of_lt (by omega : k-1<k)] at hv
    omega


theorem pair_rot {n k : Nat} [NeZero k] (c : Ambient n k) (r : Fin k)
    (a b : Fin n) (h : HasCyclePair c a b) : HasCyclePair (rot c r) a b := by
  obtain ⟨i,hi⟩ := h
  refine ⟨i-r,?_⟩
  change s(c (i-r+r),c (i-r+1+r))=s(a,b)
  have he : i-r+1+r=i+1 := by abel
  simpa only [sub_add_cancel,he] using hi

theorem pair_refl {n k : Nat} [NeZero k] (c : Ambient n k) (r : Fin k)
    (a b : Fin n) (h : HasCyclePair c a b) : HasCyclePair (refl c r) a b := by
  obtain ⟨i,hi⟩ := h
  refine ⟨r-i-1,?_⟩
  change s(c (r-(r-i-1)),c (r-(r-i-1+1)))=s(a,b)
  have he : r-(r-i-1)=i+1 := by abel
  have he' : r-(r-i-1+1)=i := by abel
  rw [he,he',Sym2.eq_swap]
  exact hi

theorem pair_step {n k : Nat} [NeZero k] (c d : Ambient n k)
    (h : dihedralStep c d) (a b : Fin n) (hp : HasCyclePair c a b) :
    HasCyclePair d a b := by
  obtain ⟨r,hr | hr⟩ := (dihedralStep_iff _ _).mp h
  · rw [hr]; exact pair_rot c r a b hp
  · rw [hr]; exact pair_refl c r a b hp

abbrev PathPrefix {n k : Nat} [NeZero k] (q : Ambient n 3) :=
  {c : Ambient n k // c 0=q 0 ∧ c 1=q 1 ∧ c 2=q 2}
abbrev AdjacentTuples {n k : Nat} [NeZero k] (q : Ambient n 3) :=
  {c : Ambient n k // HasCyclePair c (q 0) (q 1) ∧ HasCyclePair c (q 1) (q 2)}

theorem prefix_pairs {n k : Nat} [NeZero k] (hk : 3 ≤ k) (q : Ambient n 3)
    (d : PathPrefix (k:=k) q) :
    HasCyclePair d.val (q 0) (q 1) ∧ HasCyclePair d.val (q 1) (q 2) := by
  have ht : (1 : Fin k)+1=2 := by
    apply Fin.ext
    norm_num [Fin.val_add,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 1<k),
      Nat.mod_eq_of_lt (by omega : 2<k)]
  constructor
  · refine ⟨0,?_⟩
    simp only [zero_add,d.property.1,d.property.2.1]
  · refine ⟨1,?_⟩
    rw [ht,d.property.2.1,d.property.2.2]

noncomputable def adjacentPlacement {n k : Nat} [NeZero k] (hk : 3 ≤ k)
    (q : Ambient n 3) (p : (Bool × Fin k) × PathPrefix (k:=k) q) :
    AdjacentTuples (k:=k) q := by
  let e := orbitMap p.2.val p.1
  have h := prefix_pairs hk q p.2
  exact ⟨e.val, pair_step _ _ e.property _ _ h.1,
    pair_step _ _ e.property _ _ h.2⟩

theorem adjacentPlacement_bijective {n k : Nat} [NeZero k] (hk : 3 ≤ k)
    (q : Ambient n 3) : Function.Bijective (adjacentPlacement hk q) := by
  constructor
  · rintro ⟨p,c⟩ ⟨r,d⟩ h
    have he : (orbitMap c.val p).val=(orbitMap d.val r).val := congrArg Subtype.val h
    have hc : dihedralStep c.val d.val :=
      step_trans (orbitMap c.val p).property
        (he ▸ step_symm (orbitMap d.val r).property)
    have hcd : c=d := Subtype.ext (two_point_orbit_unique hk c.val d.val
      (d.property.1.trans c.property.1.symm)
      (d.property.2.1.trans c.property.2.1.symm) hc)
    subst d
    have hpr : p=r := (orbitMap_bijective hk c.val).1 (Subtype.ext he)
    subst r
    rfl
  · intro c
    obtain ⟨d,hd,h₀,h₁,h₂⟩ := adjacent_normalize hk c.val q c.property.1 c.property.2
    let e : PathPrefix (k:=k) q := ⟨d,h₀,h₁,h₂⟩
    obtain ⟨p,hp⟩ := (orbitMap_bijective hk d).2 ⟨c.val,step_symm hd⟩
    refine ⟨(p,e),?_⟩
    apply Subtype.ext
    change (orbitMap d p).val=c.val
    exact congrArg Subtype.val hp

noncomputable def adjacentPlacementEquiv {n k : Nat} [NeZero k] (hk : 3 ≤ k)
    (q : Ambient n 3) :
    ((Bool × Fin k) × PathPrefix (k:=k) q) ≃ AdjacentTuples (k:=k) q :=
  Equiv.ofBijective _ (adjacentPlacement_bijective hk q)
#print axioms adjacentPlacementEquiv
end Frustrated
```
<!-- LEAN-SOURCE-END AdjacentBijection -->

<!-- LEAN-SOURCE-BEGIN Invariant SHA256 219339c192f95bf70be53bb2ad2e1ea076aceadfdc270a43735ae3b0d45f3957 BYTES 2634 -->
```lean
import Orbit
namespace Frustrated

theorem succ_as_add {k} [NeZero k] (i : Fin k) :
    (⟨(i.val + 1) % k, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ : Fin k) = i+1 := by
  apply Fin.ext
  simp [Fin.val_add, Nat.add_mod]

def edgeBool {n k} [NeZero k] (G : Graph (Fin n)) (c : Ambient n k) (i : Fin k) :=
  G.edge (c i) (c (i+1))

theorem tupleOdd_count {n k} [NeZero k] (G : Graph (Fin n)) (c : Ambient n k) :
    tupleOdd G c ↔ (List.ofFn (edgeBool G c)).count true % 2 = 1 := by
  rw [ofFn_count]
  simp only [tupleOdd, edgeBool, succ_as_add]
  rfl

theorem ofFn_perm {k} (e : Equiv.Perm (Fin k)) (f : Fin k → Bool) :
    List.Perm (List.ofFn (fun i => f (e i))) (List.ofFn f) := by
  simpa [List.ofFn_eq_map, List.map_map, Function.comp_def] using
    (Equiv.Perm.map_finRange_perm e).map f

theorem tupleOdd_rot {n k} [NeZero k] (G : Graph (Fin n)) (c : Ambient n k) (r : Fin k) :
    tupleOdd G (rot c r) ↔ tupleOdd G c := by
  rw [tupleOdd_count, tupleOdd_count]
  have hp : edgeBool G (rot c r) = fun i => edgeBool G c (i+r) := by
    funext i
    change G.edge (c (i+r)) (c ((i+1)+r)) = G.edge (c (i+r)) (c ((i+r)+1))
    congr 2
    abel
  let e : Equiv.Perm (Fin k) :=
    { toFun := fun i => i+r
      invFun := fun i => i-r
      left_inv := by intro i; simp
      right_inv := by intro i; simp }
  have hc := (ofFn_perm e (edgeBool G c)).count_eq true
  change (List.ofFn (fun i => edgeBool G c (i+r))).count true = _ at hc
  rw [hp, hc]

theorem tupleOdd_refl {n k} [NeZero k] (G : Graph (Fin n)) (c : Ambient n k) (r : Fin k) :
    tupleOdd G (refl c r) ↔ tupleOdd G c := by
  rw [tupleOdd_count, tupleOdd_count]
  have hp : edgeBool G (refl c r) = fun i => edgeBool G c (r-i-1) := by
    funext i
    change G.edge (c (r-i)) (c (r-(i+1))) =
      G.edge (c (r-i-1)) (c ((r-i-1)+1))
    rw [G.symm]
    congr 2 <;> abel
  let e : Equiv.Perm (Fin k) :=
    { toFun := fun i => r-i-1
      invFun := fun i => r-i-1
      left_inv := by intro i; simp only [sub_eq_add_neg, neg_add_rev, neg_neg]; abel
      right_inv := by intro i; simp only [sub_eq_add_neg, neg_add_rev, neg_neg]; abel }
  have hc := (ofFn_perm e (edgeBool G c)).count_eq true
  change (List.ofFn (fun i => edgeBool G c (r-i-1))).count true = _ at hc
  rw [hp, hc]

theorem tupleOdd_step {n k} [NeZero k] (G : Graph (Fin n))
    {c d : Ambient n k} (h : dihedralStep c d) : tupleOdd G c ↔ tupleOdd G d := by
  obtain ⟨r, rfl | rfl⟩ := (dihedralStep_iff _ _).mp h
  · exact (tupleOdd_rot G c r).symm
  · exact (tupleOdd_refl G c r).symm

#print axioms tupleOdd_rot
#print axioms tupleOdd_refl
#print axioms tupleOdd_step
end Frustrated
```
<!-- LEAN-SOURCE-END Invariant -->

<!-- LEAN-SOURCE-BEGIN Counting SHA256 6dd1c1a4e6c92e4daa4e52dc845075d2dee407611fb47d5beed0469fdfea169e BYTES 2870 -->
```lean
import Invariant
import Mathlib.Logic.Relation
import Mathlib.Logic.Equiv.Basic
namespace Frustrated
abbrev OddTuple (n k) (G : Graph (Fin n)) := {c : Ambient n k // tupleOdd G c}
def oddRel {n k} (G : Graph (Fin n)) (c d : OddTuple n k G) := dihedralStep c.val d.val

theorem quotient_eq_step {n k} [NeZero k] (G : Graph (Fin n)) (c d : OddTuple n k G) :
    Quot.mk (oddRel (k := k) G) c = Quot.mk (oddRel (k := k) G) d ↔ dihedralStep c.val d.val := by
  constructor
  · intro h
    have hh : Relation.EqvGen (oddRel (k := k) G) c d := Quot.eqvGen_exact h
    clear h
    induction hh with
    | rel a b h => exact h
    | refl a => exact step_refl a.val
    | symm a b _ ih => exact step_symm ih
    | trans a b c _ _ h1 h2 => exact step_trans h1 h2
  · intro h
    exact Quot.sound (r := oddRel (k := k) G) h

def oddOrbitEquiv {n k} [NeZero k] (G : Graph (Fin n)) (c : OddTuple n k G) :
    {d : OddTuple n k G // dihedralStep c.val d.val} ≃
      {d : Ambient n k // dihedralStep c.val d} where
  toFun d := ⟨d.val.val,d.property⟩
  invFun d := ⟨⟨d.val, (tupleOdd_step G d.property).mp c.property⟩,d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem quotient_fiber_card {n k} [NeZero k] (hk : 3 ≤ k)
    (G : Graph (Fin n)) (q : Quot (oddRel (k := k) G)) :
    Nat.card {c : OddTuple n k G // Quot.mk (oddRel (k := k) G) c = q} = 2*k := by
  induction q using Quot.inductionOn with | h c =>
    let e : {d : OddTuple n k G // Quot.mk (oddRel (k := k) G) d = Quot.mk (oddRel (k := k) G) c} ≃
        {d : OddTuple n k G // dihedralStep c.val d.val} :=
      Equiv.subtypeEquivRight (fun d => by
        rw [eq_comm, quotient_eq_step])
    rw [Nat.card_congr e, Nat.card_congr (oddOrbitEquiv G c)]
    exact ambient_orbit_card hk c.val

theorem tuple_cycle_scale {n k} (hk : 3 ≤ k) (G : Graph (Fin n)) :
    tupleCount n k G = (2*k) * cycleCount n k G := by
  classical
  have : NeZero k := ⟨by omega⟩
  have ht : tupleCount n k G = Nat.card (OddTuple n k G) := by
    simp [tupleCount, OddTuple, tupleOdd, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [ht]
  let : Fintype (Quot (oddRel (k := k) G)) := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (Quot.mk (oddRel (k := k) G))), Nat.card_sigma]
  simp only [quotient_fiber_card hk G, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  rw [mul_comm]
  change 2*k*Fintype.card (Quot (oddRel (k := k) G)) =
    2*k*Nat.card (Quot (oddRel (k := k) G))
  rw [Nat.card_eq_fintype_card]

theorem strict_scale_cancel {n k} (hk : 3 ≤ k) (G H : Graph (Fin n)) :
    tupleCount n k G < tupleCount n k H ↔ cycleCount n k G < cycleCount n k H := by
  rw [tuple_cycle_scale hk, tuple_cycle_scale hk]
  exact Nat.mul_lt_mul_left (by omega)

#print axioms quotient_eq_step
#print axioms tuple_cycle_scale
#print axioms strict_scale_cancel
end Frustrated
```
<!-- LEAN-SOURCE-END Counting -->

<!-- LEAN-SOURCE-BEGIN WitnessCount SHA256 bdbd4503dc56fba7642988b6573c28d931f9c5e69ffcb2d4116829e8c46d98ea BYTES 3445 -->
```lean
import Counting
import Mathlib.Tactic.Ring
namespace Frustrated

theorem list_odd_tuple {n k} (G : Graph (Fin n)) (C : ListCycle (Fin n) k) :
    tupleOdd G C.toTuple ↔ frustrated G C := by
  rw [tupleOdd_list, ListCycle.toTuple_toList]
  rfl

abbrev CountWitness (n k) (G : Graph (Fin n)) :=
  {w : Witness (Fin n) // w.internal.length + 3 = k ∧
    cycleParity G [w.a,w.b,w.c,w.d] = true}

def CountWitness.firstList {n k G} (w : CountWitness n k G) : ListCycle (Fin n) k where
  vertices := w.val.first
  length_eq := by simpa [Witness.first] using w.property.1
  distinct := first_nodup w.val

def CountWitness.secondList {n k G} (w : CountWitness n k G) : ListCycle (Fin n) k where
  vertices := w.val.second
  length_eq := by simpa [Witness.second] using w.property.1
  distinct := second_nodup w.val

noncomputable def witnessEncode {n k} (G : Graph (Fin n)) (w : CountWitness n k G) :
    Bool × (OddTuple n k G × Fin n) := by
  classical
  by_cases h : frustrated G w.firstList
  · exact (false, (⟨w.firstList.toTuple, (list_odd_tuple G _).mpr h⟩, w.val.d))
  · have h' : frustrated G w.secondList := by
      have hh := exactly_one G w.val w.property.2
      change cycleParity G w.val.first ≠ cycleParity G w.val.second at hh
      change cycleParity G w.val.first ≠ true at h
      change cycleParity G w.val.second = true
      cases h1 : cycleParity G w.val.first <;>
        cases h2 : cycleParity G w.val.second <;> simp_all
    exact (true, (⟨w.secondList.toTuple, (list_odd_tuple G _).mpr h'⟩, w.val.b))

theorem firstList_recover {n k G} (w z : CountWitness n k G)
    (ht : w.firstList.toTuple = z.firstList.toTuple) (hd : w.val.d = z.val.d) : w = z := by
  apply Subtype.ext
  apply witness_first_recover _ _ _ hd
  have hc := (listTupleEquiv n k).injective ht
  exact congrArg ListCycle.vertices hc

theorem secondList_recover {n k G} (w z : CountWitness n k G)
    (ht : w.secondList.toTuple = z.secondList.toTuple) (hb : w.val.b = z.val.b) : w = z := by
  apply Subtype.ext
  apply witness_second_recover _ _ _ hb
  have hc := (listTupleEquiv n k).injective ht
  exact congrArg ListCycle.vertices hc

theorem witnessEncode_injective {n k} (G : Graph (Fin n)) :
    Function.Injective (witnessEncode (k := k) G) := by
  classical
  intro w z h
  unfold witnessEncode at h
  split_ifs at h with hw hz hz
  · have ht := congrArg (fun p => p.2.1.val) h
    have hd := congrArg (fun p => p.2.2) h
    exact firstList_recover w z ht hd
  · have hh := congrArg Prod.fst h
    contradiction
  · have hh := congrArg Prod.fst h
    contradiction
  · have ht := congrArg (fun p => p.2.1.val) h
    have hb := congrArg (fun p => p.2.2) h
    exact secondList_recover w z ht hb

theorem witness_bound_tuple {n k} (G : Graph (Fin n)) :
    Nat.card (CountWitness n k G) ≤ 2*n*tupleCount n k G := by
  have h := Nat.card_le_card_of_injective _ (witnessEncode_injective (k := k) G)
  have ht : Nat.card (OddTuple n k G) = tupleCount n k G := by
    simp [OddTuple, tupleOdd, tupleCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa [Nat.card_prod, ht, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem witness_bound_cycle {n k} (hk : 3 ≤ k) (G : Graph (Fin n)) :
    Nat.card (CountWitness n k G) ≤ 4*k*n*cycleCount n k G := by
  have h := witness_bound_tuple (k := k) G
  rw [tuple_cycle_scale hk] at h
  convert h using 1
  ring

#print axioms witness_bound_cycle
end Frustrated
```
<!-- LEAN-SOURCE-END WitnessCount -->

<!-- LEAN-SOURCE-BEGIN ExactWitness SHA256 01dc12bb5318b4358375cf9c8b85202274356b09d72b9658b2949a66499cf9aa BYTES 4522 -->
```lean
import WitnessCount
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.FinCases
namespace Frustrated

abbrev Outside {n} (q : Ambient n 4) := {v : Fin n // v ∉ Set.range q}

noncomputable def ExtensionWitness (n m) (G : Graph (Fin n)) :=
  (q : OddTuple n 4 G) × (Fin m ↪ Outside q.val)

theorem outside_card {n} (q : Ambient n 4) : Nat.card (Outside q) = n-4 := by
  classical
  let : Fintype (Outside q) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {v : Fin n // ¬ v ∈ Set.range q} = n-4
  rw [Fintype.card_subtype_compl]
  have hr : Fintype.card {v : Fin n // v ∈ Set.range q} = 4 := by
    let e : Fin 4 ≃ {v : Fin n // v ∈ Set.range q} :=
      Equiv.ofBijective (fun i => ⟨q i,⟨i,rfl⟩⟩)
        ⟨fun i j h => q.injective (congrArg Subtype.val h), by
          rintro ⟨v,⟨i,rfl⟩⟩
          exact ⟨i,rfl⟩⟩
    simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm
  rw [hr]
  simp

theorem extensionWitness_card (n m) (G : Graph (Fin n)) :
    Nat.card (ExtensionWitness n m G) =
      8 * cycleCount n 4 G * (n-4).descFactorial m := by
  classical
  let : Fintype (OddTuple n 4 G) := Fintype.ofFinite _
  unfold ExtensionWitness
  rw [Nat.card_sigma]
  have he (q : OddTuple n 4 G) :
      Nat.card (Fin m ↪ Outside q.val) = (n-4).descFactorial m := by
    let : Fintype (Outside q.val) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
    rw [← Nat.card_eq_fintype_card, outside_card]
    simp
  simp only [he, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  have ht : Nat.card (OddTuple n 4 G) = tupleCount n 4 G := by
    simp [OddTuple, tupleOdd, tupleCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Nat.card_eq_fintype_card, ht, tuple_cycle_scale (by decide : 3 ≤ 4)]

theorem extension_distinct {n m} (q : Ambient n 4) (e : Fin m ↪ Outside q) :
    (q 0 :: List.ofFn (fun i => (e i).val) ++ [q 2,q 1,q 3]).Nodup := by
  have hp : (List.ofFn (fun i => (e i).val)).Nodup :=
    List.nodup_ofFn_ofInjective (Subtype.val_injective.comp e.injective)
  have ho (i : Fin m) (j : Fin 4) : (e i).val ≠ q j := by
    intro h
    exact (e i).property ⟨j,h.symm⟩
  have hd := List.nodup_ofFn_ofInjective q.injective
  simp only [List.ofFn_succ, List.ofFn_zero, List.nodup_cons, List.mem_cons,
    List.not_mem_nil] at hd
  simp only [List.nodup_cons, List.nodup_append, List.mem_cons,
    List.not_mem_nil, not_false_eq_true]
  simp_all only [List.mem_ofFn]
  aesop

noncomputable def extensionToWitness {n m} (G : Graph (Fin n))
    (x : ExtensionWitness n m G) : CountWitness n (m+3) G := by
  let q := x.1.val
  let e := x.2
  let w : Witness (Fin n) :=
    { a := q 0, b := q 1, c := q 2, d := q 3
      internal := List.ofFn (fun i => (e i).val)
      distinct := extension_distinct q e }
  refine ⟨w, ?_, ?_⟩
  · simp [w]
  · have h := (tupleOdd_list G x.1.val).mp x.1.property
    simpa [tupleToList, List.ofFn_succ, List.ofFn_zero, w, q] using h

theorem extensionToWitness_injective {n m} (G : Graph (Fin n)) :
    Function.Injective (extensionToWitness (m := m) G) := by
  rintro ⟨⟨q,hq⟩,e⟩ ⟨⟨r,hr⟩,f⟩ h
  have hw := congrArg Subtype.val h
  have ha := congrArg Witness.a hw
  have hb := congrArg Witness.b hw
  have hc := congrArg Witness.c hw
  have hd := congrArg Witness.d hw
  change q 0 = r 0 at ha
  change q 1 = r 1 at hb
  change q 2 = r 2 at hc
  change q 3 = r 3 at hd
  have hqr : q = r := by
    apply Function.Embedding.ext
    intro i
    fin_cases i <;> assumption
  subst r
  have hef : e = f := by
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    have hp := congrArg Witness.internal hw
    change List.ofFn (fun j => (e j).val) = List.ofFn (fun j => (f j).val) at hp
    exact congrFun (List.ofFn_injective hp) i
  subst f
  rfl

theorem source_witness_inequality {n k} (hk : 3 ≤ k)
    (_hn : max 4 (k+1) ≤ n) (G : Graph (Fin n)) :
    8 * cycleCount n 4 G * (n-4).descFactorial (k-3) ≤
      4*k*n*cycleCount n k G := by
  have : Finite (CountWitness n (k-3+3) G) :=
    Finite.of_injective _ (witnessEncode_injective (k := k-3+3) G)
  have h := Nat.card_le_card_of_injective _
    (extensionToWitness_injective (m := k-3) G)
  rw [extensionWitness_card] at h
  have he : k-3+3 = k := by omega
  rw [he] at h
  exact h.trans (witness_bound_cycle hk G)

#print axioms extensionWitness_card
#print axioms extensionToWitness
#print axioms source_witness_inequality
end Frustrated
```
<!-- LEAN-SOURCE-END ExactWitness -->

<!-- LEAN-SOURCE-BEGIN Structural SHA256 d452d81bcb4504e2271acd7981b913faff85757e57732ea3ef3cccfbf829658b BYTES 4256 -->
```lean
import ExactWitness
import Mathlib.Tactic.Linarith
namespace Frustrated

theorem isolated_quadrilateral {V} (G : Graph V) (u v w x : V)
    (hu : ∀ z, G.edge u z = false) :
    cycleParity G [u,v,w,x] = xor (G.edge w v) (G.edge w x) := by
  simp [cycleParity, pathParity, hu, G.symm x u, G.symm v w]

abbrev DirectedError {n} (G : Graph (Fin n)) (U : Fin n → Bool) :=
  {p : Fin n × Fin n // p.1 ≠ p.2 ∧ G.edge p.1 p.2 ≠ U p.1}

abbrev MixedRows {n} (U : Fin n → Bool) :=
  {a : Fin n // U a = true} × {b : Fin n // U b = false}

def mixedError {n} (G : Graph (Fin n)) (U : Fin n → Bool)
    (p : MixedRows U) : DirectedError G U := by
  have hab : p.1.val ≠ p.2.val := by
    intro h
    have hh := p.1.property
    rw [h,p.2.property] at hh
    contradiction
  by_cases he : G.edge p.1.val p.2.val = true
  · exact ⟨(p.2.val,p.1.val), Ne.symm hab, by
      rw [G.symm, he, p.2.property]; decide⟩
  · exact ⟨(p.1.val,p.2.val), hab, by rw [p.1.property]; exact he⟩

theorem mixedError_injective {n} (G : Graph (Fin n)) (U : Fin n → Bool) :
    Function.Injective (mixedError G U) := by
  intro p q h
  have hp := p.1.property
  have hp' := p.2.property
  have hq := q.1.property
  have hq' := q.2.property
  have hv := congrArg Subtype.val h
  unfold mixedError at hv
  split_ifs at hv with he hf hf
  · have hh := Prod.mk.inj hv
    apply Prod.ext
    · exact Subtype.ext hh.2
    · exact Subtype.ext hh.1
  · have hh := Prod.mk.inj hv
    have hx := congrArg U hh.1
    simp_all
  · have hh := Prod.mk.inj hv
    have hx := congrArg U hh.1
    simp_all
  · have hh := Prod.mk.inj hv
    apply Prod.ext
    · exact Subtype.ext hh.1
    · exact Subtype.ext hh.2

theorem mixed_row_bound {n} (G : Graph (Fin n)) (U : Fin n → Bool) :
    Nat.card {a : Fin n // U a = true} * Nat.card {b : Fin n // U b = false} ≤
      Nat.card (DirectedError G U) := by
  have h := Nat.card_le_card_of_injective _ (mixedError_injective G U)
  simpa only [Nat.card_prod] using h

theorem row_preference_rigidity {n} (G : Graph (Fin n)) (U : Fin n → Bool)
    (herr : Nat.card (DirectedError G U) < n-1) :
    (∀ a, U a = false) ∨ (∀ a, U a = true) := by
  classical
  by_cases h0 : ∀ a, U a = false
  · exact Or.inl h0
  by_cases h1 : ∀ a, U a = true
  · exact Or.inr h1
  push Not at h0 h1
  obtain ⟨a,ha⟩ := h0
  obtain ⟨b,hb⟩ := h1
  have ha' : U a = true := by cases h : U a <;> simp_all
  have hb' : U b = false := by cases h : U b <;> simp_all
  let : Nonempty {a : Fin n // U a = true} := ⟨⟨a,ha'⟩⟩
  let : Nonempty {b : Fin n // U b = false} := ⟨⟨b,hb'⟩⟩
  have hp : 0 < Nat.card {a : Fin n // U a = true} := Nat.card_pos
  have lp : 0 < Nat.card {b : Fin n // U b = false} := Nat.card_pos
  have hc : Nat.card {b : Fin n // U b = false} =
      n - Nat.card {a : Fin n // U a = true} := by
    let e : {b : Fin n // U b = false} ≃ {b : Fin n // ¬ U b = true} :=
      Equiv.subtypeEquivRight (fun b => by cases U b <;> simp)
    rw [Nat.card_congr e]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp only [Fintype.card_fin, Nat.card_eq_fintype_card]
  have hn : Nat.card {a : Fin n // U a = true} ≤ n := by
    simpa using Nat.card_le_card_of_injective
      (fun x : {a : Fin n // U a = true} => x.val) Subtype.val_injective
  have hsum : Nat.card {a : Fin n // U a = true} +
      Nat.card {b : Fin n // U b = false} = n := by omega
  have hm := mixed_row_bound G U
  have hprod : 0 ≤ (Nat.card {a : Fin n // U a = true} - 1) *
      (Nat.card {b : Fin n // U b = false} - 1) := Nat.zero_le _
  have heq1 : Nat.card {a : Fin n // U a = true} - 1 + 1 =
      Nat.card {a : Fin n // U a = true} := by omega
  have heq2 : Nat.card {b : Fin n // U b = false} - 1 + 1 =
      Nat.card {b : Fin n // U b = false} := by omega
  have hi : Nat.card {a : Fin n // U a = true} * Nat.card {b : Fin n // U b = false} =
      (Nat.card {a : Fin n // U a = true} - 1 + 1) *
      (Nat.card {b : Fin n // U b = false} - 1 + 1) := by rw [heq1,heq2]
  have hsub : n-1+1 = n := by omega
  exfalso
  nlinarith only [hi,hprod,heq1,heq2,hsum,hm,herr,hsub]

#print axioms row_preference_rigidity
#print axioms isolated_quadrilateral
#print axioms mixed_row_bound
end Frustrated
```
<!-- LEAN-SOURCE-END Structural -->

<!-- LEAN-SOURCE-BEGIN Rows SHA256 5459de6a9a042436e53ae70ad66cb7bd4d8ec651abd50e53ac55cc8d5415dfd1 BYTES 2604 -->
```lean
import Structural
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Sigma
namespace Frustrated
/-- Off-diagonal neighbors in an actual finite symmetric graph. -/
abbrev RowNeighbor {n} (G : Graph (Fin n)) (w : Fin n) :=
  {v : Fin n // v ≠ w ∧ G.edge w v = true}
abbrev RowNonneighbor {n} (G : Graph (Fin n)) (w : Fin n) :=
  {v : Fin n // v ≠ w ∧ G.edge w v = false}
noncomputable def rowDegree {n} (G : Graph (Fin n)) (w : Fin n) :=
  Nat.card (RowNeighbor G w)
abbrev RowMixed {n} (G : Graph (Fin n)) :=
  (w : Fin n) × (RowNeighbor G w × RowNonneighbor G w)

theorem row_nonneighbor_card {n} (G : Graph (Fin n)) (w : Fin n) :
    Nat.card (RowNonneighbor G w) = n - 1 - rowDegree G w := by
  classical
  let e : {v : Fin n // ¬(v ≠ w ∧ G.edge w v = true)} ≃
      Option (RowNonneighbor G w) :=
    { toFun := fun v => if h : v.val = w then none else
        some ⟨v.val, h, by
          have hh := v.property
          cases he : G.edge w v.val <;> simp_all⟩
      invFun := fun v => match v with
        | none => ⟨w, by simp⟩
        | some v => ⟨v.val, by simp [v.property.2]⟩
      left_inv := by
        intro v
        dsimp
        split_ifs with h
        · exact Subtype.ext h.symm
        · rfl
      right_inv := by
        intro v
        cases v with
        | none => simp
        | some v => simp [v.property.1] }
  have hc := Fintype.card_subtype_compl (fun v : Fin n => v ≠ w ∧ G.edge w v = true)
  have hh := Nat.card_congr e
  simp only [Nat.card_eq_fintype_card, Fintype.card_option] at hh
  change Nat.card (RowNonneighbor G w) = n - 1 - Nat.card (RowNeighbor G w)
  simp only [Nat.card_eq_fintype_card]
  change Fintype.card (RowNonneighbor G w) = n - 1 - Fintype.card {v : Fin n // v ≠ w ∧ G.edge w v = true}
  simp only [Fintype.card_fin] at hc
  omega

theorem row_mixed_card {n} (G : Graph (Fin n)) :
    Nat.card (RowMixed G) =
      ∑ w : Fin n, rowDegree G w * (n-1-rowDegree G w) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro w _
  rw [Fintype.card_prod]
  simp only [← Nat.card_eq_fintype_card, row_nonneighbor_card, rowDegree]

/-- A mixed pair has a distinguished neighbor, so reversal is not counted twice. -/
theorem mixed_vertices_distinct {n} (G : Graph (Fin n)) (w : Fin n)
    (v : RowNeighbor G w) (x : RowNonneighbor G w) : v.val ≠ x.val := by
  intro h
  have he := v.property.2
  rw [h, x.property.2] at he
  contradiction

#print axioms row_nonneighbor_card
#print axioms row_mixed_card
#print axioms mixed_vertices_distinct
end Frustrated
```
<!-- LEAN-SOURCE-END Rows -->

<!-- LEAN-SOURCE-BEGIN Discrepancy SHA256 a610bd3b3c5d64f5389295bef8062fa2202e387cd334404e08012a910618b7dd BYTES 3709 -->
```lean
import Rows
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
namespace Frustrated
abbrev RowError {n} (G : Graph (Fin n)) (U : Fin n → Bool) (w : Fin n) :=
  {v : Fin n // v ≠ w ∧ G.edge w v ≠ U w}
def directedRowEquiv {n} (G : Graph (Fin n)) (U : Fin n → Bool) :
    DirectedError G U ≃ ((w : Fin n) × RowError G U w) where
  toFun p := ⟨p.val.1, ⟨p.val.2, Ne.symm p.property.1, p.property.2⟩⟩
  invFun p := ⟨(p.1,p.2.val), Ne.symm p.2.property.1, p.2.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
noncomputable def majority {n} (G : Graph (Fin n)) (w : Fin n) : Bool :=
  decide (n-1-rowDegree G w < rowDegree G w)

theorem degree_le {n} (G : Graph (Fin n)) (w : Fin n) :
    rowDegree G w ≤ n-1 := by
  classical
  have h := Fintype.card_subtype_le (fun v : Fin n => v ≠ w ∧ G.edge w v = true)
  have hc := Fintype.card_subtype_compl (fun v : Fin n => v ≠ w ∧ G.edge w v = true)
  have hn := row_nonneighbor_card G w
  -- The complement contains w, hence it is nonempty.
  have : Nonempty {v : Fin n // ¬(v ≠ w ∧ G.edge w v = true)} := ⟨⟨w, by simp⟩⟩
  have hp : 0 < Fintype.card {v : Fin n // ¬(v ≠ w ∧ G.edge w v = true)} :=
    Fintype.card_pos
  change Nat.card {v : Fin n // v ≠ w ∧ G.edge w v = true} ≤ n-1
  simp only [Nat.card_eq_fintype_card]
  simp only [Fintype.card_fin] at h hc
  omega

theorem row_error_card {n} (G : Graph (Fin n)) (w : Fin n) :
    Nat.card (RowError G (majority G) w) =
      min (rowDegree G w) (n-1-rowDegree G w) := by
  classical
  by_cases h : n-1-rowDegree G w < rowDegree G w
  · have e : RowError G (majority G) w ≃ RowNonneighbor G w :=
      Equiv.subtypeEquivRight (fun v => by
        simp only [majority, h, decide_true]
        cases G.edge w v <;> simp)
    rw [Nat.card_congr e, row_nonneighbor_card, Nat.min_eq_right (Nat.le_of_lt h)]
  · have e : RowError G (majority G) w ≃ RowNeighbor G w :=
      Equiv.subtypeEquivRight (fun v => by
        simp only [majority, h, decide_false]
        cases G.edge w v <;> simp)
    rw [Nat.card_congr e, Nat.min_eq_left (Nat.le_of_not_gt h)]
    rfl

theorem actual_directed_error_sum {n} (G : Graph (Fin n)) :
    Nat.card (DirectedError G (majority G)) =
      ∑ w : Fin n, min (rowDegree G w) (n-1-rowDegree G w) := by
  classical
  rw [Nat.card_congr (directedRowEquiv G (majority G)),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro w _
  rw [← Nat.card_eq_fintype_card, row_error_card]

theorem actual_discrepancy_product_bound {n} (G : Graph (Fin n)) :
    (n-1) * Nat.card (DirectedError G (majority G)) ≤
      2 * Nat.card (RowMixed G) := by
  classical
  rw [actual_directed_error_sum, row_mixed_card,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w _
  have hd := degree_le G w
  have he : rowDegree G w + (n-1-rowDegree G w) = n-1 := by omega
  rcases le_total (rowDegree G w) (n-1-rowDegree G w) with h | h
  · rw [Nat.min_eq_left h]
    have hp := Nat.mul_le_mul_left (rowDegree G w) h
    nlinarith
  · rw [Nat.min_eq_right h]
    have hp := Nat.mul_le_mul_left (n-1-rowDegree G w) h
    nlinarith

theorem actual_majority_rigidity {n} (G : Graph (Fin n))
    (h : 2 * Nat.card (RowMixed G) < (n-1)*(n-1)) :
    (∀ w, majority G w = false) ∨ (∀ w, majority G w = true) := by
  apply row_preference_rigidity G (majority G)
  have hp := actual_discrepancy_product_bound G
  by_contra hn
  have hh := Nat.mul_le_mul_left (n-1) (Nat.le_of_not_gt hn)
  omega
#print axioms actual_directed_error_sum
#print axioms actual_discrepancy_product_bound
#print axioms actual_majority_rigidity
end Frustrated
```
<!-- LEAN-SOURCE-END Discrepancy -->

<!-- LEAN-SOURCE-BEGIN UnorderedRows SHA256 2be3737cbafb5f6dc80ef431434f339dd1d76dbe60a63d9be90f212c754e4780 BYTES 3396 -->
```lean
import Discrepancy
namespace Frustrated
/-- An unordered off-diagonal pair meeting the row in exactly one edge. -/
abbrev MixedPair {n} (G : Graph (Fin n)) (w : Fin n) :=
  {s : Finset (Fin n) // s.card = 2 ∧
    (∀ v ∈ s, v ≠ w) ∧
    (∃ v ∈ s, G.edge w v = true) ∧ (∃ x ∈ s, G.edge w x = false)}
noncomputable def pairOfMixed {n} (G : Graph (Fin n)) (w : Fin n)
    (p : RowNeighbor G w × RowNonneighbor G w) : MixedPair G w := by
  classical
  refine ⟨{p.1.val,p.2.val}, ?_, ?_, ?_, ?_⟩
  · simp [mixed_vertices_distinct G w p.1 p.2]
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact p.1.property.1
    · exact p.2.property.1
  · exact ⟨p.1.val, by simp, p.1.property.2⟩
  · exact ⟨p.2.val, by simp, p.2.property.2⟩

theorem pairOfMixed_injective {n} (G : Graph (Fin n)) (w : Fin n) :
    Function.Injective (pairOfMixed G w) := by
  classical
  intro p q h
  have he := congrArg Subtype.val h
  change ({p.1.val,p.2.val} : Finset (Fin n)) = {q.1.val,q.2.val} at he
  have hv : p.1.val = q.1.val := by
    have hm : p.1.val ∈ ({q.1.val,q.2.val} : Finset (Fin n)) := by
      rw [← he]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact hm
    · have hp := p.1.property.2
      rw [hm,q.2.property.2] at hp
      contradiction
  have hx : p.2.val = q.2.val := by
    have hm : p.2.val ∈ ({q.1.val,q.2.val} : Finset (Fin n)) := by
      rw [← he]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · have hp := p.2.property.2
      rw [hm,q.1.property.2] at hp
      contradiction
    · exact hm
  exact Prod.ext (Subtype.ext hv) (Subtype.ext hx)

theorem pairOfMixed_surjective {n} (G : Graph (Fin n)) (w : Fin n) :
    Function.Surjective (pairOfMixed G w) := by
  classical
  intro s
  obtain ⟨v,hv,he⟩ := s.property.2.2.1
  obtain ⟨x,hx,hf⟩ := s.property.2.2.2
  have hne : v ≠ x := by intro h; rw [h,hf] at he; contradiction
  let p : RowNeighbor G w × RowNonneighbor G w :=
    (⟨v,s.property.2.1 v hv,he⟩,⟨x,s.property.2.1 x hx,hf⟩)
  refine ⟨p, Subtype.ext ?_⟩
  change ({v,x} : Finset (Fin n)) = s.val
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  · simp [s.property.1,hne]

noncomputable def mixedPairEquiv {n} (G : Graph (Fin n)) (w : Fin n) :
    (RowNeighbor G w × RowNonneighbor G w) ≃ MixedPair G w :=
  Equiv.ofBijective (pairOfMixed G w)
    ⟨pairOfMixed_injective G w,pairOfMixed_surjective G w⟩

/-- Actual unordered pair count: no factor two is present. -/
theorem unordered_mixed_pair_card {n} (G : Graph (Fin n)) (w : Fin n) :
    Nat.card (MixedPair G w) = rowDegree G w * (n-1-rowDegree G w) := by
  rw [← Nat.card_congr (mixedPairEquiv G w), Nat.card_prod,
    row_nonneighbor_card]
  rfl

theorem opposite_pair_card {n} (G : Graph (Fin n)) :
    Nat.card ((w : Fin n) × MixedPair G w) =
      ∑ w : Fin n, rowDegree G w * (n-1-rowDegree G w) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro w _
  rw [← Nat.card_eq_fintype_card, unordered_mixed_pair_card]
#print axioms mixedPairEquiv
#print axioms opposite_pair_card
end Frustrated
```
<!-- LEAN-SOURCE-END UnorderedRows -->

<!-- LEAN-SOURCE-BEGIN Incidence SHA256 ee4256e931abdec5778978fd2313f47435df5cd2b40eedb6366dd2825363e14f BYTES 4489 -->
```lean
import UnorderedRows
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.SuccPred
namespace Frustrated
def deleteVertex {n} (G : Graph (Fin (n+1))) (u : Fin (n+1)) : Graph (Fin n) where
  edge a b := G.edge (u.succAbove a) (u.succAbove b)
  symm a b := G.symm (u.succAbove a) (u.succAbove b)
  loopless a := G.loopless (u.succAbove a)
/-- Root fixed at u, with reversal resolved by putting the neighbor first. -/
abbrev CanonicalQuad {n} (G : Graph (Fin (n+1))) (u : Fin (n+1)) :=
  {c : Ambient (n+1) 4 // c 0 = u ∧ G.edge (c 2) (c 1) = true ∧
    G.edge (c 2) (c 3) = false}
def mixedTuple {n} (G : Graph (Fin (n+1))) (u : Fin (n+1))
    (p : RowMixed (deleteVertex G u)) : Ambient (n+1) 4 := by
  let v := p.2.1
  let x := p.2.2
  have hv := v.property.1
  have hx := x.property.1
  have hvx := mixed_vertices_distinct (deleteVertex G u) p.1 v x
  refine ⟨![u,u.succAbove v.val,u.succAbove p.1,u.succAbove x.val], ?_⟩
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [Fin.succAbove_ne, Fin.ne_succAbove]
def mixedCanonical {n} (G : Graph (Fin (n+1))) (u : Fin (n+1))
    (p : RowMixed (deleteVertex G u)) : CanonicalQuad G u :=
  ⟨mixedTuple G u p, by
    exact ⟨rfl,p.2.1.property.2,p.2.2.property.2⟩⟩

theorem mixedCanonical_injective {n} (G : Graph (Fin (n+1))) (u : Fin (n+1)) :
    Function.Injective (mixedCanonical G u) := by
  intro p q h
  have he := congrArg (fun c : CanonicalQuad G u => c.val 2) h
  have hw : p.1 = q.1 := Fin.succAbove_right_injective (by exact he)
  cases p with | mk w p =>
    cases q with | mk z q =>
      dsimp at hw
      subst z
      apply Sigma.mk.inj_iff.mpr
      refine ⟨rfl, ?_⟩
      apply heq_of_eq
      apply Prod.ext
      · apply Subtype.ext
        apply Fin.succAbove_right_injective (p := u)
        exact congrArg (fun c : CanonicalQuad G u => c.val 1) h
      · apply Subtype.ext
        apply Fin.succAbove_right_injective (p := u)
        exact congrArg (fun c : CanonicalQuad G u => c.val 3) h

theorem mixedCanonical_surjective {n} (G : Graph (Fin (n+1))) (u : Fin (n+1)) :
    Function.Surjective (mixedCanonical G u) := by
  intro c
  have h1 : c.val 1 ≠ u := by
    intro h
    have hh := c.val.injective (h.trans c.property.1.symm)
    have : (1 : Fin 4) ≠ 0 := by decide
    exact this hh
  have h2 : c.val 2 ≠ u := by
    intro h
    have hh := c.val.injective (h.trans c.property.1.symm)
    have : (2 : Fin 4) ≠ 0 := by decide
    exact this hh
  have h3 : c.val 3 ≠ u := by
    intro h
    have hh := c.val.injective (h.trans c.property.1.symm)
    have : (3 : Fin 4) ≠ 0 := by decide
    exact this hh
  obtain ⟨v,hv⟩ := Fin.exists_succAbove_eq h1
  obtain ⟨w,hw⟩ := Fin.exists_succAbove_eq h2
  obtain ⟨x,hx⟩ := Fin.exists_succAbove_eq h3
  have hvw : v ≠ w := by
    intro h
    have hh : c.val 1 = c.val 2 := by rw [← hv, ← hw,h]
    have := c.val.injective hh
    contradiction
  have hxw : x ≠ w := by
    intro h
    have hh : c.val 3 = c.val 2 := by rw [← hx, ← hw,h]
    have := c.val.injective hh
    contradiction
  let p : RowMixed (deleteVertex G u) := ⟨w,
    ⟨⟨v,hvw,by simpa [deleteVertex,hw,hv] using c.property.2.1⟩,
     ⟨x,hxw,by simpa [deleteVertex,hw,hx] using c.property.2.2⟩⟩⟩
  refine ⟨p, Subtype.ext ?_⟩
  apply DFunLike.ext
  intro i
  fin_cases i <;> simp [mixedCanonical,mixedTuple,p,hv,hw,hx,c.property.1]

noncomputable def canonicalQuadEquiv {n} (G : Graph (Fin (n+1))) (u : Fin (n+1)) :
    RowMixed (deleteVertex G u) ≃ CanonicalQuad G u :=
  Equiv.ofBijective (mixedCanonical G u)
    ⟨mixedCanonical_injective G u,mixedCanonical_surjective G u⟩

theorem canonical_quad_card {n} (G : Graph (Fin (n+1))) (u : Fin (n+1)) :
    Nat.card (CanonicalQuad G u) =
      ∑ w : Fin n, rowDegree (deleteVertex G u) w *
        (n-1-rowDegree (deleteVertex G u) w) := by
  rw [← Nat.card_congr (canonicalQuadEquiv G u),row_mixed_card]

theorem canonical_is_frustrated {n} (G : Graph (Fin (n+1))) (u : Fin (n+1))
    (hu : ∀ z, G.edge u z = false) (c : CanonicalQuad G u) :
    tupleOdd G c.val := by
  rw [tupleOdd_list]
  change cycleParity G (List.ofFn c.val) = true
  have hl : List.ofFn c.val = [c.val 0,c.val 1,c.val 2,c.val 3] := by
    simp [List.ofFn_succ]
  rw [hl,c.property.1,isolated_quadrilateral G u _ _ _ hu,
    c.property.2.1,c.property.2.2]
  rfl
#print axioms canonicalQuadEquiv
#print axioms canonical_quad_card
#print axioms canonical_is_frustrated
end Frustrated
```
<!-- LEAN-SOURCE-END Incidence -->

<!-- LEAN-SOURCE-BEGIN IncidentQuotient SHA256 dbb4ea433af623cda35c4c6990d1e44454078672d1d80e1510bf1b00dc8486b7 BYTES 4339 -->
```lean
import Incidence
namespace Frustrated
abbrev CycleThrough {n} (G : Graph (Fin (n+1))) (u : Fin (n+1)) :=
  {q : Quot (oddRel (k := 4) G) //
    ∃ c : OddTuple (n+1) 4 G, Quot.mk (oddRel G) c = q ∧ ∃ i, c.val i = u}
def canonicalClass {n} (G : Graph (Fin (n+1))) (u : Fin (n+1))
    (hu : ∀ z, G.edge u z = false) (c : CanonicalQuad G u) : CycleThrough G u :=
  ⟨Quot.mk (oddRel G) ⟨c.val,canonical_is_frustrated G u hu c⟩,
    ⟨⟨c.val,canonical_is_frustrated G u hu c⟩,rfl,0,c.property.1⟩⟩

theorem canonical_step_unique {n} (G : Graph (Fin (n+1))) (u : Fin (n+1))
    (c d : CanonicalQuad G u) (h : dihedralStep c.val d.val) : c = d := by
  obtain ⟨r,hr | hr⟩ := (dihedralStep_iff c.val d.val).mp h
  · have hh : c.val r = c.val 0 := by
      have h0 := congrArg (fun x : Ambient (n+1) 4 => x 0) hr
      change d.val 0 = c.val (0+r) at h0
      simpa only [zero_add,c.property.1,d.property.1] using h0.symm
    have hz : r = 0 := c.val.injective hh
    apply Subtype.ext
    simpa [hz,rot_zero] using hr.symm
  · have hh : c.val r = c.val 0 := by
      have h0 := congrArg (fun x : Ambient (n+1) 4 => x 0) hr
      change d.val 0 = c.val (r-0) at h0
      simpa only [sub_zero,c.property.1,d.property.1] using h0.symm
    have hz : r = 0 := c.val.injective hh
    have he := d.property.2.1
    rw [hr,hz] at he
    change G.edge (c.val (0-2)) (c.val (0-1)) = true at he
    have h2 : (0-2 : Fin 4) = 2 := by decide
    have h3 : (0-1 : Fin 4) = 3 := by decide
    rw [h2,h3,c.property.2.2] at he
    contradiction

theorem canonicalClass_injective {n} (G : Graph (Fin (n+1))) (u : Fin (n+1))
    (hu : ∀ z, G.edge u z = false) :
    Function.Injective (canonicalClass G u hu) := by
  intro c d h
  apply canonical_step_unique G u c d
  exact (quotient_eq_step G _ _).mp (congrArg Subtype.val h)

theorem odd_root_canonical {n} (G : Graph (Fin (n+1))) (u : Fin (n+1))
    (hu : ∀ z, G.edge u z = false) (c : OddTuple (n+1) 4 G)
    (i : Fin 4) (hi : c.val i = u) :
    ∃ d : CanonicalQuad G u, dihedralStep c.val d.val := by
  let r := rot c.val i
  have hr0 : r 0 = u := by
    change c.val (0+i) = u
    simpa only [zero_add] using hi
  have hodd : tupleOdd G r := (tupleOdd_rot G c.val i).mpr c.property
  have hp := (tupleOdd_list G r).mp hodd
  change cycleParity G (List.ofFn r) = true at hp
  have hl : List.ofFn r = [r 0,r 1,r 2,r 3] := by simp [List.ofFn_succ]
  rw [hl,hr0,isolated_quadrilateral G u _ _ _ hu] at hp
  by_cases he : G.edge (r 2) (r 1) = true
  · have hf : G.edge (r 2) (r 3) = false := by
      cases h : G.edge (r 2) (r 3) <;> simp_all
    exact ⟨⟨r,hr0,he,hf⟩,(dihedralStep_iff _ _).mpr ⟨i,Or.inl rfl⟩⟩
  · have he' : G.edge (r 2) (r 1) = false := by
      cases h : G.edge (r 2) (r 1) <;> simp_all
    have hf : G.edge (r 2) (r 3) = true := by
      cases h : G.edge (r 2) (r 3) <;> simp_all
    let d := refl r 0
    have hd0 : d 0 = u := by simpa [d,refl] using hr0
    have hd1 : G.edge (d 2) (d 1) = true := by exact hf
    have hd2 : G.edge (d 2) (d 3) = false := by exact he'
    refine ⟨⟨d,hd0,hd1,hd2⟩, ?_⟩
    exact step_trans ((dihedralStep_iff _ _).mpr ⟨i,Or.inl rfl⟩)
      ((dihedralStep_iff _ _).mpr ⟨0,Or.inr rfl⟩)

theorem canonicalClass_surjective {n} (G : Graph (Fin (n+1))) (u : Fin (n+1))
    (hu : ∀ z, G.edge u z = false) :
    Function.Surjective (canonicalClass G u hu) := by
  intro q
  obtain ⟨c,hc,i,hi⟩ := q.property
  obtain ⟨d,hd⟩ := odd_root_canonical G u hu c i hi
  refine ⟨d,Subtype.ext ?_⟩
  change Quot.mk (oddRel G) _ = q.val
  rw [← hc]
  exact (quotient_eq_step G _ _).mpr (step_symm hd)

noncomputable def incidentQuadEquiv {n} (G : Graph (Fin (n+1))) (u : Fin (n+1))
    (hu : ∀ z, G.edge u z = false) : CanonicalQuad G u ≃ CycleThrough G u :=
  Equiv.ofBijective (canonicalClass G u hu)
    ⟨canonicalClass_injective G u hu,canonicalClass_surjective G u hu⟩

theorem isolated_incidence_row_sum {n} (G : Graph (Fin (n+1))) (u : Fin (n+1))
    (hu : ∀ z, G.edge u z = false) :
    Nat.card (CycleThrough G u) =
      ∑ w : Fin n, rowDegree (deleteVertex G u) w *
        (n-1-rowDegree (deleteVertex G u) w) := by
  rw [← Nat.card_congr (incidentQuadEquiv G u hu),canonical_quad_card]
#print axioms incidentQuadEquiv
#print axioms isolated_incidence_row_sum
end Frustrated
```
<!-- LEAN-SOURCE-END IncidentQuotient -->

<!-- LEAN-SOURCE-BEGIN Averaging SHA256 fcf2999ec4edca83fd2fba3d492066963eced49738014186a6245a530adad222 BYTES 3321 -->
```lean
import IncidentQuotient
namespace Frustrated
theorem step_vertex_iff {n k} [NeZero k] {c d : Ambient n k}
    (h : dihedralStep c d) (u : Fin n) :
    (∃ i, c i = u) ↔ (∃ i, d i = u) := by
  obtain ⟨r, rfl | rfl⟩ := (dihedralStep_iff c d).mp h
  · constructor
    · rintro ⟨i,hi⟩
      refine ⟨i-r, ?_⟩
      change c (i-r+r) = u
      simpa using hi
    · rintro ⟨i,hi⟩
      exact ⟨i+r,hi⟩
  · constructor
    · rintro ⟨i,hi⟩
      refine ⟨r-i, ?_⟩
      change c (r-(r-i)) = u
      simpa using hi
    · rintro ⟨i,hi⟩
      exact ⟨r-i,hi⟩

abbrev VertexOn {n} (G : Graph (Fin (n+1))) (q : Quot (oddRel (k := 4) G)) :=
  {u : Fin (n+1) // ∃ c : OddTuple (n+1) 4 G,
    Quot.mk (oddRel G) c = q ∧ ∃ i, c.val i = u}

theorem vertexOn_card {n} (G : Graph (Fin (n+1)))
    (q : Quot (oddRel (k := 4) G)) : Nat.card (VertexOn G q) = 4 := by
  induction q using Quot.inductionOn with | h c =>
    have hp (u : Fin (n+1)) :
        (∃ d : OddTuple (n+1) 4 G, Quot.mk (oddRel G) d =
          Quot.mk (oddRel G) c ∧ ∃ i, d.val i = u) ↔ ∃ i, c.val i = u := by
      constructor
      · rintro ⟨d,hd,hv⟩
        exact (step_vertex_iff ((quotient_eq_step G d c).mp hd) u).mp hv
      · intro hv
        exact ⟨c,rfl,hv⟩
    let e : VertexOn G (Quot.mk (oddRel G) c) ≃
        {u : Fin (n+1) // ∃ i, c.val i = u} :=
      Equiv.subtypeEquivRight hp
    let f : Fin 4 → {u : Fin (n+1) // ∃ i, c.val i = u} :=
      fun i => ⟨c.val i,i,rfl⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j h
        exact c.val.injective (congrArg Subtype.val h)
      · rintro ⟨u,i,hi⟩
        exact ⟨i,Subtype.ext hi⟩
    rw [Nat.card_congr e, ← Nat.card_congr (Equiv.ofBijective f hf)]
    exact Nat.card_fin 4

def swapIncidence {n} (G : Graph (Fin (n+1))) :
    ((u : Fin (n+1)) × CycleThrough G u) ≃
      ((q : Quot (oddRel (k := 4) G)) × VertexOn G q) where
  toFun p := ⟨p.2.val,⟨p.1,p.2.property⟩⟩
  invFun p := ⟨p.2.val,⟨p.1,p.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem four_cycle_incidence_sum {n} (G : Graph (Fin (n+1))) :
    (∑ u : Fin (n+1), Nat.card (CycleThrough G u)) =
      4 * cycleCount (n+1) 4 G := by
  classical
  let : Fintype (Quot (oddRel (k := 4) G)) := Fintype.ofFinite _
  rw [← Nat.card_sigma, Nat.card_congr (swapIncidence G),Nat.card_sigma]
  simp only [vertexOn_card,Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul]
  rw [mul_comm]
  change 4 * Fintype.card (Quot (oddRel (k := 4) G)) = 4 * Nat.card (Quot (oddRel (k := 4) G))
  rw [Nat.card_eq_fintype_card]

theorem select_four_cycle_vertex {n} (G : Graph (Fin (n+1))) :
    ∃ u : Fin (n+1), (n+1) * Nat.card (CycleThrough G u) ≤
      4 * cycleCount (n+1) 4 G := by
  classical
  by_contra h
  push Not at h
  have hp : ∀ u : Fin (n+1), 4 * cycleCount (n+1) 4 G + 1 ≤
      (n+1) * Nat.card (CycleThrough G u) := by intro u; exact h u
  have hs := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset (Fin (n+1)))) => hp u)
  rw [← Finset.mul_sum,four_cycle_incidence_sum] at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] at hs
  nlinarith
#print axioms four_cycle_incidence_sum
#print axioms select_four_cycle_vertex
end Frustrated
```
<!-- LEAN-SOURCE-END Averaging -->

<!-- LEAN-SOURCE-BEGIN SwitchLaws SHA256 bdade938587fc4617ba0d9e11e9beb632dfd227ddf6ee402754e18caa01f8fff BYTES 2634 -->
```lean
import Averaging
namespace Frustrated
theorem tupleOdd_switch_iff {n k} (G : Graph (Fin n)) (U : Fin n → Bool)
    (c : Ambient n k) : tupleOdd (switch G U) c ↔ tupleOdd G c := by
  rw [tupleOdd_list,tupleOdd_list,cycle_switch]

def switchOddEquiv {n k} (G : Graph (Fin n)) (U : Fin n → Bool) :
    OddTuple n k G ≃ OddTuple n k (switch G U) where
  toFun c := ⟨c.val,(tupleOdd_switch_iff G U c.val).mpr c.property⟩
  invFun c := ⟨c.val,(tupleOdd_switch_iff G U c.val).mp c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def switchQuotEquiv {n k} (G : Graph (Fin n)) (U : Fin n → Bool) :
    Quot (oddRel (k := k) G) ≃ Quot (oddRel (k := k) (switch G U)) where
  toFun := Quot.map (switchOddEquiv G U) (fun _ _ h => h)
  invFun := Quot.map (switchOddEquiv G U).symm (fun _ _ h => h)
  left_inv q := by induction q using Quot.inductionOn with | h c => rfl
  right_inv q := by induction q using Quot.inductionOn with | h c => rfl

theorem cycleCount_switch {n k} (G : Graph (Fin n)) (U : Fin n → Bool) :
    cycleCount n k (switch G U) = cycleCount n k G :=
  (Nat.card_congr (switchQuotEquiv (k := k) G U)).symm

def switchThroughEquiv {n} (G : Graph (Fin (n+1))) (U : Fin (n+1) → Bool)
    (u : Fin (n+1)) : CycleThrough G u ≃ CycleThrough (switch G U) u where
  toFun q := ⟨switchQuotEquiv G U q.val, by
    obtain ⟨c,hc,hv⟩ := q.property
    exact ⟨switchOddEquiv G U c,congrArg (switchQuotEquiv G U) hc,hv⟩⟩
  invFun q := ⟨(switchQuotEquiv G U).symm q.val, by
    obtain ⟨c,hc,hv⟩ := q.property
    exact ⟨(switchOddEquiv G U).symm c,
      congrArg (switchQuotEquiv G U).symm hc,hv⟩⟩
  left_inv q := Subtype.ext ((switchQuotEquiv G U).left_inv q.val)
  right_inv q := Subtype.ext ((switchQuotEquiv G U).right_inv q.val)

theorem switch_neighborhood_isolates {V} (G : Graph V) (u : V) :
    ∀ z, (switch G (G.edge u)).edge u z = false := by
  intro z
  simp only [switch,cut,G.loopless]
  cases G.edge u z <;> rfl

theorem singleton_complement_repair {V} [DecidableEq V] (G : Graph V) (u : V)
    (hu : ∀ z, G.edge u z = false) :
    (∀ z, (switch (complement G) (fun a => decide (a=u))).edge u z = false) ∧
    (∀ a b, a ≠ u → b ≠ u →
      (switch (complement G) (fun z => decide (z=u))).edge a b =
        (complement G).edge a b) := by
  constructor
  · intro z
    by_cases h : u = z
    · subst z; exact (switch _ _).loopless _
    · simp [switch,cut,complement,h,Ne.symm h,hu]
  · intro a b ha hb
    simp [switch,cut,ha,hb]
#print axioms cycleCount_switch
#print axioms switchThroughEquiv
#print axioms singleton_complement_repair
end Frustrated
```
<!-- LEAN-SOURCE-END SwitchLaws -->

<!-- LEAN-SOURCE-BEGIN EdgeBounds SHA256 8f5c3640d0e9f8ee7e4cb4e796f0c007ac96f676fae84e4f0dcfdb9cf4d62ea1 BYTES 2802 -->
```lean
import SwitchLaws
namespace Frustrated
abbrev EdgePair {n} (G : Graph (Fin n)) :=
  {p : Fin n × Fin n // p.1 < p.2 ∧ G.edge p.1 p.2 = true}
noncomputable def edgeCount {n} (G : Graph (Fin n)) := Nat.card (EdgePair G)
theorem edgeCount_eq_editDistance {n} (G : Graph (Fin n)) :
    edgeCount G = editDistance n G (cut (fun _ => false)) := by
  classical
  simp only [edgeCount,editDistance,Nat.card_eq_fintype_card,Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro p _
  simp [cut]

theorem sparse_from_false_rows {n} (G : Graph (Fin n)) (U : Fin n → Bool)
    (h : ∀ w, U w = false) : edgeCount G ≤ Nat.card (DirectedError G U) := by
  let f : EdgePair G → DirectedError G U :=
    fun p => ⟨p.val,ne_of_lt p.property.1,by rw [h,p.property.2]; decide⟩
  exact Nat.card_le_card_of_injective f (fun _ _ he => Subtype.ext (congrArg (fun z : DirectedError G U => z.val) he))

theorem sparse_from_true_rows {n} (G : Graph (Fin n)) (U : Fin n → Bool)
    (h : ∀ w, U w = true) : edgeCount (complement G) ≤ Nat.card (DirectedError G U) := by
  have he (p : EdgePair (complement G)) : G.edge p.val.1 p.val.2 = false := by
    have hp := p.property.2
    have hn := ne_of_lt p.property.1
    simp only [complement,hn,ite_false] at hp
    cases hv : G.edge p.val.1 p.val.2 <;> simp_all
  let f : EdgePair (complement G) → DirectedError G U :=
    fun p => ⟨p.val,ne_of_lt p.property.1,by rw [h,he p]; decide⟩
  exact Nat.card_le_card_of_injective f (fun _ _ hh => Subtype.ext (congrArg (fun z : DirectedError G U => z.val) hh))

theorem editDistance_switch_cut {n} (G : Graph (Fin n)) (U : Fin n → Bool) :
    editDistance n (switch G U) (cut U) = edgeCount G := by
  classical
  rw [edgeCount_eq_editDistance]
  unfold editDistance
  congr 1
  apply Finset.filter_congr
  intro p _
  simp only [switch,cut]
  cases G.edge p.1 p.2 <;> cases U p.1 <;> cases U p.2 <;> simp

theorem nearCut_of_sparse_switch {n t} (G : Graph (Fin n)) (U : Fin n → Bool)
    (h : edgeCount G ≤ t) : NearCut n t (switch G U) :=
  ⟨U,by rw [editDistance_switch_cut]; exact h⟩

theorem switch_involutive {V} (G : Graph V) (U : V → Bool) :
    switch (switch G U) U = G := by
  have he : (switch (switch G U) U).edge = G.edge := by
    funext a b
    simp only [switch,cut]
    cases G.edge a b <;> cases U a <;> cases U b <;> rfl
  generalize hh : switch (switch G U) U = H at he ⊢
  cases G
  cases H
  cases he
  rfl

theorem nearCut_of_switch_sparse {n t} (G : Graph (Fin n)) (U : Fin n → Bool)
    (h : edgeCount (switch G U) ≤ t) : NearCut n t G := by
  have hh := nearCut_of_sparse_switch (switch G U) U h
  rwa [switch_involutive] at hh
#print axioms nearCut_of_switch_sparse
#print axioms sparse_from_false_rows
#print axioms sparse_from_true_rows
end Frustrated
```
<!-- LEAN-SOURCE-END EdgeBounds -->

<!-- LEAN-SOURCE-BEGIN Normalization SHA256 a054de60f72216d5295ee4528bdfd47b2ec7be0709160d09fbaa6c26e31be850 BYTES 2553 -->
```lean
import EdgeBounds
namespace Frustrated
theorem select_switched_row_control {n} (G : Graph (Fin (n+1))) :
    ∃ u : Fin (n+1),
      let H := switch G (G.edge u)
      (∀ z, H.edge u z = false) ∧
      (n+1) * Nat.card (RowMixed (deleteVertex H u)) ≤
        4 * cycleCount (n+1) 4 G := by
  obtain ⟨u,hu⟩ := select_four_cycle_vertex G
  refine ⟨u,switch_neighborhood_isolates G u,?_⟩
  have hi := isolated_incidence_row_sum (switch G (G.edge u)) u
    (switch_neighborhood_isolates G u)
  rw [← row_mixed_card] at hi
  rw [← hi,← Nat.card_congr (switchThroughEquiv G (G.edge u) u)]
  exact hu

theorem bounded_discrepancy_of_f4 {n D} (hn : 3 ≤ n)
    (G : Graph (Fin (n+1))) (hf : cycleCount (n+1) 4 G ≤ D*(n+1)*(n+1)) :
    ∃ u : Fin (n+1),
      let H := switch G (G.edge u)
      (∀ z, H.edge u z = false) ∧
      Nat.card (DirectedError (deleteVertex H u) (majority (deleteVertex H u))) ≤ 16*D := by
  obtain ⟨u,hu,hrow⟩ := select_switched_row_control G
  refine ⟨u,hu,?_⟩
  let B := deleteVertex (switch G (G.edge u)) u
  have hm : Nat.card (RowMixed B) ≤ 4*D*(n+1) := by
    have ht : (n+1)*Nat.card (RowMixed B) ≤ (n+1)*(4*D*(n+1)) := by
      change (n+1)*Nat.card (RowMixed B) ≤ _ at hrow
      nlinarith [hf]
    exact Nat.le_of_mul_le_mul_left ht (by omega)
  have hp := actual_discrepancy_product_bound B
  have ht : (n-1)*Nat.card (DirectedError B (majority B)) ≤ (n-1)*(16*D) := by
    have hh : 8*D*(n+1) ≤ (n-1)*(16*D) := by
      have hn' : n+1 ≤ 2*(n-1) := by omega
      nlinarith
    nlinarith [hm]
  exact Nat.le_of_mul_le_mul_left ht (by omega)

theorem deleted_sparse_normal_form {n D} (hn : 3 ≤ n) (hlarge : 16*D < n-1)
    (G : Graph (Fin (n+1))) (hf : cycleCount (n+1) 4 G ≤ D*(n+1)*(n+1)) :
    ∃ u : Fin (n+1),
      let H := switch G (G.edge u)
      let B := deleteVertex H u
      (∀ z, H.edge u z = false) ∧
      (edgeCount B ≤ 16*D ∨ edgeCount (complement B) ≤ 16*D) := by
  obtain ⟨u,hu,herr⟩ := bounded_discrepancy_of_f4 hn G hf
  refine ⟨u,hu,?_⟩
  let B := deleteVertex (switch G (G.edge u)) u
  have hr : Nat.card (DirectedError B (majority B)) < n-1 := lt_of_le_of_lt herr hlarge
  rcases row_preference_rigidity B (majority B) hr with h0 | h1
  · exact Or.inl (le_trans (sparse_from_false_rows B (majority B) h0) herr)
  · exact Or.inr (le_trans (sparse_from_true_rows B (majority B) h1) herr)
#print axioms select_switched_row_control
#print axioms bounded_discrepancy_of_f4
#print axioms deleted_sparse_normal_form
end Frustrated
```
<!-- LEAN-SOURCE-END Normalization -->

<!-- LEAN-SOURCE-BEGIN WholeNormalization SHA256 95c0c3781cb78f0e692526e289134cdca038e97ab82a2f35c54b33599d103880 BYTES 4092 -->
```lean
import Normalization
namespace Frustrated
noncomputable def removeVertex {n} (u v : Fin (n+1)) (h : v ≠ u) : Fin n :=
  Classical.choose (Fin.exists_succAbove_eq h)
theorem removeVertex_spec {n} (u v : Fin (n+1)) (h : v ≠ u) :
    u.succAbove (removeVertex u v h) = v :=
  Classical.choose_spec (Fin.exists_succAbove_eq h)

theorem isolated_edge_endpoints {n} (Q : Graph (Fin (n+1))) (u : Fin (n+1))
    (hu : ∀ z, Q.edge u z = false) (p : EdgePair Q) :
    p.val.1 ≠ u ∧ p.val.2 ≠ u := by
  constructor
  · intro h
    have he := p.property.2
    rw [h,hu] at he
    contradiction
  · intro h
    have he := p.property.2
    rw [h,Q.symm,hu] at he
    contradiction

noncomputable def liftError {n} (Q : Graph (Fin (n+1))) (u : Fin (n+1))
    (hu : ∀ z, Q.edge u z = false) (B : Graph (Fin n)) (U : Fin n → Bool)
    (herr : ∀ a b, Q.edge (u.succAbove a) (u.succAbove b) = true →
      B.edge a b ≠ U a) (p : EdgePair Q) : DirectedError B U := by
  let ha := (isolated_edge_endpoints Q u hu p).1
  let hb := (isolated_edge_endpoints Q u hu p).2
  let a := removeVertex u p.val.1 ha
  let b := removeVertex u p.val.2 hb
  have hsa := removeVertex_spec u p.val.1 ha
  have hsb := removeVertex_spec u p.val.2 hb
  refine ⟨(a,b),?_,herr a b ?_⟩
  · intro h
    have hh := congrArg u.succAbove h
    change u.succAbove a = u.succAbove b at hh
    rw [hsa,hsb] at hh
    exact (ne_of_lt p.property.1) hh
  · rw [hsa,hsb]
    exact p.property.2

theorem liftError_injective {n} (Q : Graph (Fin (n+1))) (u : Fin (n+1))
    (hu : ∀ z, Q.edge u z = false) (B : Graph (Fin n)) (U : Fin n → Bool)
    (herr : ∀ a b, Q.edge (u.succAbove a) (u.succAbove b) = true →
      B.edge a b ≠ U a) :
    Function.Injective (liftError Q u hu B U herr) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · have hh := congrArg (fun z : DirectedError B U => u.succAbove z.val.1) h
    simpa only [liftError,removeVertex_spec] using hh
  · have hh := congrArg (fun z : DirectedError B U => u.succAbove z.val.2) h
    simpa only [liftError,removeVertex_spec] using hh

theorem lift_sparse_bound {n} (Q : Graph (Fin (n+1))) (u : Fin (n+1))
    (hu : ∀ z, Q.edge u z = false) (B : Graph (Fin n)) (U : Fin n → Bool)
    (herr : ∀ a b, Q.edge (u.succAbove a) (u.succAbove b) = true →
      B.edge a b ≠ U a) :
    edgeCount Q ≤ Nat.card (DirectedError B U) :=
  Nat.card_le_card_of_injective _ (liftError_injective Q u hu B U herr)

theorem whole_sparse_normal_form {n D} (hn : 3 ≤ n) (hlarge : 16*D < n-1)
    (G : Graph (Fin (n+1))) (hf : cycleCount (n+1) 4 G ≤ D*(n+1)*(n+1)) :
    ∃ u : Fin (n+1),
      let H := switch G (G.edge u)
      edgeCount H ≤ 16*D ∨
      edgeCount (switch (complement H) (fun z => decide (z=u))) ≤ 16*D := by
  classical
  obtain ⟨u,hu,herr⟩ := bounded_discrepancy_of_f4 hn G hf
  let H := switch G (G.edge u)
  let B := deleteVertex H u
  have hr : Nat.card (DirectedError B (majority B)) < n-1 := lt_of_le_of_lt herr hlarge
  refine ⟨u,?_⟩
  rcases row_preference_rigidity B (majority B) hr with h0 | h1
  · apply Or.inl
    apply le_trans (lift_sparse_bound H u hu B (majority B) ?_) herr
    intro a b he
    change H.edge (u.succAbove a) (u.succAbove b) ≠ majority B a
    rw [h0 a,he]
    decide
  · apply Or.inr
    let Q := switch (complement H) (fun z => decide (z=u))
    have hQ := singleton_complement_repair H u hu
    apply le_trans (lift_sparse_bound Q u hQ.1 B (majority B) ?_) herr
    intro a b he
    have hab : u.succAbove a ≠ u.succAbove b := by
      intro h
      rw [h,Q.loopless] at he
      contradiction
    have hnotu := hQ.2 (u.succAbove a) (u.succAbove b)
      (Fin.succAbove_ne u a) (Fin.succAbove_ne u b)
    change Q.edge (u.succAbove a) (u.succAbove b) = _ at hnotu
    rw [hnotu] at he
    simp only [complement,hab,ite_false] at he
    change H.edge (u.succAbove a) (u.succAbove b) ≠ majority B a
    rw [h1 a]
    cases hv : H.edge (u.succAbove a) (u.succAbove b) <;> simp_all
#print axioms whole_sparse_normal_form
#print axioms lift_sparse_bound
end Frustrated
```
<!-- LEAN-SOURCE-END WholeNormalization -->

<!-- LEAN-SOURCE-BEGIN ComplementLaw SHA256 c300dae2fbc8357d86095b8cc5a1f004eabc08967e9495a431049bc7fbb2903e BYTES 5141 -->
```lean
import WholeNormalization
namespace Frustrated
theorem bitParity_not (l : List Bool) :
    bitParity (l.map Bool.not) =
      if l.length % 2 = 0 then bitParity l else !(bitParity l) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons,bitParity,List.length_cons,ih]
    by_cases hp : l.length % 2 = 0
    · have hs : (l.length+1)%2 ≠ 0 := by omega
      simp only [hp,ite_true,hs,ite_false]
      cases b <;> cases bitParity l <;> rfl
    · have hs : (l.length+1)%2 = 0 := by omega
      simp only [hp,ite_false,hs,ite_true]
      cases b <;> cases bitParity l <;> rfl

theorem tuple_complement_bits {n k} (hk : 3 ≤ k) (G : Graph (Fin n))
    (c : Ambient n k) :
    cycleBits (complement G) (List.ofFn c) =
      (cycleBits G (List.ofFn c)).map Bool.not := by
  rw [cycleBits_ofFn,cycleBits_ofFn, List.map_ofFn]
  congr 1
  funext i
  have hn : c i ≠ c ⟨(i.val+1)%k,Nat.mod_lt _ (by omega)⟩ := by
    intro h
    have hh := c.injective h
    have hv := congrArg Fin.val hh
    have hi := i.isLt
    have hm : (i.val+1)%k ≠ i.val := by
      by_cases hs : i.val+1 < k
      · rw [Nat.mod_eq_of_lt hs]; omega
      · have he : i.val+1=k := by omega
        rw [he,Nat.mod_self]; omega
    exact hm hv.symm
  simp [complement,hn]

theorem tupleOdd_complement_iff {n k} (hk : 3 ≤ k) (G : Graph (Fin n))
    (c : Ambient n k) :
    tupleOdd (complement G) c ↔
      if k%2=0 then tupleOdd G c else ¬ tupleOdd G c := by
  rw [tupleOdd_list,tupleOdd_list]
  change cycleParity (complement G) (List.ofFn c) = true ↔
    if k%2=0 then cycleParity G (List.ofFn c) = true
      else ¬ cycleParity G (List.ofFn c) = true
  rw [← cycleBits_parity,tuple_complement_bits hk G c,bitParity_not]
  have hl : (cycleBits G (List.ofFn c)).length = k := by
    rw [cycleBits_ofFn,List.length_ofFn]
  rw [hl]
  rw [cycleBits_parity]
  by_cases h : k%2=0 <;> simp only [h,ite_true,ite_false]
  cases cycleParity G (List.ofFn c) <;> decide

noncomputable def totalCycleCount (n k : Nat) :=
  Nat.card (Quot (@dihedralStep n k))

theorem total_cycle_scale {n k} (hk : 3 ≤ k) :
    Nat.card (Ambient n k) = (2*k)*totalCycleCount n k := by
  classical
  have : NeZero k := ⟨by omega⟩
  let : Fintype (Quot (@dihedralStep n k)) := Fintype.ofFinite _
  have hf (q : Quot (@dihedralStep n k)) :
      Nat.card {c : Ambient n k // Quot.mk dihedralStep c=q} = 2*k := by
    induction q using Quot.inductionOn with | h c =>
      have he (d : Ambient n k) :
          Quot.mk dihedralStep d = Quot.mk dihedralStep c ↔ dihedralStep c d := by
        constructor
        · intro h
          have hh := Quot.eqvGen_exact h
          clear h
          have hs : dihedralStep d c := by
            induction hh with
            | rel a b h => exact h
            | refl a => exact step_refl a
            | symm a b _ ih => exact step_symm ih
            | trans a b c _ _ h1 h2 => exact step_trans h1 h2
          exact step_symm hs
        · intro h
          exact Quot.sound (step_symm h)
      rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
      exact ambient_orbit_card hk c
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (Quot.mk (@dihedralStep n k))),Nat.card_sigma]
  simp only [hf,Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul]
  rw [mul_comm]
  change (2*k)*Fintype.card (Quot (@dihedralStep n k)) =
    (2*k)*Nat.card (Quot (@dihedralStep n k))
  rw [Nat.card_eq_fintype_card]

theorem complement_even_cycleCount {n k} (hk : 3 ≤ k) (he : k%2=0)
    (G : Graph (Fin n)) : cycleCount n k (complement G) = cycleCount n k G := by
  classical
  have hc : tupleCount n k (complement G) = tupleCount n k G := by
    unfold tupleCount
    congr 1
    apply Finset.filter_congr
    intro c _
    change tupleOdd (complement G) c ↔ tupleOdd G c
    simpa only [he,ite_true] using tupleOdd_complement_iff hk G c
  rw [tuple_cycle_scale hk,tuple_cycle_scale hk] at hc
  exact Nat.eq_of_mul_eq_mul_left (by omega) hc

theorem complement_odd_cycleCount {n k} (hk : 3 ≤ k) (ho : k%2≠0)
    (G : Graph (Fin n)) :
    cycleCount n k G + cycleCount n k (complement G) = totalCycleCount n k := by
  classical
  have hc : tupleCount n k G + tupleCount n k (complement G) = Nat.card (Ambient n k) := by
    have ht (H : Graph (Fin n)) : tupleCount n k H = Fintype.card {c : Ambient n k // tupleOdd H c} := by
      rw [Fintype.card_subtype]
      unfold tupleCount
      congr 1
      apply Finset.filter_congr
      intro c _
      rfl
    rw [ht,ht]
    let e : {c : Ambient n k // tupleOdd (complement G) c} ≃
        {c : Ambient n k // ¬ tupleOdd G c} :=
      Equiv.subtypeEquivRight (fun c => by
        simpa only [ho,ite_false] using tupleOdd_complement_iff hk G c)
    rw [Fintype.card_congr e,Fintype.card_subtype_compl,Nat.card_eq_fintype_card]
    have hh := Fintype.card_subtype_le (tupleOdd (k := k) G)
    omega
  rw [tuple_cycle_scale hk,tuple_cycle_scale hk,total_cycle_scale hk,← Nat.mul_add] at hc
  exact Nat.eq_of_mul_eq_mul_left (by omega) hc
#print axioms complement_even_cycleCount
#print axioms complement_odd_cycleCount
#print axioms total_cycle_scale
end Frustrated
```
<!-- LEAN-SOURCE-END ComplementLaw -->

<!-- LEAN-SOURCE-BEGIN StarBound SHA256 605c6d88852809b4ba6c220bd2aea9df26b7206f42d09ad3ff1af2955bc94104 BYTES 3263 -->
```lean
import ComplementLaw
namespace Frustrated
abbrev StarDirected (n s : Nat) :=
  {p : Fin n × Fin n // (star n s).edge p.1 p.2 = true}
noncomputable def starDirectedEncode {n s} (p : StarDirected n s) : Bool × Fin s := by
  have hp := p.property
  simp only [star,decide_eq_true_eq] at hp
  by_cases h : p.val.1.val = 0
  · have hh : 1 ≤ p.val.2.val ∧ p.val.2.val ≤ s := by rcases hp with hp | hp <;> omega
    exact (false,⟨p.val.2.val-1,by omega⟩)
  · have hh : p.val.2.val = 0 ∧ 1 ≤ p.val.1.val ∧ p.val.1.val ≤ s := by
      rcases hp with hp | hp <;> omega
    exact (true,⟨p.val.1.val-1,by omega⟩)

theorem starDirectedEncode_injective {n s} :
    Function.Injective (@starDirectedEncode n s) := by
  intro p q h
  have hp := p.property
  have hq := q.property
  simp only [star,decide_eq_true_eq] at hp hq
  have hb := congrArg Prod.fst h
  have hi := congrArg (fun z : Bool × Fin s => z.2.val) h
  unfold starDirectedEncode at hb hi
  split_ifs at hb hi with h1 h2 h2
  all_goals
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> dsimp at * <;> omega

theorem star_directed_card (n s) : Nat.card (StarDirected n s) ≤ 2*s := by
  have h := Nat.card_le_card_of_injective _ (@starDirectedEncode_injective n s)
  simpa [Nat.card_prod,Nat.card_eq_fintype_card] using h

abbrev RestPositions {k} (i j : Fin k) := {a : Fin k // a ≠ i ∧ a ≠ j}
theorem rest_positions_card {k} (i j : Fin k) (h : i ≠ j) :
    Nat.card (RestPositions i j) = k-2 := by
  classical
  let e : RestPositions i j ≃ {a : Fin k // ¬ (a=i ∨ a=j)} :=
    Equiv.subtypeEquivRight (fun a => by tauto)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  have he : Fintype.card {a : Fin k // a=i ∨ a=j} = 2 := by
    rw [Fintype.card_subtype]
    have hf : (Finset.univ.filter (fun a : Fin k => a=i ∨ a=j)) = {i,j} := by ext a; simp
    rw [hf]
    simp [h]
  rw [he,Fintype.card_fin]

abbrev EdgePositionStar {n k} (s) (i j : Fin k) :=
  {c : Ambient n k // (star n s).edge (c i) (c j) = true}
def starPositionEncode {n k s} (i j : Fin k) (c : EdgePositionStar (n := n) s i j) :
    StarDirected n s × (RestPositions i j → Fin n) :=
  (⟨(c.val i,c.val j),c.property⟩,fun a => c.val a.val)

theorem starPositionEncode_injective {n k s} (i j : Fin k) :
    Function.Injective (@starPositionEncode n k s i j) := by
  intro c d h
  apply Subtype.ext
  apply Function.Embedding.ext
  intro a
  by_cases hi : a=i
  · subst a
    exact congrArg (fun z : StarDirected n s × (RestPositions i j → Fin n) => z.1.val.1) h
  by_cases hj : a=j
  · subst a
    exact congrArg (fun z : StarDirected n s × (RestPositions i j → Fin n) => z.1.val.2) h
  exact congrArg (fun z : StarDirected n s × (RestPositions i j → Fin n) => z.2 ⟨a,hi,hj⟩) h

theorem star_position_card {n k s} (i j : Fin k) (h : i ≠ j) :
    Nat.card (EdgePositionStar (n := n) s i j) ≤ 2*s*n^(k-2) := by
  classical
  have he := Nat.card_le_card_of_injective _ (@starPositionEncode_injective n k s i j)
  rw [Nat.card_prod,Nat.card_fun,rest_positions_card i j h,Nat.card_fin] at he
  exact le_trans he (Nat.mul_le_mul_right _ (star_directed_card n s))
#print axioms star_directed_card
#print axioms star_position_card
end Frustrated
```
<!-- LEAN-SOURCE-END StarBound -->

<!-- LEAN-SOURCE-BEGIN ThresholdTransfer SHA256 19cc778161d93ac8034c1738f90cc37657ffe3b62c368bff766273956623f6c1 BYTES 3727 -->
```lean
import StarBound
namespace Frustrated
def nextIndex {k} (i : Fin k) : Fin k :=
  ⟨(i.val+1)%k,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩
theorem nextIndex_ne {k} (hk : 3 ≤ k) (i : Fin k) : i ≠ nextIndex i := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  change i.val = (i.val+1)%k at hv
  by_cases hs : i.val+1 < k
  · rw [Nat.mod_eq_of_lt hs] at hv
    omega
  · have he : i.val+1=k := by omega
    rw [he,Nat.mod_self] at hv
    omega

noncomputable def starOddWitness {n k s} (c : OddTuple n k (star n s)) :
    (i : Fin k) × EdgePositionStar (n := n) s i (nextIndex i) := by
  classical
  have hp := c.property
  unfold tupleOdd at hp
  have hh : 0 < (Finset.univ.filter (fun i : Fin k =>
      (star n s).edge (c.val i) (c.val (nextIndex i)))).card := by
    change (Finset.univ.filter (fun i : Fin k =>
      (star n s).edge (c.val i) (c.val (nextIndex i)))).card % 2 = 1 at hp
    omega
  let i := Classical.choose (Finset.card_pos.mp hh)
  have hi := Classical.choose_spec (Finset.card_pos.mp hh)
  exact ⟨i,⟨c.val,(Finset.mem_filter.mp hi).2⟩⟩

theorem starOddWitness_injective {n k s} :
    Function.Injective (@starOddWitness n k s) := by
  intro c d h
  have hh := congrArg (fun p : (i : Fin k) × EdgePositionStar (n := n) s i (nextIndex i) =>
    p.2.val) h
  exact Subtype.ext hh

theorem tupleCount_card {n k} (G : Graph (Fin n)) :
    tupleCount n k G = Nat.card (OddTuple n k G) := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  unfold tupleCount
  congr 1
  apply Finset.filter_congr
  intro c _
  rfl

theorem star_cycle_upper {n k s} (hk : 3 ≤ k) :
    cycleCount n k (star n s) ≤ s*n^(k-2) := by
  classical
  have h := Nat.card_le_card_of_injective _ (@starOddWitness_injective n k s)
  rw [Nat.card_sigma] at h
  have hu : (∑ i : Fin k, Nat.card (EdgePositionStar (n := n) s i (nextIndex i))) ≤
      k*(2*s*n^(k-2)) := by
    calc
      _ ≤ ∑ _ : Fin k, 2*s*n^(k-2) :=
        Finset.sum_le_sum (fun i _ => star_position_card i (nextIndex i) (nextIndex_ne hk i))
      _ = _ := by simp [Nat.mul_comm]
  rw [← tupleCount_card,tuple_cycle_scale hk] at h
  have ht : (2*k)*cycleCount n k (star n s) ≤ (2*k)*(s*n^(k-2)) := by nlinarith
  exact Nat.le_of_mul_le_mul_left ht (by omega)

theorem threshold_f4_bound {n k s} (hk : 3 ≤ k) (hn : 2*(k+1) ≤ n)
    (G : Graph (Fin n))
    (hth : cycleCount n k G < cycleCount n k (star n s)) :
    cycleCount n 4 G ≤ (k*s*2^(k-3))*n*n := by
  have hn4 : 4 ≤ n := by omega
  have hw := source_witness_inequality hk (by omega) G
  have hu := star_cycle_upper (n := n) (s := s) hk
  have hm : k-2 = (k-3)+1 := by omega
  have hb : 0 < n-k := by omega
  have hd : (n-k)^(k-3) ≤ (n-4).descFactorial (k-3) := by
    have he : (n-4)+1-(k-3) = n-k := by omega
    simpa only [he] using Nat.pow_sub_le_descFactorial (n-4) (k-3)
  have hn2 : n ≤ 2*(n-k) := by omega
  have hp : n^(k-3) ≤ 2^(k-3)*(n-k)^(k-3) := by
    simpa only [Nat.mul_pow] using Nat.pow_le_pow_left hn2 (k-3)
  have hpos : 0 < (n-k)^(k-3) := Nat.pow_pos hb
  rw [hm,Nat.pow_succ] at hu
  have hg : cycleCount n k G ≤ s*(n^(k-3)*n) := le_trans (Nat.le_of_lt hth) hu
  have hright : 4*k*n*cycleCount n k G ≤
      (4*k*s*2^(k-3)*n*n)*(n-k)^(k-3) := by
    calc
      _ ≤ 4*k*n*(s*(n^(k-3)*n)) := Nat.mul_le_mul_left _ hg
      _ ≤ 4*k*n*(s*((2^(k-3)*(n-k)^(k-3))*n)) := by gcongr
      _ = _ := by ring
  have hleft : (8*cycleCount n 4 G)*(n-k)^(k-3) ≤
      (4*k*s*2^(k-3)*n*n)*(n-k)^(k-3) := by
    exact le_trans (Nat.mul_le_mul_left _ hd) (le_trans hw hright)
  have hc := Nat.le_of_mul_le_mul_right hleft hpos
  nlinarith
#print axioms star_cycle_upper
#print axioms threshold_f4_bound
end Frustrated
```
<!-- LEAN-SOURCE-END ThresholdTransfer -->

<!-- LEAN-SOURCE-BEGIN FiniteEdges SHA256 558d41e8a9f9f168418447094529b03be7f017d747b2389611636d37c3cc315c BYTES 2555 -->
```lean
import ThresholdTransfer
import Mathlib.Data.Sym.Sym2
namespace Frustrated
noncomputable instance sym2FinFintype {n} : Fintype (Sym2 (Fin n)) := Fintype.ofFinite _
def cycleEdge {n k} (c : Ambient n k) (i : Fin k) : Sym2 (Fin n) :=
  s(c i,c (nextIndex i))

theorem cycleEdge_injective {n k} (hk : 3 ≤ k) (c : Ambient n k) :
    Function.Injective (cycleEdge c) := by
  intro i j h
  rcases Sym2.eq_iff.mp h with h | h
  · exact c.injective h.1
  · have h1 := c.injective h.1
    have h2 := c.injective h.2
    have hv1 := congrArg Fin.val h1
    have hv2 := congrArg Fin.val h2
    change i.val = (j.val+1)%k at hv1
    change (i.val+1)%k = j.val at hv2
    have hi := i.isLt
    have hj := j.isLt
    by_cases hi' : i.val+1<k
    · rw [Nat.mod_eq_of_lt hi'] at hv2
      by_cases hj' : j.val+1<k
      · rw [Nat.mod_eq_of_lt hj'] at hv1
        omega
      · have he : j.val+1=k := by omega
        rw [he,Nat.mod_self] at hv1
        omega
    · have he : i.val+1=k := by omega
      rw [he,Nat.mod_self] at hv2
      have hj' : j.val+1<k := by omega
      rw [Nat.mod_eq_of_lt hj'] at hv1
      omega

def edgePresent {n} (G : Graph (Fin n)) : Sym2 (Fin n) → Bool :=
  Sym2.lift ⟨G.edge,G.symm⟩
noncomputable def graphEdges {n} (G : Graph (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical
  exact Finset.univ.filter (fun e => edgePresent G e = true)
noncomputable def cycleSupport {n k} (c : Ambient n k) : Finset (Sym2 (Fin n)) := by
  classical
  exact Finset.univ.image (cycleEdge c)

theorem cycleSupport_card {n k} (hk : 3 ≤ k) (c : Ambient n k) :
    (cycleSupport c).card = k := by
  classical
  exact (Finset.card_image_of_injective _ (cycleEdge_injective hk c)).trans (by simp)

theorem graph_cycle_intersection {n k} (G : Graph (Fin n)) (c : Ambient n k) :
    graphEdges G ∩ cycleSupport c =
      (Finset.univ.filter (fun i => G.edge (c i) (c (nextIndex i)) = true)).image
        (cycleEdge c) := by
  classical
  ext e
  simp only [graphEdges,cycleSupport,Finset.mem_inter,Finset.mem_filter,
    Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · rintro ⟨he,i,_,rfl⟩
    exact ⟨i,he,rfl⟩
  · rintro ⟨i,he,rfl⟩
    exact ⟨he,i,rfl⟩

theorem tupleOdd_edge_subset {n k} (hk : 3 ≤ k) (G : Graph (Fin n)) (c : Ambient n k) :
    tupleOdd G c ↔ (graphEdges G ∩ cycleSupport c).card % 2 = 1 := by
  classical
  rw [graph_cycle_intersection,Finset.card_image_of_injective _ (cycleEdge_injective hk c)]
  rfl
#print axioms cycleEdge_injective
#print axioms tupleOdd_edge_subset
end Frustrated
```
<!-- LEAN-SOURCE-END FiniteEdges -->

<!-- LEAN-SOURCE-BEGIN SubsetExpansion SHA256 c665ca3a461a4ef0bdd9ffbef366fb890c924a51ca51693f4e87813c71820787 BYTES 3103 -->
```lean
import FiniteEdges
import Mathlib.Algebra.Ring.Parity
namespace Frustrated
attribute [local instance] Classical.propDecidable
theorem powerset_signed_sum {α : Type} (A : Finset α) :
    (∑ F ∈ A.powerset, (-2 : Int)^F.card) = (-1 : Int)^A.card := by
  classical
  have h := Finset.prod_add (fun _ : α => (-2 : Int)) (fun _ => (1 : Int)) A
  simpa using h.symm

theorem restricted_powerset_sum {α : Type} [DecidableEq α] (E C : Finset α) :
    (∑ F ∈ E.powerset, if F ⊆ C then (-2 : Int)^F.card else 0) =
      (-1 : Int)^(E∩C).card := by
  classical
  have hf : E.powerset.filter (fun F => F ⊆ C) = (E∩C).powerset := by
    ext F
    simp only [Finset.mem_filter,Finset.mem_powerset,Finset.subset_inter_iff]
  rw [← Finset.sum_filter,hf,powerset_signed_sum]

/-- Exact finite expansion over actual graph-edge subsets; doubled to avoid division. -/
theorem cycle_subset_expansion {n k : Nat} (hk : 3 ≤ k) (G : Graph (Fin n)) (c : Ambient n k) :
    (2 : Int) * (if tupleOdd G c then 1 else 0) =
      1 - ∑ F ∈ (graphEdges G).powerset,
        if F ⊆ cycleSupport c then (-2 : Int)^F.card else 0 := by
  classical
  rw [restricted_powerset_sum,tupleOdd_edge_subset hk G c,neg_one_pow_eq_ite]
  simp only [Nat.even_iff]
  have hm := Nat.mod_lt (graphEdges G ∩ cycleSupport c).card (by decide : 0<2)
  by_cases h : (graphEdges G ∩ cycleSupport c).card % 2 = 0
  · simp [h]
  · have hn : (graphEdges G ∩ cycleSupport c).card % 2 = 1 := by omega
    simp [hn]

noncomputable def tupleCompletions {n k : Nat} (F : Finset (Sym2 (Fin n))) : Nat :=
  Nat.card {c : Ambient n k // F ⊆ cycleSupport c}

theorem subset_expansion_tuple_sum {n k : Nat} (hk : 3 ≤ k) (G : Graph (Fin n)) :
    (2 : Int) * tupleCount n k G =
      (Nat.card (Ambient n k) : Int) -
      ∑ F ∈ (graphEdges G).powerset, (-2 : Int)^F.card * tupleCompletions (k := k) F := by
  classical
  have h := congrArg (fun f : Ambient n k → Int => ∑ c, f c)
    (funext (cycle_subset_expansion hk G))
  have ht : (∑ c : Ambient n k, if tupleOdd G c then (1 : Int) else 0) = tupleCount n k G := by
    rw [tupleCount_card,Nat.card_eq_fintype_card,Fintype.card_subtype]
    simp
  have hf (F : Finset (Sym2 (Fin n))) :
      (∑ c : Ambient n k, if F ⊆ cycleSupport c then (-2 : Int)^F.card else 0) =
        (-2 : Int)^F.card * tupleCompletions (k := k) F := by
    unfold tupleCompletions
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    simp [Finset.sum_ite,mul_comm]
  rw [← Finset.mul_sum,ht,Finset.sum_sub_distrib] at h
  rw [Finset.sum_comm] at h
  simp_rw [hf] at h
  simpa [Nat.card_eq_fintype_card] using h

theorem subset_expansion_cycle_scale {n k : Nat} (hk : 3 ≤ k) (G : Graph (Fin n)) :
    (4*(k : Int)) * cycleCount n k G =
      (Nat.card (Ambient n k) : Int) -
      ∑ F ∈ (graphEdges G).powerset, (-2 : Int)^F.card * tupleCompletions (k := k) F := by
  have h := subset_expansion_tuple_sum hk G
  rw [tuple_cycle_scale hk] at h
  push_cast at h
  nlinarith [h]
#print axioms cycle_subset_expansion
#print axioms subset_expansion_cycle_scale
end Frustrated
```
<!-- LEAN-SOURCE-END SubsetExpansion -->

<!-- LEAN-SOURCE-BEGIN PrefixCompletions SHA256 f7c9fde24e982db06712e50f5b28ee051437707934963c523c3a378107934d2d BYTES 3852 -->
```lean
import SubsetExpansion
namespace Frustrated
abbrev OutsidePrefix {n r} (q : Ambient n r) := {v : Fin n // v ∉ Set.range q}
abbrev FixedPrefix {n r} (m : Nat) (q : Ambient n r) :=
  {c : Ambient n (r+m) // ∀ i : Fin r, c (Fin.castAdd m i) = q i}

def joinPrefix {n r m} (q : Ambient n r) (e : Fin m ↪ OutsidePrefix q) :
    FixedPrefix m q := by
  let c : Ambient n (r+m) :=
    { toFun := Fin.addCases q (fun i => (e i).val)
      inj' := by
        intro i j h
        cases i using Fin.addCases with
        | left i =>
          cases j using Fin.addCases with
          | left j =>
            simp only [Fin.addCases_left] at h
            exact congrArg (Fin.castAdd m) (q.injective h)
          | right j =>
            simp only [Fin.addCases_left,Fin.addCases_right] at h
            exact False.elim ((e j).property ⟨i,h⟩)
        | right i =>
          cases j using Fin.addCases with
          | left j =>
            simp only [Fin.addCases_left,Fin.addCases_right] at h
            exact False.elim ((e i).property ⟨j,h.symm⟩)
          | right j =>
            simp only [Fin.addCases_right] at h
            exact congrArg (Fin.natAdd r) (e.injective (Subtype.ext h)) }
  refine ⟨c,?_⟩
  intro i
  change Fin.addCases q (fun j => (e j).val) (Fin.castAdd m i) = q i
  exact Fin.addCases_left i

def tailPrefix {n r m} (q : Ambient n r) (c : FixedPrefix m q) :
    Fin m ↪ OutsidePrefix q where
  toFun i := ⟨c.val (Fin.natAdd r i),by
    rintro ⟨j,hj⟩
    have hh : c.val (Fin.castAdd m j) = c.val (Fin.natAdd r i) :=
      (c.property j).trans hj
    have he := congrArg Fin.val (c.val.injective hh)
    have hj' := j.isLt
    change j.val = r+i.val at he
    omega⟩
  inj' i j h := by
    have hh := c.val.injective (congrArg Subtype.val h)
    have he := congrArg Fin.val hh
    change r+i.val = r+j.val at he
    apply Fin.ext
    omega

def prefixCompletionEquiv {n r m} (q : Ambient n r) :
    (Fin m ↪ OutsidePrefix q) ≃ FixedPrefix m q where
  toFun := joinPrefix q
  invFun := tailPrefix q
  left_inv e := by
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    change Fin.addCases q (fun j => (e j).val) (Fin.natAdd r i) = (e i).val
    exact Fin.addCases_right i
  right_inv c := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    cases i using Fin.addCases with
    | left i =>
      change Fin.addCases q (fun j => c.val (Fin.natAdd r j)) (Fin.castAdd m i) = c.val (Fin.castAdd m i)
      rw [Fin.addCases_left]
      exact (c.property i).symm
    | right i =>
      change Fin.addCases q (fun j => c.val (Fin.natAdd r j)) (Fin.natAdd r i) = c.val (Fin.natAdd r i)
      exact Fin.addCases_right i

theorem outside_prefix_card {n r} (q : Ambient n r) :
    Nat.card (OutsidePrefix q) = n-r := by
  classical
  let : Fintype (OutsidePrefix q) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  change Fintype.card {v : Fin n // ¬ v ∈ Set.range q} = n-r
  rw [Fintype.card_subtype_compl]
  have hr : Fintype.card {v : Fin n // v ∈ Set.range q} = r := by
    let e : Fin r ≃ {v : Fin n // v ∈ Set.range q} :=
      Equiv.ofBijective (fun i => ⟨q i,⟨i,rfl⟩⟩)
        ⟨fun i j h => q.injective (congrArg Subtype.val h),by
          rintro ⟨v,⟨i,rfl⟩⟩
          exact ⟨i,rfl⟩⟩
    simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm
  rw [hr,Fintype.card_fin]

theorem fixed_prefix_card {n r m} (q : Ambient n r) :
    Nat.card (FixedPrefix m q) = (n-r).descFactorial m := by
  classical
  let : Fintype (OutsidePrefix q) := Fintype.ofFinite _
  rw [← Nat.card_congr (prefixCompletionEquiv (m := m) q),
    Nat.card_eq_fintype_card,Fintype.card_embedding_eq]
  rw [← Nat.card_eq_fintype_card,outside_prefix_card]
  simp
#print axioms fixed_prefix_card
#print axioms prefixCompletionEquiv
end Frustrated
```
<!-- LEAN-SOURCE-END PrefixCompletions -->

<!-- LEAN-SOURCE-BEGIN AdjacentCount SHA256 b860b2f804c0cb7368e41cc054986d2d836de3d299810c5775d010dd63cb9c14 BYTES 4686 -->
```lean
import AdjacentBijection
import PrefixCompletions
import Mathlib.Tactic.FinCases
namespace Frustrated
/-- Same unordered support definition as the inherited FiniteEdges module;
    kept in this small dependency branch to avoid rebuilding unrelated graph lemmas. -/
def adjacentSupport {n k} [NeZero k] (c : Ambient n k) : Finset (Sym2 (Fin n)) := by
  classical
  exact Finset.univ.image (fun i : Fin k => s(c i,c (i+1)))

theorem pair_iff_support {n k} [NeZero k] (c : Ambient n k) (a b : Fin n) :
    HasCyclePair c a b ↔ s(a,b) ∈ adjacentSupport c := by
  classical
  simp only [adjacentSupport,Finset.mem_image,Finset.mem_univ,true_and]
  rfl

theorem castAdd_three_0 (m : Nat) :
    Fin.castAdd m (0 : Fin 3) = (0 : Fin (3+m)) := by
  apply Fin.ext
  norm_num [Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 0<3+m)]

theorem castAdd_three_1 (m : Nat) :
    Fin.castAdd m (1 : Fin 3) = (1 : Fin (3+m)) := by
  apply Fin.ext
  norm_num [Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 1<3+m)]

theorem castAdd_three_2 (m : Nat) :
    Fin.castAdd m (2 : Fin 3) = (2 : Fin (3+m)) := by
  apply Fin.ext
  norm_num [Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 2<3+m)]

noncomputable def pathPrefixEquiv {n m} (q : Ambient n 3) :
    PathPrefix (k:=3+m) q ≃ FixedPrefix m q where
  toFun c := ⟨c.val,by
    intro i
    fin_cases i
    · change c.val (Fin.castAdd m (0 : Fin 3)) = q 0
      simpa only [castAdd_three_0,castAdd_three_1,castAdd_three_2] using c.property.1
    · change c.val (Fin.castAdd m (1 : Fin 3)) = q 1
      simpa only [castAdd_three_0,castAdd_three_1,castAdd_three_2] using c.property.2.1
    · change c.val (Fin.castAdd m (2 : Fin 3)) = q 2
      simpa only [castAdd_three_0,castAdd_three_1,castAdd_three_2] using c.property.2.2⟩
  invFun c := ⟨c.val,by
    have h₀ := c.property 0
    have h₁ := c.property 1
    have h₂ := c.property 2
    simpa only [castAdd_three_0,castAdd_three_1,castAdd_three_2] using And.intro h₀ (And.intro h₁ h₂)⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv c := by apply Subtype.ext; rfl

theorem adjacent_tuple_count {n m} (q : Ambient n 3) :
    Nat.card (AdjacentTuples (k:=3+m) q) = 2*(3+m)*(n-3).descFactorial m := by
  have h := Nat.card_congr (adjacentPlacementEquiv (k:=3+m) (by omega) q)
  rw [← h,Nat.card_prod,Nat.card_prod]
  rw [Nat.card_congr (pathPrefixEquiv (m:=m) q),fixed_prefix_card]
  simp [Nat.card_eq_fintype_card]

theorem adjacent_support_count {n m} (q : Ambient n 3) :
    Nat.card {c : Ambient n (3+m) //
      ({s(q 0,q 1),s(q 1,q 2)} : Finset (Sym2 (Fin n))) ⊆ adjacentSupport c} =
      2*(3+m)*(n-3).descFactorial m := by
  classical
  have he : (fun c : Ambient n (3+m) =>
      ({s(q 0,q 1),s(q 1,q 2)} : Finset (Sym2 (Fin n))) ⊆ adjacentSupport c) =
      (fun c => HasCyclePair c (q 0) (q 1) ∧ HasCyclePair c (q 1) (q 2)) := by
    funext c
    apply propext
    simp [Finset.insert_subset_iff,pair_iff_support]
  change Nat.card (Subtype _) = _
  rw [he]
  exact adjacent_tuple_count q
theorem support_definition_bridge {n k} [NeZero k] (c : Ambient n k) :
    cycleSupport c = adjacentSupport c := by
  classical
  unfold cycleSupport adjacentSupport
  congr 1
  funext i
  unfold cycleEdge nextIndex
  rw [succ_as_add]

theorem adjacent_completion_count {n m} (q : Ambient n 3) :
    Nat.card {c : Ambient n (3+m) //
      ({s(q 0,q 1),s(q 1,q 2)} : Finset (Sym2 (Fin n))) ⊆ cycleSupport c} =
      2*(3+m)*(n-3).descFactorial m := by
  simp_rw [support_definition_bridge]
  exact adjacent_support_count q
noncomputable def adjacentCompletionEquiv {n m} (q : Ambient n 3) :
    {c : Ambient n (3+m) //
      ({s(q 0,q 1),s(q 1,q 2)} : Finset (Sym2 (Fin n))) ⊆ cycleSupport c} ≃
      Bool × (Fin (3+m) × FixedPrefix m q) := by
  classical
  let e : {c : Ambient n (3+m) //
      ({s(q 0,q 1),s(q 1,q 2)} : Finset (Sym2 (Fin n))) ⊆ cycleSupport c} ≃
      AdjacentTuples (k:=3+m) q :=
    { toFun := fun c => ⟨c.val,by
        simpa [support_definition_bridge,Finset.insert_subset_iff,← pair_iff_support]
          using c.property⟩
      invFun := fun c => ⟨c.val,by
        simpa [support_definition_bridge,Finset.insert_subset_iff,← pair_iff_support]
          using c.property⟩
      left_inv := fun c => by apply Subtype.ext; rfl
      right_inv := fun c => by apply Subtype.ext; rfl }
  exact e.trans ((adjacentPlacementEquiv (k:=3+m) (by omega) q).symm.trans
    ((Equiv.prodCongr (Equiv.refl (Bool × Fin (3+m))) (pathPrefixEquiv q)).trans
      (Equiv.prodAssoc Bool (Fin (3+m)) (FixedPrefix m q))))
#print axioms adjacentCompletionEquiv
#print axioms adjacent_completion_count
#print axioms adjacent_support_count
end Frustrated
```
<!-- LEAN-SOURCE-END AdjacentCount -->

<!-- LEAN-SOURCE-BEGIN SingletonCount SHA256 b74b7f077307806bee2978a3d3781bcfba519ebad1225c66eee4ed176d529d40 BYTES 3943 -->
```lean
import AdjacentCount
namespace Frustrated
abbrev EdgePrefix {n k : Nat} [NeZero k] (q : Ambient n 2) :=
  {c : Ambient n k // c 0=q 0 ∧ c 1=q 1}
abbrev SingletonTuples {n k : Nat} [NeZero k] (q : Ambient n 2) :=
  {c : Ambient n k // HasCyclePair c (q 0) (q 1)}

theorem singleton_normalize {n k} [NeZero k] (c : Ambient n k)
    (q : Ambient n 2) (h : HasCyclePair c (q 0) (q 1)) :
    ∃ d : Ambient n k, dihedralStep c d ∧ d 0=q 0 ∧ d 1=q 1 := by
  obtain ⟨x,y,hx,hy,hxy⟩ := pair_positions c (q 0) (q 1) h
  rcases hxy with hxy | hxy
  · refine ⟨rot c x,(dihedralStep_iff _ _).mpr ⟨x,Or.inl rfl⟩,?_,?_⟩
    · change c (0+x)=q 0; simpa using hx
    · change c (1+x)=q 1; simpa only [hxy,add_comm] using hy
  · refine ⟨refl c x,(dihedralStep_iff _ _).mpr ⟨x,Or.inr rfl⟩,?_,?_⟩
    · change c (x-0)=q 0; simpa using hx
    · change c (x-1)=q 1
      have he : x-1=y := by rw [hxy]; abel
      simpa only [he] using hy

noncomputable def singletonPlacement {n k} [NeZero k] (q : Ambient n 2)
    (p : (Bool × Fin k) × EdgePrefix (k:=k) q) : SingletonTuples (k:=k) q := by
  have h : HasCyclePair p.2.val (q 0) (q 1) := by
    refine ⟨0,?_⟩
    simp only [zero_add,p.2.property.1,p.2.property.2]
  let e := orbitMap p.2.val p.1
  exact ⟨e.val,pair_step _ _ e.property _ _ h⟩

theorem singletonPlacement_bijective {n k} [NeZero k] (hk : 3 ≤ k)
    (q : Ambient n 2) : Function.Bijective (singletonPlacement (k:=k) q) := by
  constructor
  · rintro ⟨p,c⟩ ⟨r,d⟩ h
    have he : (orbitMap c.val p).val=(orbitMap d.val r).val := congrArg Subtype.val h
    have hc : dihedralStep c.val d.val :=
      step_trans (orbitMap c.val p).property
        (he ▸ step_symm (orbitMap d.val r).property)
    have hcd : c=d := Subtype.ext (two_point_orbit_unique hk c.val d.val
      (d.property.1.trans c.property.1.symm)
      (d.property.2.trans c.property.2.symm) hc)
    subst d
    have hpr : p=r := (orbitMap_bijective hk c.val).1 (Subtype.ext he)
    subst r
    rfl
  · intro c
    obtain ⟨d,hd,h₀,h₁⟩ := singleton_normalize c.val q c.property
    let e : EdgePrefix (k:=k) q := ⟨d,h₀,h₁⟩
    obtain ⟨p,hp⟩ := (orbitMap_bijective hk d).2 ⟨c.val,step_symm hd⟩
    refine ⟨(p,e),?_⟩
    apply Subtype.ext
    change (orbitMap d p).val=c.val
    exact congrArg Subtype.val hp

theorem castAdd_two_0 (m : Nat) :
    Fin.castAdd m (0 : Fin 2) = (0 : Fin (2+m)) := by
  apply Fin.ext
  norm_num [Fin.val_ofNat]
theorem castAdd_two_1 (m : Nat) :
    Fin.castAdd m (1 : Fin 2) = (1 : Fin (2+m)) := by
  apply Fin.ext
  norm_num [Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 1<2+m)]

noncomputable def edgePrefixEquiv {n m} (q : Ambient n 2) :
    EdgePrefix (k:=2+m) q ≃ FixedPrefix m q where
  toFun c := ⟨c.val,by
    intro i
    fin_cases i
    · change c.val (Fin.castAdd m (0:Fin 2))=q 0
      simpa only [castAdd_two_0] using c.property.1
    · change c.val (Fin.castAdd m (1:Fin 2))=q 1
      simpa only [castAdd_two_1] using c.property.2⟩
  invFun c := ⟨c.val,by
    have h₀ := c.property 0
    have h₁ := c.property 1
    simpa only [castAdd_two_0,castAdd_two_1] using And.intro h₀ h₁⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv c := by apply Subtype.ext; rfl

theorem singleton_completion_count {n m} (hm : 1 ≤ m) (q : Ambient n 2) :
    Nat.card {c : Ambient n (2+m) // s(q 0,q 1) ∈ cycleSupport c} =
      2*(2+m)*(n-2).descFactorial m := by
  classical
  have he : Nat.card {c : Ambient n (2+m) // s(q 0,q 1) ∈ cycleSupport c} =
      Nat.card (SingletonTuples (k:=2+m) q) := by
    simp_rw [support_definition_bridge,← pair_iff_support]
  rw [he,← Nat.card_congr (Equiv.ofBijective _ (singletonPlacement_bijective (k:=2+m) (by omega) q))]
  rw [Nat.card_prod,Nat.card_prod,Nat.card_congr (edgePrefixEquiv (m:=m) q),fixed_prefix_card]
  simp [Nat.card_eq_fintype_card]
#print axioms singleton_completion_count
end Frustrated
```
<!-- LEAN-SOURCE-END SingletonCount -->

<!-- LEAN-SOURCE-BEGIN FixedPositions SHA256 19f6ff2676cab33034dcd55d117aee9e85939da0196abbb73bfe5d1904e97974 BYTES 1650 -->
```lean
import SingletonCount
import Mathlib.Logic.Equiv.Fintype
namespace Frustrated
abbrev FixedPositions {n r k} (a : Fin r ↪ Fin k) (q : Ambient n r) :=
  {c : Ambient n k // ∀ i, c (a i)=q i}

def reindexAmbient {n k} (σ : Equiv.Perm (Fin k)) (c : Ambient n k) : Ambient n k :=
  ⟨fun i => c (σ i),c.injective.comp σ.injective⟩

noncomputable def positionsPrefixEquiv {n r m} (a : Fin r ↪ Fin (r+m))
    (q : Ambient n r) : FixedPositions a q ≃ FixedPrefix m q := by
  have hex := Equiv.Perm.exists_extending_pair
    (Fin.castAdd m : Fin r → Fin (r+m)) a
    (Fin.castAdd_injective r m) a.injective
  let σ := Classical.choose hex
  have hσ := Classical.choose_spec hex
  exact {
    toFun := fun c => ⟨reindexAmbient σ c.val,by
      intro i
      change c.val (σ (Fin.castAdd m i))=q i
      rw [hσ]
      exact c.property i⟩
    invFun := fun c => ⟨reindexAmbient σ.symm c.val,by
      intro i
      change c.val (σ.symm (a i))=q i
      rw [← hσ,σ.symm_apply_apply]
      exact c.property i⟩
    left_inv := fun c => by
      apply Subtype.ext
      apply Function.Embedding.ext
      intro i
      change c.val (σ (σ.symm i))=c.val i
      rw [σ.apply_symm_apply]
    right_inv := fun c => by
      apply Subtype.ext
      apply Function.Embedding.ext
      intro i
      change c.val (σ.symm (σ i))=c.val i
      rw [σ.symm_apply_apply] }

theorem fixed_positions_card {n r m} (a : Fin r ↪ Fin (r+m)) (q : Ambient n r) :
    Nat.card (FixedPositions a q) = (n-r).descFactorial m := by
  rw [Nat.card_congr (positionsPrefixEquiv a q),fixed_prefix_card]
#print axioms fixed_positions_card
end Frustrated
```
<!-- LEAN-SOURCE-END FixedPositions -->

<!-- LEAN-SOURCE-BEGIN DisjointSlots SHA256 566cf5b13389328f90ce4d0c29345c5b72956901c06bb56c107f7ffa70cfa7e5 BYTES 2613 -->
```lean
import FixedPositions
namespace Frustrated
/-- Possible starts of an edge disjoint from positions 0 and 1, without wrap. -/
def disjointStart {m} (j : Fin (1+m)) : Fin (4+m) := ⟨j.val+2,by omega⟩
def disjointEnd {m} (j : Fin (1+m)) : Fin (4+m) := ⟨j.val+3,by omega⟩

theorem disjoint_next {m} (j : Fin (1+m)) :
    disjointStart j+1=disjointEnd j := by
  apply Fin.ext
  simp only [Fin.val_add,disjointStart,disjointEnd]
  norm_num [Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 1<4+m),
    Nat.mod_eq_of_lt (by omega : j.val+2+1<4+m)]

theorem disjoint_slots {n m} (c : Ambient n (4+m)) (q : Ambient n 4)
    (h₀ : c 0=q 0) (h₁ : c 1=q 1)
    (h : HasCyclePair c (q 2) (q 3)) :
    ∃ j : Fin (1+m),
      (c (disjointStart j)=q 2 ∧ c (disjointEnd j)=q 3) ∨
      (c (disjointStart j)=q 3 ∧ c (disjointEnd j)=q 2) := by
  obtain ⟨i,hi⟩ := h
  have hne (v : Fin (4+m)) (hv : c v=q 2 ∨ c v=q 3) :
      v ≠ 0 ∧ v ≠ 1 := by
    constructor
    · intro he
      subst v
      rcases hv with hv | hv
      · have he := q.injective (h₀.symm.trans hv)
        have := congrArg Fin.val he
        norm_num at this
      · have he := q.injective (h₀.symm.trans hv)
        have := congrArg Fin.val he
        norm_num at this
    · intro he
      subst v
      rcases hv with hv | hv
      · have he := q.injective (h₁.symm.trans hv)
        have := congrArg Fin.val he
        norm_num at this
      · have he := q.injective (h₁.symm.trans hv)
        have := congrArg Fin.val he
        norm_num at this
  have hev := Sym2.eq_iff.mp hi
  have hi' : c i=q 2 ∨ c i=q 3 := by rcases hev with h | h; exact Or.inl h.1; exact Or.inr h.1
  have hn' : c (i+1)=q 2 ∨ c (i+1)=q 3 := by rcases hev with h | h; exact Or.inr h.2; exact Or.inl h.2
  have hi0 := (hne i hi').1
  have hi1 := (hne i hi').2
  have hn0 := (hne (i+1) hn').1
  have hlow : 2 ≤ i.val := by
    have h0 : i.val ≠ 0 := by intro hh; exact hi0 (Fin.ext (by simpa using hh))
    have h1 : i.val ≠ 1 := by intro hh; exact hi1 (Fin.ext (by simpa [Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 1<4+m)] using hh))
    omega
  have hupp : i.val+1<4+m := by
    by_contra hh
    have he : i.val+1=4+m := by omega
    apply hn0
    apply Fin.ext
    simp only [Fin.val_add]
    norm_num [Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 1<4+m),he]
  let j : Fin (1+m) := ⟨i.val-2,by omega⟩
  have hs : disjointStart j=i := by apply Fin.ext; change i.val-2+2=i.val; omega
  have he : disjointEnd j=i+1 := by rw [← disjoint_next,hs]
  refine ⟨j,?_⟩
  rw [hs,he]
  exact hev
#print axioms disjoint_slots
end Frustrated
```
<!-- LEAN-SOURCE-END DisjointSlots -->

<!-- LEAN-SOURCE-BEGIN DisjointPositions SHA256 9bd4642491c1e495d8ab31293697657425f0b21a724628799ce7fbfe02015c9a BYTES 1087 -->
```lean
import DisjointSlots
namespace Frustrated
def disjointPositionFn {m} (b : Bool) (j : Fin (1+m)) (i : Fin 4) : Fin (4+m) :=
  if i=0 then 0 else if i=1 then 1 else
    if i=2 then (if b then disjointEnd j else disjointStart j)
    else (if b then disjointStart j else disjointEnd j)

theorem disjointPositionFn_injective {m} (b : Bool) (j : Fin (1+m)) :
    Function.Injective (disjointPositionFn b j) := by
  have hmod : 1 % (4+m)=1 := Nat.mod_eq_of_lt (by omega)
  intro i l h
  fin_cases i <;> fin_cases l <;> cases b <;>
    norm_num [disjointPositionFn] at h ⊢ <;> try omega
  all_goals
    have hv := congrArg Fin.val h
    norm_num [disjointStart,disjointEnd,Fin.val_ofNat,hmod] at hv

def disjointPositions {m} (b : Bool) (j : Fin (1+m)) : Fin 4 ↪ Fin (4+m) :=
  ⟨disjointPositionFn b j,disjointPositionFn_injective b j⟩

theorem disjoint_position_card {n m} (q : Ambient n 4)
    (b : Bool) (j : Fin (1+m)) :
    Nat.card (FixedPositions (disjointPositions b j) q) = (n-4).descFactorial m :=
  fixed_positions_card _ _
#print axioms disjoint_position_card
end Frustrated
```
<!-- LEAN-SOURCE-END DisjointPositions -->

<!-- LEAN-SOURCE-BEGIN DisjointCount SHA256 dff5795738b67355f95768c171bcabdc1a964231f6e09dcc41b2786f6fa9cd91 BYTES 7219 -->
```lean
import DisjointPositions
import Mathlib.Tactic.Ring
namespace Frustrated
abbrev DisjointRooted {n m} (q : Ambient n 4) :=
  {c : Ambient n (4+m) // c 0=q 0 ∧ c 1=q 1 ∧ HasCyclePair c (q 2) (q 3)}
abbrev DisjointData {n m} (q : Ambient n 4) :=
  (b : Bool) × (j : Fin (1+m)) × FixedPositions (disjointPositions b j) q

theorem disjoint_constraints {n m} (q : Ambient n 4) (b : Bool)
    (j : Fin (1+m)) (c : Ambient n (4+m)) :
    (∀ i, c (disjointPositions b j i)=q i) ↔
      c 0=q 0 ∧ c 1=q 1 ∧
        (if b then c (disjointEnd j)=q 2 ∧ c (disjointStart j)=q 3
        else c (disjointStart j)=q 2 ∧ c (disjointEnd j)=q 3) := by
  constructor
  · intro h
    have h₀ := h 0
    have h₁ := h 1
    have h₂ := h 2
    have h₃ := h 3
    cases b <;> simpa [disjointPositions,disjointPositionFn] using
      And.intro h₀ (And.intro h₁ (And.intro h₂ h₃))
  · intro h i
    cases b <;> fin_cases i
    all_goals simp only [Bool.false_eq_true,ite_false,ite_true] at h
    all_goals simp [disjointPositions,disjointPositionFn,h.1,h.2.1,h.2.2.1,h.2.2.2]

noncomputable def disjointForget {n m} (q : Ambient n 4)
    (p : DisjointData (m:=m) q) : DisjointRooted (m:=m) q := by
  obtain ⟨b,j,c⟩ := p
  have h := (disjoint_constraints q b j c.val).mp c.property
  refine ⟨c.val,h.1,h.2.1,disjointStart j,?_⟩
  rw [disjoint_next]
  cases b
  · simp only [Bool.false_eq_true,ite_false] at h
    rw [h.2.2.1,h.2.2.2]
  · simp only [ite_true] at h
    rw [h.2.2.1,h.2.2.2,Sym2.eq_swap]

theorem disjointForget_bijective {n m} (q : Ambient n 4) :
    Function.Bijective (disjointForget (m:=m) q) := by
  constructor
  · rintro ⟨b,j,c⟩ ⟨d,l,e⟩ hh
    have he : c.val=e.val := congrArg Subtype.val hh
    have h := (disjoint_constraints q b j c.val).mp c.property
    have h' := (disjoint_constraints q d l e.val).mp e.property
    have hj : cycleEdge c.val (disjointStart j)=s(q 2,q 3) := by
      change s(c.val (disjointStart j),c.val (nextIndex (disjointStart j)))=_
      unfold nextIndex
      rw [succ_as_add,disjoint_next]
      cases b <;> simp_all [Sym2.eq_swap]
    have hl : cycleEdge c.val (disjointStart l)=s(q 2,q 3) := by
      rw [he]
      change s(e.val (disjointStart l),e.val (nextIndex (disjointStart l)))=_
      unfold nextIndex
      rw [succ_as_add,disjoint_next]
      cases d <;> simp_all [Sym2.eq_swap]
    have hjl := cycleEdge_injective (by omega : 3 ≤ 4+m) c.val (hj.trans hl.symm)
    have hjl' : j=l := by
      apply Fin.ext
      have hv := congrArg Fin.val hjl
      change j.val+2=l.val+2 at hv
      omega
    subst l
    have hbd : b=d := by
      cases b <;> cases d <;> try rfl
      all_goals
        simp only [Bool.false_eq_true,ite_false,ite_true] at h h'
        have h23 : q 2=q 3 := by
          first
          | exact h.2.2.1.symm.trans ((congrArg (fun x : Ambient n (4+m) => x (disjointStart j)) he).trans h'.2.2.2)
          | exact h'.2.2.1.symm.trans ((congrArg (fun x : Ambient n (4+m) => x (disjointStart j)) he.symm).trans h.2.2.2)
        have hv := congrArg Fin.val (q.injective h23)
        norm_num at hv
    subst d
    have hce : c=e := Subtype.ext he
    subst e
    rfl
  · intro c
    obtain ⟨j,hj | hj⟩ := disjoint_slots c.val q c.property.1 c.property.2.1 c.property.2.2
    · let e : FixedPositions (disjointPositions false j) q :=
        ⟨c.val,(disjoint_constraints q false j c.val).mpr ⟨c.property.1,c.property.2.1,hj⟩⟩
      exact ⟨⟨false,j,e⟩,Subtype.ext rfl⟩
    · let e : FixedPositions (disjointPositions true j) q :=
        ⟨c.val,(disjoint_constraints q true j c.val).mpr ⟨c.property.1,c.property.2.1,hj.2,hj.1⟩⟩
      exact ⟨⟨true,j,e⟩,Subtype.ext rfl⟩
theorem disjoint_rooted_count {n m} (q : Ambient n 4) :
    Nat.card (DisjointRooted (m:=m) q) = 2*(1+m)*(n-4).descFactorial m := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (disjointForget_bijective (m:=m) q))]
  classical
  have hc (b : Bool) (j : Fin (1+m)) :
      Fintype.card (FixedPositions (disjointPositions b j) q) = (n-4).descFactorial m := by
    rw [← Nat.card_eq_fintype_card]
    exact disjoint_position_card q b j
  simp [DisjointData,hc,two_mul]
  ring

abbrev DisjointTuples {n m} (q : Ambient n 4) :=
  {c : Ambient n (4+m) // HasCyclePair c (q 0) (q 1) ∧ HasCyclePair c (q 2) (q 3)}

noncomputable def disjointPlacement {n m} (q : Ambient n 4)
    (p : (Bool × Fin (4+m)) × DisjointRooted (m:=m) q) : DisjointTuples (m:=m) q := by
  have h : HasCyclePair p.2.val (q 0) (q 1) := by
    refine ⟨0,?_⟩
    simp only [zero_add,p.2.property.1,p.2.property.2.1]
  let e := orbitMap p.2.val p.1
  exact ⟨e.val,pair_step _ _ e.property _ _ h,
    pair_step _ _ e.property _ _ p.2.property.2.2⟩

theorem disjointPlacement_bijective {n m} (q : Ambient n 4) :
    Function.Bijective (disjointPlacement (m:=m) q) := by
  constructor
  · rintro ⟨p,c⟩ ⟨r,d⟩ h
    have he : (orbitMap c.val p).val=(orbitMap d.val r).val := congrArg Subtype.val h
    have hc : dihedralStep c.val d.val :=
      step_trans (orbitMap c.val p).property
        (he ▸ step_symm (orbitMap d.val r).property)
    have hcd : c=d := Subtype.ext (two_point_orbit_unique (by omega) c.val d.val
      (d.property.1.trans c.property.1.symm)
      (d.property.2.1.trans c.property.2.1.symm) hc)
    subst d
    have hpr : p=r := (orbitMap_bijective (by omega) c.val).1 (Subtype.ext he)
    subst r
    rfl
  · intro c
    let q01 : Ambient n 2 :=
      ⟨fun i => q (Fin.castLE (by omega : 2≤4) i),q.injective.comp (Fin.castLE_injective (by omega : 2≤4))⟩
    have h01 : HasCyclePair c.val (q01 0) (q01 1) := by
      change HasCyclePair c.val (q 0) (q 1)
      exact c.property.1
    obtain ⟨d,hd,h₀,h₁⟩ := singleton_normalize c.val q01 h01
    have hd0 : d 0=q 0 := h₀
    have hd1 : d 1=q 1 := h₁
    let e : DisjointRooted (m:=m) q :=
      ⟨d,hd0,hd1,pair_step _ _ hd _ _ c.property.2⟩
    obtain ⟨p,hp⟩ := (orbitMap_bijective (by omega) d).2 ⟨c.val,step_symm hd⟩
    refine ⟨(p,e),?_⟩
    apply Subtype.ext
    change (orbitMap d p).val=c.val
    exact congrArg Subtype.val hp

theorem disjoint_tuple_count {n m} (q : Ambient n 4) :
    Nat.card (DisjointTuples (m:=m) q) = 4*(4+m)*(1+m)*(n-4).descFactorial m := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (disjointPlacement_bijective (m:=m) q))]
  rw [Nat.card_prod,Nat.card_prod,disjoint_rooted_count]
  simp only [Nat.card_eq_fintype_card,Fintype.card_bool,Fintype.card_fin]
  ring

theorem disjoint_completion_count {n m} (q : Ambient n 4) :
    Nat.card {c : Ambient n (4+m) //
      ({s(q 0,q 1),s(q 2,q 3)} : Finset (Sym2 (Fin n))) ⊆ cycleSupport c} =
      4*(4+m)*(1+m)*(n-4).descFactorial m := by
  classical
  have he : (fun c : Ambient n (4+m) =>
      ({s(q 0,q 1),s(q 2,q 3)} : Finset (Sym2 (Fin n))) ⊆ cycleSupport c) =
      (fun c => HasCyclePair c (q 0) (q 1) ∧ HasCyclePair c (q 2) (q 3)) := by
    funext c
    apply propext
    simp [support_definition_bridge,Finset.insert_subset_iff,pair_iff_support]
  change Nat.card (Subtype _) = _
  rw [he]
  exact disjoint_tuple_count q
#print axioms disjoint_completion_count
#print axioms disjointForget_bijective
end Frustrated
```
<!-- LEAN-SOURCE-END DisjointCount -->

<!-- LEAN-SOURCE-BEGIN VertexCompletions SHA256 a4746d9e4e43876eb16b63c84bf42992e27e352e7b5f1c521f031c582eccd391 BYTES 1918 -->
```lean
import DisjointCount
namespace Frustrated
abbrev ContainsVertices {n k r} (q : Ambient n r) :=
  {c : Ambient n k // ∀ i, ∃ j, c j=q i}
abbrev VertexPlacementData {n k r} (q : Ambient n r) :=
  (a : Fin r ↪ Fin k) × FixedPositions a q

def vertexPlacement {n k r} (q : Ambient n r) (p : VertexPlacementData (k:=k) q) :
    ContainsVertices (k:=k) q :=
  ⟨p.2.val,fun i => ⟨p.1 i,p.2.property i⟩⟩

theorem vertexPlacement_bijective {n k r} (q : Ambient n r) :
    Function.Bijective (vertexPlacement (k:=k) q) := by
  constructor
  · rintro ⟨a,c⟩ ⟨b,d⟩ h
    have he : c.val=d.val := congrArg Subtype.val h
    have hab : a=b := by
      apply Function.Embedding.ext
      intro i
      apply c.val.injective
      exact (c.property i).trans ((d.property i).symm.trans
        (congrArg (fun e : Ambient n k => e (b i)) he.symm))
    subst b
    have hcd : c=d := Subtype.ext he
    subst d
    rfl
  · intro c
    let a : Fin r ↪ Fin k := {
      toFun := fun i => Classical.choose (c.property i)
      inj' := by
        intro i j h
        apply q.injective
        exact (Classical.choose_spec (c.property i)).symm.trans
          ((congrArg c.val h).trans (Classical.choose_spec (c.property j))) }
    let e : FixedPositions a q := ⟨c.val,fun i => Classical.choose_spec (c.property i)⟩
    exact ⟨⟨a,e⟩,Subtype.ext rfl⟩

theorem vertex_completion_count {n r m} (q : Ambient n r) :
    Nat.card (ContainsVertices (k:=r+m) q) =
      (r+m).descFactorial r * (n-r).descFactorial m := by
  classical
  rw [← Nat.card_congr (Equiv.ofBijective _ (vertexPlacement_bijective (k:=r+m) q))]
  have hc (a : Fin r ↪ Fin (r+m)) :
      Fintype.card (FixedPositions a q) = (n-r).descFactorial m := by
    rw [← Nat.card_eq_fintype_card]
    exact fixed_positions_card a q
  simp [VertexPlacementData,hc,Fintype.card_embedding_eq]
#print axioms vertex_completion_count
end Frustrated
```
<!-- LEAN-SOURCE-END VertexCompletions -->

<!-- LEAN-SOURCE-BEGIN UniformFactorials SHA256 64784a90a670e8c8a5e232d6fa6f59a860170ca5e9bde0969cc9e4d2405afe6d BYTES 2036 -->
```lean
import VertexCompletions
namespace Frustrated
/-- Uniform for every n above the displayed threshold, with no asymptotic oracle. -/
theorem falling_uniform_lower (a m n : Nat) (hn : 2*(a+m) ≤ n) :
    n^m ≤ 2^m * (n-a).descFactorial m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hi := ih (by omega : 2*(a+m) ≤ n)
    have hf : n ≤ 2*(n-a-m) := by omega
    calc
      n^(m+1) = n^m*n := by rw [pow_succ]
      _ ≤ (2^m*(n-a).descFactorial m)*(2*(n-a-m)) := Nat.mul_le_mul hi hf
      _ = 2^(m+1)*(n-a).descFactorial (m+1) := by
        rw [pow_succ,Nat.descFactorial_succ]
        ring

theorem falling_eventual_positive (a m n : Nat) (hn : a+m ≤ n) :
    0 < (n-a).descFactorial m := by
  rw [Nat.descFactorial_pos]
  omega

theorem vertex_completion_uniform_bound {n r m} (q : Ambient n r) :
    Nat.card (ContainsVertices (k:=r+m) q) ≤ (r+m)^r*n^m := by
  rw [vertex_completion_count]
  apply Nat.mul_le_mul (Nat.descFactorial_le_pow _ _)
  exact (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)

theorem total_cycle_uniform_lower {n k} (hk : 3 ≤ k) (hn : 2*k ≤ n) :
    n^k ≤ (2^k*(2*k))*totalCycleCount n k := by
  have h := falling_uniform_lower 0 k n (by simpa using hn)
  have hc := total_cycle_scale (n:=n) hk
  rw [Nat.card_eq_fintype_card,Fintype.card_embedding_eq] at hc
  simp only [Fintype.card_fin] at hc
  simpa only [Nat.sub_zero,hc,Nat.mul_assoc] using h

theorem total_cycle_dominates_sparse {n k D} (hk : 3 ≤ k)
    (hn : 2*k ≤ n) (hD : (2^k*(2*k))*D < n^2) :
    D*n^(k-2) < totalCycleCount n k := by
  have hp : 0<n^(k-2) := Nat.pow_pos (by omega)
  have hmul := Nat.mul_lt_mul_of_pos_right hD hp
  have hexp : n^2*n^(k-2)=n^k := by
    rw [← pow_add]
    congr 1
    omega
  rw [hexp] at hmul
  have hlow := total_cycle_uniform_lower hk hn
  have hfac : 0 < 2^k*(2*k) := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  nlinarith
#print axioms vertex_completion_uniform_bound
#print axioms total_cycle_dominates_sparse
end Frustrated
```
<!-- LEAN-SOURCE-END UniformFactorials -->

<!-- LEAN-SOURCE-BEGIN TriangleExclusion SHA256 11941ba7eab3bbdc5fc2b32fb33707fcc27975b3ada9f097109c90b3206fae9e BYTES 2038 -->
```lean
import UniformFactorials
namespace Frustrated
/-- A proper triangle cannot be an edge subset of a longer simple cycle. -/
theorem triangle_not_in_cycle {n k} [NeZero k] (hk : 4 ≤ k)
    (q : Ambient n 3) (c : Ambient n k)
    (h₀₁ : HasCyclePair c (q 0) (q 1))
    (h₁₂ : HasCyclePair c (q 1) (q 2)) :
    ¬ HasCyclePair c (q 2) (q 0) := by
  intro h₂₀
  obtain ⟨d,hd,h₀,h₁,h₂⟩ := adjacent_normalize (by omega) c q h₀₁ h₁₂
  have h := pair_step c d hd (q 2) (q 0) h₂₀
  obtain ⟨x,y,hx,hy,hxy⟩ := pair_positions d (q 2) (q 0) h
  have hx' : x=2 := d.injective (hx.trans h₂.symm)
  have hy' : y=0 := d.injective (hy.trans h₀.symm)
  rw [hx',hy'] at hxy
  rcases hxy with hxy | hxy
  · have hv := congrArg Fin.val hxy
    norm_num [Fin.val_add,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 1<k),
      Nat.mod_eq_of_lt (by omega : 2<k),Nat.mod_eq_of_lt (by omega : 3<k)] at hv
  · have hv := congrArg Fin.val hxy
    norm_num [Fin.val_add,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 1<k),
      Nat.mod_eq_of_lt (by omega : 2<k)] at hv

theorem triangle_completion_zero {n m} (q : Ambient n 3) :
    Nat.card {c : Ambient n (4+m) //
      ({s(q 0,q 1),s(q 1,q 2),s(q 2,q 0)} : Finset (Sym2 (Fin n))) ⊆ cycleSupport c} = 0 := by
  classical
  have he : IsEmpty {c : Ambient n (4+m) //
      ({s(q 0,q 1),s(q 1,q 2),s(q 2,q 0)} : Finset (Sym2 (Fin n))) ⊆ cycleSupport c} := by
    constructor
    rintro ⟨c,hc⟩
    have h₀₁ := hc (by simp : s(q 0,q 1) ∈ ({s(q 0,q 1),s(q 1,q 2),s(q 2,q 0)} : Finset (Sym2 (Fin n))))
    have h₁₂ := hc (by simp : s(q 1,q 2) ∈ ({s(q 0,q 1),s(q 1,q 2),s(q 2,q 0)} : Finset (Sym2 (Fin n))))
    have h₂₀ := hc (by simp : s(q 2,q 0) ∈ ({s(q 0,q 1),s(q 1,q 2),s(q 2,q 0)} : Finset (Sym2 (Fin n))))
    rw [support_definition_bridge,← pair_iff_support] at h₀₁ h₁₂ h₂₀
    exact triangle_not_in_cycle (by omega) q c h₀₁ h₁₂ h₂₀
  let := he
  exact Nat.card_of_isEmpty
#print axioms triangle_completion_zero
end Frustrated
```
<!-- LEAN-SOURCE-END TriangleExclusion -->

<!-- LEAN-SOURCE-BEGIN SupportEventBound SHA256 02c7802752139a899b12e1df3dccdc2f6d02d80c0faf389aa8918d885b0cb4f8 BYTES 1179 -->
```lean
import TriangleExclusion
namespace Frustrated

theorem cycle_support_vertex {n k} (c : Ambient n k) (e : Sym2 (Fin n))
    (he : e ∈ cycleSupport c) (v : Fin n) (hv : v ∈ e) :
    ∃ j, c j=v := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp he
  rw [← hi] at hv
  change v ∈ s(c i,c (nextIndex i)) at hv
  rcases Sym2.mem_iff.mp hv with hv | hv
  · exact ⟨i,hv.symm⟩
  · exact ⟨nextIndex i,hv.symm⟩

theorem four_vertex_completion_bound {n m} (F : Finset (Sym2 (Fin n)))
    (q : Ambient n 4) (hq : ∀ i, ∃ e ∈ F, q i ∈ e) :
    Nat.card {c : Ambient n (4+m) // F ⊆ cycleSupport c} ≤
      (4+m)^4*n^m := by
  let f : {c : Ambient n (4+m) // F ⊆ cycleSupport c} →
      ContainsVertices (k:=4+m) q := fun c => ⟨c.val,by
        intro i
        obtain ⟨e,he,hv⟩ := hq i
        exact cycle_support_vertex c.val e (c.property he) (q i) hv⟩
  have hf : Function.Injective f := by
    intro c d h
    have hh : (f c).val=(f d).val := congrArg Subtype.val h
    exact Subtype.ext hh
  exact (Nat.card_le_card_of_injective f hf).trans (vertex_completion_uniform_bound q)
#print axioms four_vertex_completion_bound
end Frustrated
```
<!-- LEAN-SOURCE-END SupportEventBound -->

<!-- LEAN-SOURCE-BEGIN EdgeClassification SHA256 f99089065143d109d628aff513c023ad36cd40e6c4ca4c1251f87044564ba8de BYTES 3620 -->
```lean
import SupportEventBound
namespace Frustrated
def EdgeMeets {V : Type} (e f : Sym2 V) : Prop := ∃ v, v ∈ e ∧ v ∈ f

theorem meets_pair_iff {V : Type} (e : Sym2 V) (a b : V) :
    EdgeMeets e s(a,b) ↔ a ∈ e ∨ b ∈ e := by
  constructor
  · rintro ⟨v,hv,hab⟩
    rcases Sym2.mem_iff.mp hab with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr hv
  · rintro (h | h)
    · exact ⟨a,h,Sym2.mem_mk_left _ _⟩
    · exact ⟨b,h,Sym2.mem_mk_right _ _⟩

theorem meets_triangle_edges {V : Type} [DecidableEq V] (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (e : Sym2 V)
    (h₁ : a ∈ e ∨ b ∈ e) (h₂ : a ∈ e ∨ c ∈ e)
    (h₃ : b ∈ e ∨ c ∈ e) :
    e ∈ ({s(a,b),s(a,c),s(b,c)} : Finset (Sym2 V)) := by
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp only [Sym2.mem_iff] at h₁ h₂ h₃
    rcases h₁ with (h₁ | h₁) | (h₁ | h₁) <;>
      rcases h₂ with (h₂ | h₂) | (h₂ | h₂) <;>
      rcases h₃ with (h₃ | h₃) | (h₃ | h₃) <;>
      simp_all [Sym2.eq_swap]

theorem intersecting_edges_star_or_triangle {V : Type} [DecidableEq V]
    (E : Finset (Sym2 V)) (a b c : V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h₁ : s(a,b) ∈ E) (h₂ : s(a,c) ∈ E)
    (hE : ∀ e ∈ E, ∀ f ∈ E, EdgeMeets e f) :
    (∀ e ∈ E, a ∈ e) ∨ E = {s(a,b),s(a,c),s(b,c)} := by
  by_cases ha : ∀ e ∈ E, a ∈ e
  · exact Or.inl ha
  · right
    push Not at ha
    obtain ⟨e,he,hae⟩ := ha
    have hb : b ∈ e := ((meets_pair_iff e a b).mp (hE e he _ h₁)).resolve_left hae
    have hc : c ∈ e := ((meets_pair_iff e a c).mp (hE e he _ h₂)).resolve_left hae
    have heq : e=s(b,c) := (Sym2.mem_and_mem_iff hbc).mp ⟨hb,hc⟩
    have h₃ : s(b,c) ∈ E := heq ▸ he
    apply Finset.Subset.antisymm
    · intro f hf
      exact meets_triangle_edges a b c hab hac hbc f
        ((meets_pair_iff f a b).mp (hE f hf _ h₁))
        ((meets_pair_iff f a c).mp (hE f hf _ h₂))
        ((meets_pair_iff f b c).mp (hE f hf _ h₃))
    · intro f hf
      simp only [Finset.mem_insert,Finset.mem_singleton] at hf
      rcases hf with rfl | rfl | rfl
      · exact h₁
      · exact h₂
      · exact h₃
theorem pairwise_intersecting_classification {V : Type} [DecidableEq V]
    (E : Finset (Sym2 V)) (hne : E.Nonempty)
    (hloop : ∀ a, s(a,a) ∉ E)
    (hE : ∀ e ∈ E, ∀ f ∈ E, EdgeMeets e f) :
    (∃ a, ∀ e ∈ E, a ∈ e) ∨
      ∃ a b c, a≠b ∧ a≠c ∧ b≠c ∧ E={s(a,b),s(a,c),s(b,c)} := by
  by_cases hcard : E.card ≤ 1
  · obtain ⟨e,he⟩ := hne
    have rep : ∃ a b, e=s(a,b) := by
      induction e using Sym2.inductionOn with
      | _ a b => exact ⟨a,b,rfl⟩
    obtain ⟨a,b,rfl⟩ := rep
    left
    refine ⟨a,?_⟩
    intro f hf
    rw [(Finset.card_le_one.mp hcard) f hf _ he]
    exact Sym2.mem_mk_left _ _
  · obtain ⟨e,he,f,hf,hef⟩ := Finset.one_lt_card.mp (by omega : 1<E.card)
    obtain ⟨a,hae,haf⟩ := hE e he f hf
    obtain ⟨b,hb⟩ := Sym2.mem_iff_exists.mp hae
    obtain ⟨c,hc⟩ := Sym2.mem_iff_exists.mp haf
    subst e
    subst f
    have hab : a≠b := by intro hh; subst b; exact hloop a he
    have hac : a≠c := by intro hh; subst c; exact hloop a hf
    have hbc : b≠c := by intro hh; subst c; exact hef rfl
    rcases intersecting_edges_star_or_triangle E a b c hab hac hbc he hf hE with h | h
    · exact Or.inl ⟨a,h⟩
    · exact Or.inr ⟨a,b,c,hab,hac,hbc,h⟩
#print axioms pairwise_intersecting_classification
#print axioms intersecting_edges_star_or_triangle
end Frustrated
```
<!-- LEAN-SOURCE-END EdgeClassification -->

<!-- LEAN-SOURCE-BEGIN SparseUpper SHA256 9aec4d01fc2c6b6b69e5254eba7d5a00e1ea820f295de87285dc2fd70e4e0f3d BYTES 2996 -->
```lean
import EdgeClassification
namespace Frustrated

theorem graph_edge_completion_count {n k} (hk : 3 ≤ k) (G : Graph (Fin n))
    (e : Sym2 (Fin n)) (he : e ∈ graphEdges G) :
    Nat.card {c : Ambient n k // e ∈ cycleSupport c} =
      2*k*(n-2).descFactorial (k-2) := by
  classical
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hab : a ≠ b := by
      intro h
      subst b
      have hh := (Finset.mem_filter.mp he).2
      change G.edge a a=true at hh
      rw [G.loopless] at hh
      cases hh
    let q : Ambient n 2 := {
      toFun := fun i => if i=0 then a else b
      inj' := by
        intro i j h
        fin_cases i <;> fin_cases j <;> simp_all }
    have hq0 : q 0=a := by change (if (0:Fin 2)=0 then a else b)=a; simp
    have hq1 : q 1=b := by change (if (1:Fin 2)=0 then a else b)=b; norm_num
    have hcount := singleton_completion_count (n:=n) (m:=k-2) (by omega) q
    have hlen : 2+(k-2)=k := by omega
    rw [hlen,hq0,hq1] at hcount
    exact hcount

noncomputable def oddEdgeWitness {n k} (hk : 3 ≤ k) (G : Graph (Fin n))
    (c : OddTuple n k G) :
    (e : {e // e ∈ graphEdges G}) × {d : Ambient n k // e.val ∈ cycleSupport d} := by
  classical
  have hp := (tupleOdd_edge_subset hk G c.val).mp c.property
  have hpos : 0<(graphEdges G ∩ cycleSupport c.val).card := by omega
  let e := Classical.choose (Finset.card_pos.mp hpos)
  have he := Finset.mem_inter.mp (Classical.choose_spec (Finset.card_pos.mp hpos))
  exact ⟨⟨e,he.1⟩,⟨c.val,he.2⟩⟩

theorem oddEdgeWitness_injective {n k} (hk : 3 ≤ k) (G : Graph (Fin n)) :
    Function.Injective (oddEdgeWitness hk G) := by
  intro c d h
  have hh := congrArg (fun p : (e : {e // e ∈ graphEdges G}) ×
    {d : Ambient n k // e.val ∈ cycleSupport d} => p.2.val) h
  exact Subtype.ext hh

theorem sparse_cycle_upper {n k} (hk : 3 ≤ k) (G : Graph (Fin n)) :
    cycleCount n k G ≤ (graphEdges G).card*n^(k-2) := by
  classical
  have h := Nat.card_le_card_of_injective _ (oddEdgeWitness_injective hk G)
  rw [Nat.card_sigma] at h
  have hs (a : {e // e ∈ graphEdges G}) :
      Nat.card {d : Ambient n k // a.val ∈ cycleSupport d} =
        2*k*(n-2).descFactorial (k-2) := graph_edge_completion_count hk G a.val a.property
  simp_rw [hs] at h
  rw [← tupleCount_card,tuple_cycle_scale hk] at h
  have hu := Nat.descFactorial_le_pow (n-2) (k-2)
  have hp := Nat.pow_le_pow_left (Nat.sub_le n 2) (k-2)
  have hn : (n-2).descFactorial (k-2) ≤ n^(k-2) := hu.trans hp
  simp only [Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul] at h
  have hc : Fintype.card {e // e ∈ graphEdges G} = (graphEdges G).card := Fintype.card_coe _
  rw [hc] at h
  have hh : (2*k)*cycleCount n k G ≤ (2*k)*
      ((graphEdges G).card*(n-2).descFactorial (k-2)) := by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm] using h
  have hcan := Nat.le_of_mul_le_mul_left hh (by omega : 0<2*k)
  exact hcan.trans (Nat.mul_le_mul_left _ hn)
#print axioms sparse_cycle_upper
end Frustrated
```
<!-- LEAN-SOURCE-END SparseUpper -->

<!-- LEAN-SOURCE-BEGIN OddExclusion SHA256 dfb93e834d9fc6aa77ecefe3a9ea6f1ad9b672304853213c2722cb544c7a9d47 BYTES 1520 -->
```lean
import SparseUpper
namespace Frustrated
/-- The odd-complement obstruction uses the total AMBIENT cycle lower bound. -/
theorem odd_complement_sparse_exclusion {n k M s} (hk : 3 ≤ k)
    (ho : k%2 ≠ 0) (hn : 2*k ≤ n)
    (hlarge : (2^k*(2*k))*(M+s) < n^2)
    (G : Graph (Fin n)) (hM : (graphEdges (complement G)).card ≤ M)
    (hthreshold : cycleCount n k G < cycleCount n k (star n s)) : False := by
  have hG : cycleCount n k G < s*n^(k-2) :=
    hthreshold.trans_le (star_cycle_upper hk)
  have hE : cycleCount n k (complement G) ≤ M*n^(k-2) :=
    (sparse_cycle_upper hk (complement G)).trans (Nat.mul_le_mul_right _ hM)
  have hsum := complement_odd_cycleCount hk ho G
  have htotal := total_cycle_dominates_sparse hk hn hlarge
  nlinarith

/-- A single explicit sufficient order threshold, independent of the graph. -/
theorem odd_complement_eventual_exclusion {k M s} (hk : 3 ≤ k) :
    ∃ N, ∀ n, N ≤ n → ∀ G : Graph (Fin n), k%2 ≠ 0 →
      (graphEdges (complement G)).card ≤ M →
      cycleCount n k G < cycleCount n k (star n s) → False := by
  let N := max (2*k) ((2^k*(2*k))*(M+s)+1)
  refine ⟨N,?_⟩
  intro n hn G ho hM hthreshold
  have hkn : 2*k ≤ n := le_trans (le_max_left _ _) hn
  have hdn : (2^k*(2*k))*(M+s)+1 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : 0<n := by omega
  have hn2 : n ≤ n^2 := by nlinarith
  exact odd_complement_sparse_exclusion hk ho hkn (by omega) G hM hthreshold
#print axioms odd_complement_eventual_exclusion
end Frustrated
```
<!-- LEAN-SOURCE-END OddExclusion -->

<!-- LEAN-SOURCE-BEGIN EventualDominance SHA256 035725833e320841515169c3ee73140ca9a7c91120d9701c2b2fed190c1e7d78 BYTES 1079 -->
```lean
import OddExclusion
namespace Frustrated
/-- Explicit all-n domination of a lower-degree monomial by a falling factorial. -/
theorem falling_dominates_lower_power (a m C n : Nat)
    (hn : 2*(a+(m+1)) ≤ n) (hC : C*2^(m+1) < n) :
    C*n^m < (n-a).descFactorial (m+1) := by
  have hlow := falling_uniform_lower a (m+1) n hn
  have hp : 0<n^m := Nat.pow_pos (by omega)
  have hmul : 2^(m+1)*(C*n^m) < 2^(m+1)*(n-a).descFactorial (m+1) := by
    calc
      _ = (C*2^(m+1))*n^m := by ring
      _ < n*n^m := Nat.mul_lt_mul_of_pos_right hC hp
      _ = n^(m+1) := by rw [pow_succ]; ring
      _ ≤ _ := hlow
  exact Nat.lt_of_mul_lt_mul_left hmul

theorem falling_eventual_dominance (a m C : Nat) :
    ∃ N, ∀ n, N ≤ n → C*n^m < (n-a).descFactorial (m+1) := by
  refine ⟨max (2*(a+(m+1))) (C*2^(m+1)+1),?_⟩
  intro n hn
  have h₁ : 2*(a+(m+1)) ≤ n := le_trans (le_max_left _ _) hn
  have h₂ : C*2^(m+1)+1 ≤ n := le_trans (le_max_right _ _) hn
  exact falling_dominates_lower_power a m C n h₁ (by omega)
#print axioms falling_eventual_dominance
end Frustrated
```
<!-- LEAN-SOURCE-END EventualDominance -->

<!-- LEAN-SOURCE-BEGIN CycleDegreeBound SHA256 5ab1ec8e8626d35df8122d7e8317c09d873e4e97b1f719f4ccf9c5f05bfab1ce BYTES 1472 -->
```lean
import EventualDominance
namespace Frustrated

theorem support_incident_at {n k} [NeZero k] (c : Ambient n k) (i : Fin k)
    (e : Sym2 (Fin n)) (he : e ∈ cycleSupport c) (hv : c i ∈ e) :
    e ∈ ({cycleEdge c i,cycleEdge c (i-1)} : Finset (Sym2 (Fin n))) := by
  classical
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp he
  rw [← hj] at hv ⊢
  change c i ∈ s(c j,c (nextIndex j)) at hv
  rcases Sym2.mem_iff.mp hv with hv | hv
  · have hij := c.injective hv
    subst j
    simp
  · have hij := c.injective hv
    unfold nextIndex at hij
    rw [succ_as_add] at hij
    have hji : j=i-1 := by rw [hij]; abel
    subst j
    simp

theorem cycle_incident_card_le_two {n k} [NeZero k] (c : Ambient n k) (v : Fin n) :
    ((cycleSupport c).filter (fun e => v ∈ e)).card ≤ 2 := by
  classical
  by_cases hv : ∃ i, c i=v
  · obtain ⟨i,rfl⟩ := hv
    have hs : (cycleSupport c).filter (fun e => c i ∈ e) ⊆
        {cycleEdge c i,cycleEdge c (i-1)} := by
      intro e he
      have hh := Finset.mem_filter.mp he
      exact support_incident_at c i e hh.1 hh.2
    exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _ |>.trans (by simp))
  · have he : (cycleSupport c).filter (fun e => v ∈ e) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hh := Finset.mem_filter.mp he
      exact hv (cycle_support_vertex c e hh.1 v hh.2)
    simp [he]
#print axioms cycle_incident_card_le_two
end Frustrated
```
<!-- LEAN-SOURCE-END CycleDegreeBound -->

<!-- LEAN-SOURCE-BEGIN HigherSupport SHA256 5115f3696eafb060f13cb1591213dd8142a4b4a105ea59db163d22db308b6cc5 BYTES 4131 -->
```lean
import CycleDegreeBound
import Mathlib.Tactic.FinCases
namespace Frustrated

theorem support_loopless {n k} (hk : 3 ≤ k) (c : Ambient n k) (a : Fin n) :
    s(a,a) ∉ cycleSupport c := by
  classical
  intro h
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
  change s(c i,c (nextIndex i)) = s(a,a) at hi
  rcases Sym2.eq_iff.mp hi with h | h
  · exact nextIndex_ne hk i (c.injective (h.1.trans h.2.symm))
  · exact nextIndex_ne hk i (c.injective (h.1.trans h.2.symm))

theorem higher_support_has_disjoint {n m} (F : Finset (Sym2 (Fin n)))
    (hcard : 3 ≤ F.card) (c : Ambient n (4+m)) (hF : F ⊆ cycleSupport c) :
    ∃ e ∈ F, ∃ f ∈ F, ¬ EdgeMeets e f := by
  classical
  by_contra! h
  have hloop : ∀ a, s(a,a) ∉ F := fun a ha => support_loopless (by omega) c a (hF ha)
  rcases pairwise_intersecting_classification F (Finset.card_pos.mp (by omega)) hloop h with hs | ht
  · obtain ⟨a,ha⟩ := hs
    have sub : F ⊆ (cycleSupport c).filter (fun e => a ∈ e) := by
      intro e he
      exact Finset.mem_filter.mpr ⟨hF he,ha e he⟩
    have hh := (Finset.card_le_card sub).trans (cycle_incident_card_le_two c a)
    omega
  · obtain ⟨a,b,d,hab,had,hbd,hEq⟩ := ht
    let q : Ambient n 3 := ⟨![a,b,d],by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
    have hzero := triangle_completion_zero (m:=m) q
    have hsub : ({s(q 0,q 1),s(q 1,q 2),s(q 2,q 0)} : Finset (Sym2 (Fin n))) ⊆ cycleSupport c := by
      intro e he
      apply hF
      rw [hEq]
      change e ∈ ({s(a,b),s(b,d),s(d,a)} : Finset (Sym2 (Fin n))) at he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he ⊢
      rcases he with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl Sym2.eq_swap)
    have hpos : 0 < Nat.card {c : Ambient n (4+m) //
        ({s(q 0,q 1),s(q 1,q 2),s(q 2,q 0)} : Finset (Sym2 (Fin n))) ⊆ cycleSupport c} :=
      Nat.card_pos_iff.mpr ⟨⟨⟨c,hsub⟩⟩,inferInstance⟩
    omega

theorem disjoint_incident_four {n} (F : Finset (Sym2 (Fin n)))
    (hloop : ∀ a, s(a,a) ∉ F)
    (hdis : ∃ e ∈ F, ∃ f ∈ F, ¬ EdgeMeets e f) :
    ∃ q : Ambient n 4, ∀ i, ∃ e ∈ F, q i ∈ e := by
  classical
  obtain ⟨e,he,f,hf,hd⟩ := hdis
  induction e using Sym2.inductionOn with
  | _ a b =>
    induction f using Sym2.inductionOn with
    | _ c d =>
      have hab : a ≠ b := by intro h; subst b; exact hloop a he
      have hcd : c ≠ d := by intro h; subst d; exact hloop c hf
      have hac : a ≠ c := by intro h; subst c; exact hd ⟨a,by simp,by simp⟩
      have had : a ≠ d := by intro h; subst d; exact hd ⟨a,by simp,by simp⟩
      have hbc : b ≠ c := by intro h; subst c; exact hd ⟨b,by simp,by simp⟩
      have hbd : b ≠ d := by intro h; subst d; exact hd ⟨b,by simp,by simp⟩
      let q : Ambient n 4 := ⟨![a,b,c,d],by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all⟩
      refine ⟨q,?_⟩
      intro i
      fin_cases i
      · exact ⟨_,he,by change a ∈ s(a,b); simp⟩
      · exact ⟨_,he,by change b ∈ s(a,b); simp⟩
      · exact ⟨_,hf,by change c ∈ s(c,d); simp⟩
      · exact ⟨_,hf,by change d ∈ s(c,d); simp⟩

theorem bad_support_completion_bound {n m} (F : Finset (Sym2 (Fin n)))
    (hbad : 3 ≤ F.card ∨ ∃ e ∈ F, ∃ f ∈ F, ¬ EdgeMeets e f) :
    tupleCompletions (k:=4+m) F ≤ (4+m)^4*n^m := by
  classical
  by_cases hz : tupleCompletions (k:=4+m) F = 0
  · rw [hz]; exact Nat.zero_le _
  have hp : 0 < Nat.card {c : Ambient n (4+m) // F ⊆ cycleSupport c} := Nat.pos_of_ne_zero hz
  obtain ⟨c,hc⟩ := (Nat.card_pos_iff.mp hp).1
  have hd : ∃ e ∈ F, ∃ f ∈ F, ¬ EdgeMeets e f := by
    rcases hbad with h | h
    · exact higher_support_has_disjoint F h c hc
    · exact h
  have hl : ∀ a, s(a,a) ∉ F := fun a ha => support_loopless (by omega) c a (hc ha)
  obtain ⟨q,hq⟩ := disjoint_incident_four F hl hd
  exact four_vertex_completion_bound F q hq
#print axioms higher_support_has_disjoint
#print axioms bad_support_completion_bound
end Frustrated
```
<!-- LEAN-SOURCE-END HigherSupport -->

<!-- LEAN-SOURCE-BEGIN FullRemainder SHA256 14ec54d2b2d669c4262af190a9aa536de20341424124c7dff87abaa2a5ce3b92 BYTES 2518 -->
```lean
import HigherSupport
import Mathlib.Algebra.Order.Ring.Abs
namespace Frustrated
noncomputable def badSupports {n} (E : Finset (Sym2 (Fin n))) : Finset (Finset (Sym2 (Fin n))) := by
  classical
  exact E.powerset.filter (fun F => 3 ≤ F.card ∨ ∃ e ∈ F, ∃ f ∈ F, ¬ EdgeMeets e f)

noncomputable def signedRemainder {n k : Nat} (E : Finset (Sym2 (Fin n))) : Int :=
  ∑ F ∈ badSupports E, (-2 : Int)^(F.card-1) * (tupleCompletions (k:=k) F : Int)

theorem unsigned_remainder_bound {n m M} (E : Finset (Sym2 (Fin n))) (hM : E.card ≤ M) :
    (∑ F ∈ badSupports E, 2^(F.card-1) * tupleCompletions (k:=4+m) F) ≤
      2^(2*M)*(4+m)^4*n^m := by
  classical
  have hc : (badSupports E).card ≤ 2^M := by
    have hs : badSupports E ⊆ E.powerset := Finset.filter_subset _ _
    calc
      (badSupports E).card ≤ E.powerset.card := Finset.card_le_card hs
      _ = 2^E.card := Finset.card_powerset E
      _ ≤ 2^M := Nat.pow_le_pow_right (by decide) hM
  have ht : ∀ F ∈ badSupports E,
      2^(F.card-1)*tupleCompletions (k:=4+m) F ≤ 2^M*((4+m)^4*n^m) := by
    intro F hF
    have hf := Finset.mem_filter.mp hF
    have hsub : F ⊆ E := Finset.mem_powerset.mp hf.1
    have hcard := Finset.card_le_card hsub
    have hp : 2^(F.card-1) ≤ 2^M := Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.mul_le_mul hp (bad_support_completion_bound F hf.2)
  calc
    _ ≤ ∑ F ∈ badSupports E, 2^M*((4+m)^4*n^m) := Finset.sum_le_sum ht
    _ = (badSupports E).card * (2^M*((4+m)^4*n^m)) := by simp
    _ ≤ 2^M * (2^M*((4+m)^4*n^m)) := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [two_mul,pow_add]; ring

theorem full_signed_remainder_bound {n m M} (E : Finset (Sym2 (Fin n))) (hM : E.card ≤ M) :
    |signedRemainder (k:=4+m) E| ≤ (2^(2*M)*(4+m)^4*n^m : Nat) := by
  classical
  have ha (F : Finset (Sym2 (Fin n))) :
      |(-2 : Int)^(F.card-1) * (tupleCompletions (k:=4+m) F : Int)| =
        ((2^(F.card-1) * tupleCompletions (k:=4+m) F : Nat) : Int) := by
    simp [abs_mul,abs_pow,Nat.cast_mul,Nat.cast_pow]
  calc
    |signedRemainder (k:=4+m) E| ≤
        ∑ F ∈ badSupports E, |(-2 : Int)^(F.card-1)*(tupleCompletions (k:=4+m) F : Int)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ((∑ F ∈ badSupports E, 2^(F.card-1)*tupleCompletions (k:=4+m) F : Nat) : Int) := by
      simp only [ha,Nat.cast_sum]
    _ ≤ _ := by exact_mod_cast unsigned_remainder_bound E hM
#print axioms unsigned_remainder_bound
#print axioms full_signed_remainder_bound
end Frustrated
```
<!-- LEAN-SOURCE-END FullRemainder -->

<!-- LEAN-SOURCE-BEGIN StarSupport SHA256 e409b2901ebf2420e7709e937114db408fac883adce30e0a3c7cb2bb7bf721ef BYTES 1861 -->
```lean
import CycleDegreeBound
namespace Frustrated

theorem star_edge_zero {n s} [NeZero n] (e : Sym2 (Fin n))
    (he : e ∈ graphEdges (star n s)) : (0 : Fin n) ∈ e := by
  classical
  induction e using Sym2.inductionOn with
  | _ a b =>
    have h := (Finset.mem_filter.mp he).2
    change decide ((a.val=0 ∧ 1≤b.val ∧ b.val≤s) ∨
      (b.val=0 ∧ 1≤a.val ∧ a.val≤s))=true at h
    have hh := of_decide_eq_true h
    rw [Sym2.mem_iff]
    rcases hh with hh | hh
    · left
      apply Fin.ext
      simpa using hh.1.symm
    · right
      apply Fin.ext
      simpa using hh.1.symm

theorem star_cycle_support_card {n k s} [NeZero k] [NeZero n]
    (c : Ambient n k) : (graphEdges (star n s) ∩ cycleSupport c).card ≤ 2 := by
  classical
  have hs : graphEdges (star n s) ∩ cycleSupport c ⊆
      (cycleSupport c).filter (fun e => (0:Fin n) ∈ e) := by
    intro e he
    have hh := Finset.mem_inter.mp he
    exact Finset.mem_filter.mpr ⟨hh.2,star_edge_zero e hh.1⟩
  exact (Finset.card_le_card hs).trans (cycle_incident_card_le_two c 0)

theorem star_higher_completion_zero {n k s} (hk : 3≤k)
    (F : Finset (Sym2 (Fin n))) (hF : F ⊆ graphEdges (star n s)) (hcard : 3≤F.card) :
    tupleCompletions (k:=k) F=0 := by
  classical
  have he : IsEmpty {c : Ambient n k // F ⊆ cycleSupport c} := by
    constructor
    rintro ⟨c,hc⟩
    have hkn : k≤n := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective c c.injective
    let : NeZero n := ⟨by omega⟩
    let : NeZero k := ⟨by omega⟩
    have hs : F ⊆ graphEdges (star n s) ∩ cycleSupport c :=
      fun e he => Finset.mem_inter.mpr ⟨hF he,hc he⟩
    have hh := (Finset.card_le_card hs).trans (star_cycle_support_card c)
    omega
  let := he
  exact Nat.card_of_isEmpty
#print axioms star_higher_completion_zero
end Frustrated
```
<!-- LEAN-SOURCE-END StarSupport -->

<!-- LEAN-SOURCE-BEGIN StarExpansion SHA256 3f2f2f89c46b5a014f4b9413419d625e6acd684d11a3928c440fbbee2cd3ae88 BYTES 2237 -->
```lean
import StarSupport
namespace Frustrated

theorem empty_tuple_completions (n k : Nat) :
    tupleCompletions (n:=n) (k:=k) ∅ = Nat.card (Ambient n k) := by
  unfold tupleCompletions
  have e : {c : Ambient n k // (∅ : Finset (Sym2 (Fin n))) ⊆ cycleSupport c} ≃ Ambient n k :=
    { toFun := Subtype.val
      invFun := fun c => ⟨c,Finset.empty_subset _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

/-- Exact source expansion, with all terms of support ≥3 removed by proof. -/
theorem star_truncated_expansion {n k s : Nat} (hk : 3≤k) :
    (4*(k:Int))*cycleCount n k (star n s) =
      - ∑ F ∈ ((graphEdges (star n s)).powerset.filter
        (fun F => 1≤F.card ∧ F.card≤2)),
          (-2:Int)^F.card * tupleCompletions (k:=k) F := by
  classical
  let E := graphEdges (star n s)
  let w := fun F : Finset (Sym2 (Fin n)) => (-2:Int)^F.card * tupleCompletions (k:=k) F
  have hpart : ∑ F ∈ E.powerset, w F = w ∅ +
      ∑ F ∈ E.powerset.filter (fun F => 1≤F.card ∧ F.card≤2), w F := by
    have hpoint (F : Finset (Sym2 (Fin n))) (hF : F∈E.powerset) :
        w F = (if F=∅ then w ∅ else 0) +
          (if 1≤F.card ∧ F.card≤2 then w F else 0) := by
      by_cases hz : F=∅
      · subst F; simp
      · have hpos : 1≤F.card := by exact Nat.succ_le_of_lt (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz))
        by_cases hsmall : F.card≤2
        · simp [hz,hpos,hsmall]
        · have hzero := star_higher_completion_zero hk F (Finset.mem_powerset.mp hF) (by omega)
          simp [w,hz,hsmall,hzero]
    calc
      _ = ∑ F ∈ E.powerset, ((if F=∅ then w ∅ else 0) +
          (if 1≤F.card ∧ F.card≤2 then w F else 0)) := Finset.sum_congr rfl hpoint
      _ = _ := by simp [Finset.sum_add_distrib,Finset.sum_filter]
  have h := subset_expansion_cycle_scale hk (star n s)
  change (4*(k:Int))*cycleCount n k (star n s) =
    (Nat.card (Ambient n k):Int) - ∑ F ∈ E.powerset, w F at h
  rw [hpart] at h
  have hw : w ∅=(Nat.card (Ambient n k):Int) := by simp [w,empty_tuple_completions]
  rw [hw] at h
  simpa only [sub_add_cancel_left] using h
#print axioms star_truncated_expansion
end Frustrated
```
<!-- LEAN-SOURCE-END StarExpansion -->

<!-- LEAN-SOURCE-BEGIN SingletonSum SHA256 7fc90168c3d6139698fcbe21383bf7df3866d77b6509bac9c38faba27c48386d BYTES 747 -->
```lean
import StarExpansion
namespace Frustrated
/-- Evaluated singleton portion of the literal ordered-tuple source expansion. -/
theorem singleton_completion_sum {n k} (hk : 3≤k) (G : Graph (Fin n)) :
    (∑ e ∈ graphEdges G, tupleCompletions (k:=k) {e}) =
      (graphEdges G).card*(2*k*(n-2).descFactorial (k-2)) := by
  classical
  have h (e : Sym2 (Fin n)) (he : e∈graphEdges G) :
      tupleCompletions (k:=k) {e}=2*k*(n-2).descFactorial (k-2) := by
    unfold tupleCompletions
    simp_rw [Finset.singleton_subset_iff]
    exact graph_edge_completion_count hk G e he
  calc
    _ = ∑ _e ∈ graphEdges G, 2*k*(n-2).descFactorial (k-2) := Finset.sum_congr rfl h
    _ = _ := by simp
#print axioms singleton_completion_sum
end Frustrated
```
<!-- LEAN-SOURCE-END SingletonSum -->

<!-- LEAN-SOURCE-BEGIN SignedExpansion SHA256 2165ab1f83ec74a74845502325c165212dfae37dde99e3ba7ff12670bd624ea5 BYTES 4265 -->
```lean
import FullRemainder
import SingletonSum
namespace Frustrated
attribute [local instance] Classical.propDecidable
noncomputable def nonemptySupports {n} (E : Finset (Sym2 (Fin n))) :=
  E.powerset.filter (fun F => F.Nonempty)
noncomputable def lowSupports {n} (E : Finset (Sym2 (Fin n))) :=
  E.powerset.filter (fun F => F.Nonempty ∧ F.card ≤ 2 ∧ ∀ e ∈ F, ∀ f ∈ F, EdgeMeets e f)
noncomputable def supportWeight {n k : Nat} (F : Finset (Sym2 (Fin n))) : Int :=
  (-2 : Int)^(F.card-1) * tupleCompletions (k:=k) F

theorem nonempty_subset_expansion {n k : Nat} (hk : 3 ≤ k) (G : Graph (Fin n)) :
    (2*(k:Int))*cycleCount n k G =
      ∑ F ∈ nonemptySupports (graphEdges G), supportWeight (k:=k) F := by
  classical
  let E := graphEdges G
  let w := fun F : Finset (Sym2 (Fin n)) => (-2:Int)^F.card * tupleCompletions (k:=k) F
  have hp (F : Finset (Sym2 (Fin n))) (_hF : F ∈ E.powerset) :
      w F = (if F=∅ then (Nat.card (Ambient n k):Int) else 0) -
        2*(if F.Nonempty then supportWeight (k:=k) F else 0) := by
    by_cases hz : F=∅
    · subst F; simp [w,empty_tuple_completions]
    · have hne := Finset.nonempty_iff_ne_empty.mpr hz
      have hc : F.card = (F.card-1)+1 := by have := Finset.card_pos.mpr hne; omega
      simp only [hz,ite_false,hne,ite_true,zero_sub]
      dsimp [w,supportWeight]
      conv_lhs => rw [hc,pow_succ]
      ring
  have hsum : (∑ F ∈ E.powerset, w F) =
      (Nat.card (Ambient n k):Int) -
        2*(∑ F ∈ nonemptySupports E, supportWeight (k:=k) F) := by
    calc
      _ = ∑ F ∈ E.powerset, ((if F=∅ then (Nat.card (Ambient n k):Int) else 0) -
          2*(if F.Nonempty then supportWeight (k:=k) F else 0)) := Finset.sum_congr rfl hp
      _ = _ := by
        simp [Finset.sum_sub_distrib,nonemptySupports,Finset.sum_filter]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro F hF
        split_ifs <;> simp
  have h := subset_expansion_cycle_scale hk G
  change (4*(k:Int))*cycleCount n k G = (Nat.card (Ambient n k):Int) - ∑ F ∈ E.powerset, w F at h
  rw [hsum] at h
  nlinarith

theorem exact_low_remainder_expansion {n k : Nat} (hk : 3 ≤ k) (G : Graph (Fin n)) :
    (2*(k:Int))*cycleCount n k G =
      (∑ F ∈ lowSupports (graphEdges G), supportWeight (k:=k) F) +
        signedRemainder (k:=k) (graphEdges G) := by
  classical
  rw [nonempty_subset_expansion hk G]
  let E := graphEdges G
  have hpoint (F : Finset (Sym2 (Fin n))) (hF : F∈E.powerset) :
      (if F.Nonempty then supportWeight (k:=k) F else 0) =
        (if F.Nonempty ∧ F.card ≤ 2 ∧ ∀ e ∈ F, ∀ f ∈ F, EdgeMeets e f then supportWeight (k:=k) F else 0) +
        (if 3 ≤ F.card ∨ ∃ e ∈ F, ∃ f ∈ F, ¬ EdgeMeets e f then supportWeight (k:=k) F else 0) := by
    by_cases hz : F.Nonempty
    · by_cases hb : 3 ≤ F.card ∨ ∃ e ∈ F, ∃ f ∈ F, ¬ EdgeMeets e f
      · have hn : ¬(F.card ≤ 2 ∧ ∀ e ∈ F, ∀ f ∈ F, EdgeMeets e f) := by
          rintro ⟨hsmall,hm⟩
          rcases hb with hb | ⟨e,he,f,hf,hd⟩
          · omega
          · exact hd (hm e he f hf)
        simp [hz,hb,hn]
      · have hl : F.card ≤ 2 ∧ ∀ e ∈ F, ∀ f ∈ F, EdgeMeets e f := by
          push Not at hb
          exact ⟨by omega,hb.2⟩
        have hlow : F.Nonempty ∧ F.card ≤ 2 ∧ ∀ e ∈ F, ∀ f ∈ F, EdgeMeets e f := ⟨hz,hl⟩
        split_ifs; simp
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hz
      subst F; simp
  have hs := Finset.sum_congr rfl hpoint
  simpa [nonemptySupports,lowSupports,signedRemainder,badSupports,supportWeight,
    Finset.sum_filter,Finset.sum_add_distrib] using hs

theorem actual_expansion_uniform_remainder {n m M : Nat} (G : Graph (Fin n))
    (hM : (graphEdges G).card ≤ M) :
    |(2*((4+m):Int))*cycleCount n (4+m) G -
      ∑ F ∈ lowSupports (graphEdges G), supportWeight (k:=4+m) F| ≤
        (2^(2*M)*(4+m)^4*n^m : Nat) := by
  have h := exact_low_remainder_expansion (k:=4+m) (by omega) G
  push_cast at h
  rw [h,add_sub_cancel_left]
  exact full_signed_remainder_bound (graphEdges G) hM
#print axioms nonempty_subset_expansion
#print axioms exact_low_remainder_expansion
#print axioms actual_expansion_uniform_remainder
end Frustrated
```
<!-- LEAN-SOURCE-END SignedExpansion -->

<!-- LEAN-SOURCE-BEGIN AdjacentSum SHA256 c6e3807143f9c5aa41da5bc720788c5595d13c2201e6f7c4adb875f7346eba82 BYTES 2298 -->
```lean
import SignedExpansion
namespace Frustrated
attribute [local instance] Classical.propDecidable
noncomputable def adjacentSupports {n} (E : Finset (Sym2 (Fin n))) :=
  E.powerset.filter (fun F => F.card=2 ∧ ∀ e ∈ F, ∀ f ∈ F, EdgeMeets e f)

theorem loopless_graph_edges {n} (G : Graph (Fin n)) (a : Fin n) :
    s(a,a) ∉ graphEdges G := by
  intro h
  have hh := (Finset.mem_filter.mp h).2
  change G.edge a a = true at hh
  rw [G.loopless] at hh
  contradiction

theorem adjacent_pair_completion {n m} (F : Finset (Sym2 (Fin n)))
    (hloop : ∀ a, s(a,a) ∉ F) (hcard : F.card=2)
    (hmeet : ∀ e ∈ F, ∀ f ∈ F, EdgeMeets e f) :
    tupleCompletions (k:=3+m) F = 2*(3+m)*(n-3).descFactorial m := by
  classical
  obtain ⟨e,f,hef,hF⟩ := Finset.card_eq_two.mp hcard
  have he : e ∈ F := by rw [hF]; simp
  have hf : f ∈ F := by rw [hF]; simp
  obtain ⟨a,hae,haf⟩ := hmeet e he f hf
  obtain ⟨b,hb⟩ := Sym2.mem_iff_exists.mp hae
  obtain ⟨d,hd⟩ := Sym2.mem_iff_exists.mp haf
  subst e
  subst f
  have hab : a ≠ b := by intro h; subst b; exact hloop a he
  have had : a ≠ d := by intro h; subst d; exact hloop a hf
  have hbd : b ≠ d := by intro h; subst d; exact hef rfl
  let q : Ambient n 3 := ⟨![b,a,d],by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  have hq : F = {s(q 0,q 1),s(q 1,q 2)} := by
    change F = {s(b,a),s(a,d)}
    rw [hF,show s(b,a)=s(a,b) from Sym2.eq_swap]
  rw [hq]
  exact adjacent_completion_count q

theorem adjacent_completion_sum {n m} (G : Graph (Fin n)) :
    (∑ F ∈ adjacentSupports (graphEdges G), tupleCompletions (k:=3+m) F) =
      (adjacentSupports (graphEdges G)).card * (2*(3+m)*(n-3).descFactorial m) := by
  classical
  have ht (F : Finset (Sym2 (Fin n))) (hF : F ∈ adjacentSupports (graphEdges G)) :
      tupleCompletions (k:=3+m) F = 2*(3+m)*(n-3).descFactorial m := by
    have hh := Finset.mem_filter.mp hF
    have hs := Finset.mem_powerset.mp hh.1
    exact adjacent_pair_completion F (fun a ha => loopless_graph_edges G a (hs ha)) hh.2.1 hh.2.2
  calc
    _ = ∑ _F ∈ adjacentSupports (graphEdges G), 2*(3+m)*(n-3).descFactorial m := Finset.sum_congr rfl ht
    _ = _ := by simp
#print axioms adjacent_pair_completion
#print axioms adjacent_completion_sum
end Frustrated
```
<!-- LEAN-SOURCE-END AdjacentSum -->

<!-- LEAN-SOURCE-BEGIN LowEvaluation SHA256 82d3923ceba4eed2064c187e9b066fd7ff079655e4fe25f15e3bf9537d101921 BYTES 3031 -->
```lean
import AdjacentSum
namespace Frustrated
attribute [local instance] Classical.propDecidable

theorem edge_meets_self {V : Type} (e : Sym2 V) : EdgeMeets e e := by
  induction e using Sym2.inductionOn with
  | _ a b => exact ⟨a,by simp,by simp⟩

theorem low_support_partition {n} (E : Finset (Sym2 (Fin n))) :
    lowSupports E = E.image (fun e => {e}) ∪ adjacentSupports E := by
  classical
  ext F
  constructor
  · intro h
    obtain ⟨hsub,hne,hcard,hm⟩ := Finset.mem_filter.mp h
    have hp := Finset.card_pos.mpr hne
    by_cases h1 : F.card=1
    · obtain ⟨e,rfl⟩ := Finset.card_eq_one.mp h1
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨e,(Finset.mem_powerset.mp hsub) (by simp),rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hsub,by omega,hm⟩
  · intro h
    rcases Finset.mem_union.mp h with hs | ha
    · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hs
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (by simpa using he),by simp,by simp,?_⟩
      intro f hf g hg
      have hf' : f=e := by simpa using hf
      have hg' : g=e := by simpa using hg
      subst f; subst g
      exact edge_meets_self e
    · obtain ⟨hsub,hcard,hm⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨hsub,Finset.card_pos.mp (by omega),by omega,hm⟩

theorem low_support_evaluation {n m} (G : Graph (Fin n)) :
    (∑ F ∈ lowSupports (graphEdges G), supportWeight (k:=3+m) F) =
      (((graphEdges G).card * (2*(3+m)*(n-2).descFactorial (1+m)) : Nat) : Int) -
        2*(((adjacentSupports (graphEdges G)).card * (2*(3+m)*(n-3).descFactorial m) : Nat) : Int) := by
  classical
  let E := graphEdges G
  have hd : Disjoint (E.image (fun e => {e})) (adjacentSupports E) := by
    apply Finset.disjoint_left.mpr
    intro F hs ha
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hs
    have hh := (Finset.mem_filter.mp ha).2.1
    simp at hh
  rw [low_support_partition,Finset.sum_union hd]
  have hs : (∑ F ∈ E.image (fun e => {e}), supportWeight (k:=3+m) F) =
      ((∑ e ∈ E, tupleCompletions (k:=3+m) {e} : Nat) : Int) := by
    rw [Finset.sum_image]
    · simp [supportWeight,Nat.cast_sum]
    · intro e he f hf h
      simpa using h
  have ha : (∑ F ∈ adjacentSupports E, supportWeight (k:=3+m) F) =
      -2*((∑ F ∈ adjacentSupports E, tupleCompletions (k:=3+m) F : Nat) : Int) := by
    rw [Nat.cast_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro F hF
    have hc := (Finset.mem_filter.mp hF).2.1
    simp [supportWeight,hc]
  change (∑ F ∈ E.image (fun e => {e}), supportWeight (k:=3+m) F) +
    (∑ F ∈ adjacentSupports E, supportWeight (k:=3+m) F) = _
  rw [hs,ha]
  have hsingle := singleton_completion_sum (k:=3+m) (by omega) G
  have hadj := adjacent_completion_sum (m:=m) G
  change (∑ e ∈ E, tupleCompletions (k:=3+m) {e}) = _ at hsingle
  rw [hsingle,hadj]
  have hm : 3+m-2=1+m := by omega
  rw [hm]
  ring
#print axioms low_support_evaluation
end Frustrated
```
<!-- LEAN-SOURCE-END LowEvaluation -->

<!-- LEAN-SOURCE-BEGIN RelabelledStar SHA256 747ee2543a3ab3917a31dd263b3db0ec42225b943680674865a409034d71b22a BYTES 2544 -->
```lean
import LowEvaluation
namespace Frustrated
attribute [local instance] Classical.propDecidable

theorem centered_higher_completion_zero {n k : Nat} (hk : 3 ≤ k)
    (F : Finset (Sym2 (Fin n))) (a : Fin n) (ha : ∀ e ∈ F, a ∈ e)
    (hcard : 3 ≤ F.card) : tupleCompletions (k:=k) F=0 := by
  classical
  have he : IsEmpty {c : Ambient n k // F ⊆ cycleSupport c} := by
    constructor
    rintro ⟨c,hc⟩
    let : NeZero k := ⟨by omega⟩
    have hs : F ⊆ (cycleSupport c).filter (fun e => a ∈ e) :=
      fun e he => Finset.mem_filter.mpr ⟨hc he,ha e he⟩
    have hh := (Finset.card_le_card hs).trans (cycle_incident_card_le_two c a)
    omega
  let := he
  exact Nat.card_of_isEmpty

theorem centered_remainder_zero {n k : Nat} (hk : 3 ≤ k)
    (E : Finset (Sym2 (Fin n))) (a : Fin n) (ha : ∀ e ∈ E, a ∈ e) :
    signedRemainder (k:=k) E=0 := by
  classical
  apply Finset.sum_eq_zero
  intro F hF
  obtain ⟨hsub,hbad⟩ := Finset.mem_filter.mp hF
  have hs := Finset.mem_powerset.mp hsub
  rcases hbad with hc | ⟨e,he,f,hf,hd⟩
  · simp only [centered_higher_completion_zero hk F a (fun e he => ha e (hs he)) hc,Nat.cast_zero,mul_zero]
  · exact (hd ⟨a,ha e (hs he),ha f (hs hf)⟩).elim

theorem centered_adjacent_card {n} (E : Finset (Sym2 (Fin n)))
    (a : Fin n) (ha : ∀ e ∈ E, a ∈ e) :
    (adjacentSupports E).card = E.card.choose 2 := by
  classical
  have hs : adjacentSupports E = E.powersetCard 2 := by
    ext F
    simp only [adjacentSupports,Finset.mem_filter,Finset.mem_powerset,Finset.mem_powersetCard]
    constructor
    · rintro ⟨hsub,hcard,hm⟩
      exact ⟨hsub,hcard⟩
    · rintro ⟨hsub,hcard⟩
      exact ⟨hsub,hcard,fun e he f hf => ⟨a,ha e (hsub he),ha f (hsub hf)⟩⟩
  rw [hs,Finset.card_powersetCard]

theorem relabelled_star_formula {n m} (G : Graph (Fin n))
    (a : Fin n) (ha : ∀ e ∈ graphEdges G, a ∈ e) :
    (cycleCount n (3+m) G : Int) =
      ((graphEdges G).card : Int)*(n-2).descFactorial (1+m) -
        2*((graphEdges G).card.choose 2 : Int)*(n-3).descFactorial m := by
  have h := exact_low_remainder_expansion (k:=3+m) (by omega) G
  rw [centered_remainder_zero (by omega) (graphEdges G) a ha,add_zero,
    low_support_evaluation,centered_adjacent_card (graphEdges G) a ha] at h
  push_cast at h ⊢
  have hp : (2*(3+(m:Int))) ≠ 0 := by omega
  apply mul_left_cancel₀ hp
  rw [h]
  ring
#print axioms centered_higher_completion_zero
#print axioms centered_remainder_zero
#print axioms relabelled_star_formula
end Frustrated
```
<!-- LEAN-SOURCE-END RelabelledStar -->

<!-- LEAN-SOURCE-BEGIN CanonicalStar SHA256 e667d92c966b81981e53b975084173baa57fe3e7df301a3b93feb5fb8b77a3db BYTES 2507 -->
```lean
import RelabelledStar
namespace Frustrated

theorem canonical_star_edge_card {n s : Nat} (hn : s+1 ≤ n) :
    (graphEdges (star n s)).card = s := by
  classical
  let z : Fin n := ⟨0,by omega⟩
  let leaf : Fin s → Fin n := fun i => ⟨i.val+1,by omega⟩
  let f : Fin s → Sym2 (Fin n) := fun i => s(z,leaf i)
  have hf : Function.Injective f := by
    intro i j h
    rcases Sym2.eq_iff.mp h with h | h
    · apply Fin.ext
      have hh := congrArg Fin.val h.2
      change i.val+1=j.val+1 at hh
      omega
    · have hh := congrArg Fin.val h.1
      change 0=j.val+1 at hh
      omega
  have he : graphEdges (star n s) = Finset.univ.image f := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b =>
      constructor
      · intro h
        have hh := (Finset.mem_filter.mp h).2
        change decide ((a.val=0 ∧ 1≤b.val ∧ b.val≤s) ∨ (b.val=0 ∧ 1≤a.val ∧ a.val≤s))=true at hh
        rcases of_decide_eq_true hh with hh | hh
        · let i : Fin s := ⟨b.val-1,by omega⟩
          have ha : a=z := Fin.ext hh.1
          have hb : b=leaf i := by apply Fin.ext; dsimp [leaf,i]; omega
          exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simp only [f,← ha,← hb]⟩
        · let i : Fin s := ⟨a.val-1,by omega⟩
          have hb : b=z := Fin.ext hh.1
          have ha : a=leaf i := by apply Fin.ext; dsimp [leaf,i]; omega
          exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by
            change s(z,leaf i)=s(a,b)
            rw [← hb,← ha]
            exact Sym2.eq_swap⟩
      · intro h
        obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp h
        rw [← heq]
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        change decide ((z.val=0 ∧ 1≤(leaf i).val ∧ (leaf i).val≤s) ∨
          ((leaf i).val=0 ∧ 1≤z.val ∧ z.val≤s))=true
        apply decide_eq_true
        left
        dsimp [z,leaf]
        exact ⟨rfl,by omega,by omega⟩
  rw [he,Finset.card_image_of_injective _ hf]
  simp

theorem canonical_star_formula {n s m : Nat} (hn : s+1 ≤ n) :
    (cycleCount n (3+m) (star n s) : Int) =
      (s:Int)*(n-2).descFactorial (1+m) - 2*(s.choose 2 : Int)*(n-3).descFactorial m := by
  let : NeZero n := ⟨by omega⟩
  have h := relabelled_star_formula (m:=m) (star n s) (0:Fin n) (fun e he => star_edge_zero e he)
  rw [canonical_star_edge_card hn] at h
  exact h
#print axioms canonical_star_edge_card
#print axioms canonical_star_formula
end Frustrated
```
<!-- LEAN-SOURCE-END CanonicalStar -->

<!-- LEAN-SOURCE-BEGIN ThreeCorrection SHA256 f1175ac56b1e5088dbb0010cc36d89aa3d78c59e800711781024fa00b5787a92 BYTES 2933 -->
```lean
import CanonicalStar
namespace Frustrated
attribute [local instance] Classical.propDecidable

theorem oversized_completion_zero {n k : Nat} (hk : 3 ≤ k)
    (F : Finset (Sym2 (Fin n))) (hcard : k < F.card) : tupleCompletions (k:=k) F=0 := by
  classical
  have he : IsEmpty {c : Ambient n k // F ⊆ cycleSupport c} := by
    constructor
    rintro ⟨c,hc⟩
    have hh := Finset.card_le_card hc
    rw [cycleSupport_card hk c] at hh
    omega
  let := he
  exact Nat.card_of_isEmpty

theorem disjoint_completion_zero_three {n} (F : Finset (Sym2 (Fin n)))
    (hd : ∃ e ∈ F, ∃ f ∈ F, ¬ EdgeMeets e f) : tupleCompletions (k:=3) F=0 := by
  classical
  have he : IsEmpty {c : Ambient n 3 // F ⊆ cycleSupport c} := by
    constructor
    rintro ⟨c,hc⟩
    have hl : ∀ a, s(a,a) ∉ F := fun a ha => support_loopless (by omega) c a (hc ha)
    obtain ⟨q,hq⟩ := disjoint_incident_four F hl hd
    have hx (i : Fin 4) : ∃ j, c j=q i := by
      obtain ⟨e,he,hv⟩ := hq i
      exact cycle_support_vertex c e (hc he) (q i) hv
    let j : Fin 4 → Fin 3 := fun i => Classical.choose (hx i)
    have hj (i : Fin 4) : c (j i)=q i := Classical.choose_spec (hx i)
    have hinj : Function.Injective j := by
      intro a b h
      apply q.injective
      rw [← hj a,← hj b,h]
    have hh := Fintype.card_le_of_injective j hinj
    norm_num at hh
  let := he
  exact Nat.card_of_isEmpty

theorem three_remainder_exact {n} (E : Finset (Sym2 (Fin n))) :
    signedRemainder (k:=3) E =
      4*((∑ F ∈ E.powerset.filter (fun F => F.card=3), tupleCompletions (k:=3) F : Nat) : Int) := by
  classical
  unfold signedRemainder badSupports
  rw [Finset.sum_filter,Nat.cast_sum,Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F hF
  by_cases h3 : F.card=3
  · simp [h3]
  · by_cases hlarge : 3 < F.card
    · simp [oversized_completion_zero (by omega) F hlarge]
    · by_cases hb : 3 ≤ F.card ∨ ∃ e ∈ F, ∃ f ∈ F, ¬ EdgeMeets e f
      · have hd : ∃ e ∈ F, ∃ f ∈ F, ¬ EdgeMeets e f := hb.resolve_left (by omega)
        simp [disjoint_completion_zero_three F hd,h3]
      · simp only [hb,ite_false,h3]

theorem three_remainder_nonnegative {n} (E : Finset (Sym2 (Fin n))) :
    0 ≤ signedRemainder (k:=3) E := by
  rw [three_remainder_exact]
  positivity

theorem exact_three_correction {n} (G : Graph (Fin n)) :
    (6:Int)*cycleCount n 3 G =
      ((graphEdges G).card : Int)*(6*((n-2:Nat):Int)) -
      2*((adjacentSupports (graphEdges G)).card : Int)*6 +
      4*((∑ F ∈ (graphEdges G).powerset.filter (fun F => F.card=3), tupleCompletions (k:=3) F : Nat) : Int) := by
  have h := exact_low_remainder_expansion (k:=3) (by omega) G
  rw [low_support_evaluation (m:=0),three_remainder_exact] at h
  simpa [mul_assoc] using h
#print axioms disjoint_completion_zero_three
#print axioms three_remainder_exact
#print axioms exact_three_correction
end Frustrated
```
<!-- LEAN-SOURCE-END ThreeCorrection -->

<!-- LEAN-SOURCE-BEGIN SparseComparison SHA256 d18e9ec066e53ad05fea5fb5b96b7e50bc6ba8ca0843129dcf6160901939346e BYTES 2901 -->
```lean
import ThreeCorrection
namespace Frustrated
attribute [local instance] Classical.propDecidable

theorem adjacent_card_le_choose {n} (E : Finset (Sym2 (Fin n))) :
    (adjacentSupports E).card ≤ E.card.choose 2 := by
  have hs : adjacentSupports E ⊆ E.powersetCard 2 := by
    intro F hF
    obtain ⟨hsub,hcard,hm⟩ := Finset.mem_filter.mp hF
    exact Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hsub,hcard⟩
  exact (Finset.card_le_card hs).trans_eq (Finset.card_powersetCard _ _)

theorem adjacent_card_le_pow {n M} (E : Finset (Sym2 (Fin n))) (hM : E.card ≤ M) :
    (adjacentSupports E).card ≤ 2^M := by
  have hs : adjacentSupports E ⊆ E.powerset := Finset.filter_subset _ _
  calc
    _ ≤ E.powerset.card := Finset.card_le_card hs
    _ = 2^E.card := Finset.card_powerset E
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hM

theorem three_sparse_star_lower {n} (G : Graph (Fin n))
    (hn : (graphEdges G).card+1 ≤ n) :
    cycleCount n 3 (star n (graphEdges G).card) ≤ cycleCount n 3 G := by
  have h := exact_low_remainder_expansion (k:=3) (by omega) G
  rw [low_support_evaluation (m:=0)] at h
  have hs := canonical_star_formula (m:=0) hn
  have hr := three_remainder_nonnegative (graphEdges G)
  have ha : ((adjacentSupports (graphEdges G)).card : Int) ≤ ((graphEdges G).card.choose 2 : Int) :=
    by exact_mod_cast adjacent_card_le_choose (graphEdges G)
  simp only [Nat.add_zero,Nat.descFactorial_one,Nat.descFactorial_zero,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_one] at h hs
  have hc : (cycleCount n 3 (star n (graphEdges G).card) : Int) ≤ (cycleCount n 3 G : Int) := by nlinarith
  exact_mod_cast hc

theorem evaluated_sparse_expansion {n m} (G : Graph (Fin n)) :
    (2*((4+m:Nat):Int))*cycleCount n (4+m) G =
      (2*((4+m:Nat):Int))*
        (((graphEdges G).card : Int)*(n-2).descFactorial (2+m) -
          2*((adjacentSupports (graphEdges G)).card : Int)*(n-3).descFactorial (1+m)) +
      signedRemainder (k:=4+m) (graphEdges G) := by
  have h := exact_low_remainder_expansion (k:=3+(1+m)) (by omega) G
  rw [low_support_evaluation (m:=1+m)] at h
  have he : 3+(1+m)=4+m := by omega
  have he' : 1+(1+m)=2+m := by omega
  rw [he,he'] at h
  push_cast at h ⊢
  rw [h]
  ring

theorem remainder_smaller_than_adjacent {n m C : Nat}
    (hn : 2*(3+(1+m)) ≤ n) (hC : C*2^(1+m) < n) :
    C*n^m < (n-3).descFactorial (1+m) := by
  have hl := falling_uniform_lower 3 (1+m) n hn
  have hp : 0<n^m := Nat.pow_pos (by omega)
  have hmul := Nat.mul_lt_mul_of_pos_right hC hp
  have he : n^(1+m)=n*n^m := by rw [pow_add]; simp
  rw [he] at hl
  by_contra h
  have hb : (n-3).descFactorial (1+m) ≤ C*n^m := Nat.le_of_not_gt h
  have hh := Nat.mul_le_mul_left (2^(1+m)) hb
  nlinarith only [hl,hmul,hh]
#print axioms three_sparse_star_lower
#print axioms evaluated_sparse_expansion
#print axioms remainder_smaller_than_adjacent
end Frustrated
```
<!-- LEAN-SOURCE-END SparseComparison -->

<!-- LEAN-SOURCE-BEGIN PairwiseRemainder SHA256 0aa6c7454b1ab7a8c9a74f4a728385a30fbe7c192a60d2683b39ad90231282f8 BYTES 3334 -->
```lean
import SparseComparison
namespace Frustrated
attribute [local instance] Classical.propDecidable

theorem pairwise_adjacent_eq {n} (E : Finset (Sym2 (Fin n)))
    (hm : ∀ e ∈ E, ∀ f ∈ E, EdgeMeets e f) :
    adjacentSupports E = E.powersetCard 2 := by
  ext F
  simp only [adjacentSupports,Finset.mem_filter,Finset.mem_powerset,Finset.mem_powersetCard]
  constructor
  · rintro ⟨hs,hc,hh⟩; exact ⟨hs,hc⟩
  · rintro ⟨hs,hc⟩; exact ⟨hs,hc,fun e he f hf => hm e (hs he) f (hs hf)⟩

theorem adjacent_card_strict {n} (E : Finset (Sym2 (Fin n)))
    (hm : ¬ ∀ e ∈ E, ∀ f ∈ E, EdgeMeets e f) :
    (adjacentSupports E).card < E.card.choose 2 := by
  have hs : adjacentSupports E ⊆ E.powersetCard 2 := by
    intro F hF
    obtain ⟨hsub,hcard,hh⟩ := Finset.mem_filter.mp hF
    exact Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hsub,hcard⟩
  have hne : adjacentSupports E ≠ E.powersetCard 2 := by
    intro heq
    apply hm
    intro e he f hf
    by_cases hef : e=f
    · subst f; exact edge_meets_self e
    · have hp : ({e,f} : Finset (Sym2 (Fin n))) ∈ E.powersetCard 2 := by
        apply Finset.mem_powersetCard.mpr
        exact ⟨by intro g hg; simp only [Finset.mem_insert,Finset.mem_singleton] at hg; rcases hg with rfl | rfl <;> assumption,by simp [hef]⟩
      rw [← heq] at hp
      exact (Finset.mem_filter.mp hp).2.2 e (by simp) f (by simp)
  have hh := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs,hne⟩)
  simpa only [Finset.card_powersetCard] using hh

theorem pairwise_remainder_zero {n m} (G : Graph (Fin n))
    (hm : ∀ e ∈ graphEdges G, ∀ f ∈ graphEdges G, EdgeMeets e f) :
    signedRemainder (k:=4+m) (graphEdges G)=0 := by
  classical
  let E := graphEdges G
  by_cases hne : E.Nonempty
  · rcases pairwise_intersecting_classification E hne (loopless_graph_edges G) hm with hs | ht
    · obtain ⟨a,ha⟩ := hs
      exact centered_remainder_zero (by omega) E a ha
    · obtain ⟨a,b,c,hab,hac,hbc,hE⟩ := ht
      let q : Ambient n 3 := ⟨![a,b,c],by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all⟩
      have htri : E = {s(q 0,q 1),s(q 1,q 2),s(q 2,q 0)} := by
        change E={s(a,b),s(b,c),s(c,a)}
        rw [hE,show s(c,a)=s(a,c) from Sym2.eq_swap]
        ext e
        simp only [Finset.mem_insert,Finset.mem_singleton]
        tauto
      have hcard : E.card ≤ 3 := by
        rw [htri]
        simp only [Finset.card_insert_eq_ite,Finset.card_singleton]
        split_ifs <;> omega
      apply Finset.sum_eq_zero
      intro F hF
      obtain ⟨hsub,hbad⟩ := Finset.mem_filter.mp hF
      have hsub' := Finset.mem_powerset.mp hsub
      have hc : 3 ≤ F.card := by
        rcases hbad with h | ⟨e,he,f,hf,hd⟩
        · exact h
        · exact (hd (hm e (hsub' he) f (hsub' hf))).elim
      have hFE : F=E := Finset.eq_of_subset_of_card_le hsub' (by omega)
      have hz : tupleCompletions (k:=4+m) F=0 := by
        rw [hFE,htri]
        exact triangle_completion_zero q
      simp only [hz,Nat.cast_zero,mul_zero]
  · have he : E=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change signedRemainder (k:=4+m) E=0
    rw [he]
    simp [signedRemainder,badSupports,Finset.sum_filter]
#print axioms adjacent_card_strict
#print axioms pairwise_remainder_zero
end Frustrated
```
<!-- LEAN-SOURCE-END PairwiseRemainder -->

<!-- LEAN-SOURCE-BEGIN SparseMinimum SHA256 b2738b945cf0c2634ad31db8388ea0c64023650059cc79333b113a5d015dfc5e BYTES 2839 -->
```lean
import PairwiseRemainder
namespace Frustrated

theorem uniform_sparse_star_minimum {n m M : Nat} (G : Graph (Fin n))
    (hM : (graphEdges G).card ≤ M) (hn : (graphEdges G).card+1 ≤ n)
    (hfall : 2*(3+(1+m)) ≤ n)
    (hlarge : (2^(2*M)*(4+m)^4)*2^(1+m) < n) :
    cycleCount n (4+m) (star n (graphEdges G).card) ≤ cycleCount n (4+m) G := by
  classical
  let E := graphEdges G
  let B := (n-3).descFactorial (1+m)
  let K : Int := 2*((4+m:Nat):Int)
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hG := evaluated_sparse_expansion (m:=m) G
  have hS := canonical_star_formula (m:=1+m) hn
  have he : 3+(1+m)=4+m := by omega
  have he' : 1+(1+m)=2+m := by omega
  rw [he,he'] at hS
  have hr := full_signed_remainder_bound (m:=m) E hM
  have hd := remainder_smaller_than_adjacent hfall hlarge
  have hd' : ((2^(2*M)*(4+m)^4*n^m:Nat):Int) < (B:Int) := by exact_mod_cast hd
  have hB : (0:Int) < B := by exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le _) hd)
  have hR : -(B:Int) < signedRemainder (k:=4+m) E := by
    have hl := (abs_le.mp hr).1
    linarith
  by_cases hm : ∀ e ∈ E, ∀ f ∈ E, EdgeMeets e f
  · have hz := pairwise_remainder_zero (m:=m) G hm
    have ha : (adjacentSupports E).card=E.card.choose 2 := by
      rw [pairwise_adjacent_eq E hm,Finset.card_powersetCard]
    change (adjacentSupports (graphEdges G)).card = (graphEdges G).card.choose 2 at ha
    rw [hz,ha] at hG
    have hcount : (cycleCount n (4+m) (star n E.card):Int) = (cycleCount n (4+m) G:Int) := by
      apply mul_left_cancel₀ (by dsimp [K]; omega : K ≠ 0)
      rw [hS]
      simpa only [add_zero] using hG.symm
    exact_mod_cast hcount.le
  · have hA := adjacent_card_strict E hm
    have hA' : ((adjacentSupports E).card:Int)+1 ≤ (E.card.choose 2:Int) := by exact_mod_cast hA
    have hp := mul_le_mul_of_nonneg_right hA' (le_of_lt hB)
    have hscale := mul_le_mul_of_nonneg_left hp (by omega : (0:Int) ≤ K)
    have hKB := mul_le_mul_of_nonneg_right hK (by positivity : (0:Int) ≤ 2*(B:Int))
    have hcount : (cycleCount n (4+m) (star n E.card):Int) ≤ (cycleCount n (4+m) G:Int) := by
      by_contra hbad
      have hbad' : (cycleCount n (4+m) G:Int) ≤ (cycleCount n (4+m) (star n E.card):Int) := le_of_lt (lt_of_not_ge hbad)
      have hscaled := mul_le_mul_of_nonneg_left hbad' (by omega : (0:Int) ≤ K)
      change K*(cycleCount n (4+m) G:Int) = K*((E.card:Int)*(n-2).descFactorial (2+m) -
        2*((adjacentSupports E).card:Int)*(B:Int)) + signedRemainder (k:=4+m) E at hG
      change (cycleCount n (4+m) (star n E.card):Int) =
        (E.card:Int)*(n-2).descFactorial (2+m)-2*(E.card.choose 2:Int)*(B:Int) at hS
      have hSeq := congrArg (fun x : Int => K*x) hS
      nlinarith only [hG,hSeq,hR,hscale,hKB,hscaled,hB]
    exact_mod_cast hcount
#print axioms uniform_sparse_star_minimum
end Frustrated
```
<!-- LEAN-SOURCE-END SparseMinimum -->

<!-- LEAN-SOURCE-BEGIN SharpThreshold SHA256 44cd7079121e197956ec099035b541b29f027d804090c0d929bcce33bb0e0dc3 BYTES 2849 -->
```lean
import SparseMinimum
namespace Frustrated

theorem canonical_star_successor_lt {n s m : Nat}
    (hn : 2*s+2 < n) (hk : 3+m ≤ n) :
    cycleCount n (3+m) (star n s) < cycleCount n (3+m) (star n (s+1)) := by
  have h₀ := canonical_star_formula (m:=m) (s:=s) (by omega : s+1≤n)
  have h₁ := canonical_star_formula (m:=m) (s:=s+1) (by omega : s+1+1≤n)
  have hchoose : (s+1).choose 2=s.choose 2+s := by
    simpa [Nat.add_comm] using Nat.choose_succ_succ s 1
  have hn3 : n-3+1=n-2 := by omega
  have hfac : (n-2).descFactorial (1+m)=(n-2)*(n-3).descFactorial m := by
    simpa only [hn3,Nat.add_comm m 1] using Nat.succ_descFactorial_succ (n-3) m
  have hb : (0:Int) < (n-3).descFactorial m := by
    exact_mod_cast falling_eventual_positive 3 m n hk
  have hlead : (0:Int) < ((n-2:Nat):Int)-2*(s:Int) := by omega
  have hprod := mul_pos hlead hb
  rw [hchoose] at h₁
  rw [hfac] at h₀ h₁
  push_cast at h₀ h₁
  have hh : (cycleCount n (3+m) (star n s):Int) < (cycleCount n (3+m) (star n (s+1)):Int) := by
    nlinarith only [h₀,h₁,hprod]
  exact_mod_cast hh

theorem canonical_star_monotone {n s u m M : Nat}
    (hsu : s≤u) (hu : u≤M) (hn : 2*M+2<n) (hk : 3+m≤n) :
    cycleCount n (3+m) (star n s) ≤ cycleCount n (3+m) (star n u) := by
  have h : ∀ v, s≤v → v≤M →
      cycleCount n (3+m) (star n s) ≤ cycleCount n (3+m) (star n v) := by
    intro v hsv
    induction v, hsv using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ v hsv ih =>
      intro hv
      exact (ih (by omega)).trans (canonical_star_successor_lt (m:=m) (by omega : 2*v+2<n) hk).le
  exact h u hsu hu

theorem sparse_strict_threshold_forces_card {n m M t : Nat} (G : Graph (Fin n))
    (hM : (graphEdges G).card≤M) (hn : 2*M+2<n)
    (hfall : 2*(3+(1+m))≤n)
    (hlarge : (2^(2*M)*(4+m)^4)*2^(1+m)<n)
    (hthreshold : cycleCount n (4+m) G < cycleCount n (4+m) (star n (t+1))) :
    (graphEdges G).card≤t := by
  by_contra hbad
  have hs : t+1≤(graphEdges G).card := by omega
  have hmin := uniform_sparse_star_minimum G hM (by omega) hfall hlarge
  have hmono := canonical_star_monotone (m:=1+m) hs hM hn (by omega)
  have he : 3+(1+m)=4+m := by omega
  rw [he] at hmono
  omega

theorem three_strict_threshold_forces_card {n M t : Nat} (G : Graph (Fin n))
    (hM : (graphEdges G).card≤M) (hn : 2*M+2<n) (hk : 3≤n)
    (hthreshold : cycleCount n 3 G < cycleCount n 3 (star n (t+1))) :
    (graphEdges G).card≤t := by
  by_contra hbad
  have hs : t+1≤(graphEdges G).card := by omega
  have hmin := three_sparse_star_lower G (by omega)
  have hmono := canonical_star_monotone (m:=0) hs hM hn hk
  simp only [Nat.add_zero] at hmono
  omega
#print axioms canonical_star_successor_lt
#print axioms sparse_strict_threshold_forces_card
#print axioms three_strict_threshold_forces_card
end Frustrated
```
<!-- LEAN-SOURCE-END SharpThreshold -->

<!-- LEAN-SOURCE-BEGIN EdgeCardBridge SHA256 e8dabfcba92528ec52993c8fdc01bc529e551d1ef39a02980b186ed43c4cfdeb BYTES 1439 -->
```lean
import SharpThreshold
namespace Frustrated

theorem graphEdges_card_eq_edgeCount {n} (G : Graph (Fin n)) :
    (graphEdges G).card=edgeCount G := by
  classical
  let f : EdgePair G → {e // e ∈ graphEdges G} := fun p =>
    ⟨s(p.val.1,p.val.2),Finset.mem_filter.mpr ⟨Finset.mem_univ _,p.property.2⟩⟩
  have hf : Function.Injective f := by
    intro p q h
    have hh : s(p.val.1,p.val.2)=s(q.val.1,q.val.2) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp hh with hh | hh
    · apply Subtype.ext
      exact Prod.ext hh.1 hh.2
    · have hp := p.property.1
      have hq := q.property.1
      rw [hh.1,hh.2] at hp
      exact (lt_asymm hp hq).elim
  have hs : Function.Surjective f := by
    rintro ⟨e,he⟩
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hh := (Finset.mem_filter.mp he).2
      change G.edge a b=true at hh
      have hab : a≠b := by intro h; subst b; rw [G.loopless] at hh; contradiction
      rcases lt_or_gt_of_ne hab with hab | hba
      · refine ⟨⟨(a,b),hab,hh⟩,?_⟩
        apply Subtype.ext
        rfl
      · have hh' : G.edge b a=true := by rw [G.symm]; exact hh
        refine ⟨⟨(b,a),hba,hh'⟩,?_⟩
        apply Subtype.ext
        exact Sym2.eq_swap
  have h := Nat.card_congr (Equiv.ofBijective f ⟨hf,hs⟩)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,edgeCount] using h.symm
#print axioms graphEdges_card_eq_edgeCount
end Frustrated
```
<!-- LEAN-SOURCE-END EdgeCardBridge -->

<!-- LEAN-SOURCE-BEGIN EndpointV5 SHA256 b114247d7e34f7592482fc71223f926fcbb744d7e9d54640f130233e8e39622a BYTES 3867 -->
```lean
import EdgeCardBridge
namespace Frustrated

theorem sparse_eventual_card_bound (k t M : Nat) (hk : 3≤k) :
    ∃ N, ∀ n, N≤n → ∀ G : Graph (Fin n), (graphEdges G).card≤M →
      cycleCount n k G < cycleCount n k (star n (t+1)) → (graphEdges G).card≤t := by
  by_cases h3 : k=3
  · subst k
    refine ⟨2*M+4,?_⟩
    intro n hn G hM hth
    exact three_strict_threshold_forces_card G hM (by omega) (by omega) hth
  · obtain ⟨m,rfl⟩ : ∃ m, k=4+m := ⟨k-4,by omega⟩
    let C := (2^(2*M)*(4+m)^4)*2^(1+m)
    refine ⟨2*M+3+2*(3+(1+m))+C+1,?_⟩
    intro n hn G hM hth
    exact sparse_strict_threshold_forces_card G hM (by omega) (by omega) (by omega) hth

theorem graph_ext_edges {V} (G H : Graph V) (h : G.edge=H.edge) : G=H := by
  cases G
  cases H
  cases h
  rfl

theorem switch_compose {V} (G : Graph V) (U W : V → Bool) :
    switch (switch G U) W = switch G (fun z => xor (U z) (W z)) := by
  apply graph_ext_edges
  funext a b
  simp only [switch,cut]
  cases G.edge a b <;> cases U a <;> cases U b <;> cases W a <;> cases W b <;> rfl

theorem complement_switch_commute {V} [DecidableEq V] (G : Graph V) (U : V → Bool) :
    complement (switch G U)=switch (complement G) U := by
  apply graph_ext_edges
  funext a b
  by_cases hab : a=b
  · subst b
    simp [complement,switch,cut,G.loopless]
  · simp only [complement,switch,cut,hab,ite_false]
    cases G.edge a b <;> cases U a <;> cases U b <;> rfl

theorem conjecture19_proved : Conjecture19 := by
  intro k hk t
  let D := k*(t+1)*2^(k-3)
  let M := 16*D
  obtain ⟨Ns,hNs⟩ := sparse_eventual_card_bound k t M hk
  obtain ⟨No,hNo⟩ := odd_complement_eventual_exclusion (M:=M) (s:=t+1) hk
  let N := t+2+Ns+No+2*(k+1)+M+5
  refine ⟨N,by omega,?_⟩
  intro n hn G hthreshold
  cases n with
  | zero => omega
  | succ n =>
    have hkn : 2*(k+1) ≤ n+1 := by omega
    have hf : cycleCount (n+1) 4 G ≤ D*(n+1)*(n+1) :=
      threshold_f4_bound hk hkn G hthreshold
    have hnormal : 16*D<n-1 := by change M<n-1; omega
    obtain ⟨u,hu⟩ := whole_sparse_normal_form (by omega : 3≤n) hnormal G hf
    let U := G.edge u
    let W := fun z => decide (z=u)
    let H := switch G U
    let Q := switch (complement H) W
    change edgeCount H≤M ∨ edgeCount Q≤M at hu
    have hH : cycleCount (n+1) k H < cycleCount (n+1) k (star (n+1) (t+1)) := by
      simpa only [H,cycleCount_switch] using hthreshold
    rcases hu with hsmall | hsmall
    · have hcard : (graphEdges H).card≤M := by rwa [graphEdges_card_eq_edgeCount]
      have ht := hNs (n+1) (by omega) H hcard hH
      have hed : edgeCount H≤t := by rwa [graphEdges_card_eq_edgeCount] at ht
      exact Or.inl (nearCut_of_switch_sparse G U hed)
    · have hcard : (graphEdges Q).card≤M := by rwa [graphEdges_card_eq_edgeCount]
      by_cases he : k%2=0
      · have hQ : cycleCount (n+1) k Q < cycleCount (n+1) k (star (n+1) (t+1)) := by
          simpa only [Q,cycleCount_switch,complement_even_cycleCount hk he] using hH
        have ht := hNs (n+1) (by omega) Q hcard hQ
        have hed : edgeCount Q≤t := by rwa [graphEdges_card_eq_edgeCount] at ht
        have hq : Q=switch (complement G) (fun z => xor (U z) (W z)) := by
          change switch (complement (switch G U)) W = _
          rw [complement_switch_commute,switch_compose]
        rw [hq] at hed
        exact Or.inr (nearCut_of_switch_sparse (complement G) _ hed)
      · let A := switch H W
        have hA : cycleCount (n+1) k A < cycleCount (n+1) k (star (n+1) (t+1)) := by
          simpa only [A,cycleCount_switch] using hH
        have hAc : complement A=Q := complement_switch_commute H W
        have hMc : (graphEdges (complement A)).card≤M := by rwa [hAc]
        exact (hNo (n+1) (by omega) A he hMc hA).elim
#print axioms sparse_eventual_card_bound
#print axioms conjecture19_proved
end Frustrated
```
<!-- LEAN-SOURCE-END EndpointV5 -->

<!-- LEAN-SOURCE-BEGIN AuditV5 SHA256 013f9f948e8d08632487b1949e61cc219c4d3e38f87564044eb30d1e8b59f61f BYTES 483 -->
```lean
import EndpointV5
namespace Frustrated
example : Conjecture19 := conjecture19_proved
#print axioms conjecture19_proved
#print axioms full_signed_remainder_bound
#print axioms actual_expansion_uniform_remainder
#print axioms uniform_sparse_star_minimum
#print axioms sparse_strict_threshold_forces_card
#print axioms three_strict_threshold_forces_card
#print axioms canonical_star_formula
#print axioms exact_three_correction
#print axioms graphEdges_card_eq_edgeCount
end Frustrated
```
<!-- LEAN-SOURCE-END AuditV5 -->
