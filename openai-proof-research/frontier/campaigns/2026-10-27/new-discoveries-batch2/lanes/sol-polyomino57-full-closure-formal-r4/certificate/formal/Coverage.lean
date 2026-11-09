import Bounds
import Mathlib.Data.Finset.Union
set_option autoImplicit false
namespace Polyomino57
-- Executable, sign-complete growth. Renormalize AFTER insertion.
def neighbors (a : GridPoint) : Finset GridPoint :=
  {(a.1+1,a.2),(a.1-1,a.2),(a.1,a.2+1),(a.1,a.2-1)}
theorem mem_neighbors (a b : GridPoint) : b ∈ neighbors a ↔ Adj a b := by
  simp only [neighbors, Finset.mem_insert, Finset.mem_singleton, Adj, Prod.ext_iff]

def successors (Q : Finset GridPoint) : Finset (Finset GridPoint) :=
  Q.biUnion (fun a => ((neighbors a).filter (fun b => b ∉ Q)).image
    (fun b => normalize (insert b Q) (Finset.insert_nonempty _ _)))

theorem mem_successors (Q S : Finset GridPoint) : S ∈ successors Q ↔
    ∃ a ∈ Q, ∃ b, b ∉ Q ∧ Adj a b ∧
      S = normalize (insert b Q) (Finset.insert_nonempty _ _) := by
  simp only [successors, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    mem_neighbors]
  constructor
  · rintro ⟨a,ha,b,⟨hab,hb⟩,he⟩
    exact ⟨a,ha,b,hb,hab,he.symm⟩
  · rintro ⟨a,ha,b,hb,hab,he⟩
    exact ⟨a,ha,b,⟨hab,hb⟩,he.symm⟩

theorem translate_insert (t b : GridPoint) (Q : Finset GridPoint) :
    translate t (insert b Q) = insert (b.1+t.1,b.2+t.2) (translate t Q) := by
  simp [translate]

-- This is the bridge that covers insertions left of or below the current origin.
theorem normalized_insert_successor {Q : Finset GridPoint} (hQ : Q.Nonempty)
    {a b : GridPoint} (ha : a ∈ Q) (hb : b ∉ Q) (hab : Adj a b) :
    normalize (insert b Q) (Finset.insert_nonempty _ _) ∈
      successors (normalize Q hQ) := by
  let t : GridPoint := (-(lowerCorner Q hQ).1,-(lowerCorner Q hQ).2)
  have hat : (a.1+t.1,a.2+t.2) ∈ normalize Q hQ :=
    Finset.mem_image.mpr ⟨a,ha,rfl⟩
  have hbt : (b.1+t.1,b.2+t.2) ∉ normalize Q hQ := by
    intro h
    obtain ⟨c,hc,he⟩ := Finset.mem_image.mp h
    have he' : c = b := by
      apply Prod.ext <;> have hh := Prod.mk.inj he <;> dsimp [t] at * <;> omega
    exact hb (he' ▸ hc)
  apply (mem_successors _ _).mpr
  refine ⟨_,hat,_,hbt,(adj_translate t a b).mpr hab,?_⟩
  have hn := normalize_translate (insert b Q) (Finset.insert_nonempty _ _) t
  simpa only [translate_insert, normalize, t] using hn.symm

def generatedLayer : ℕ → Finset (Finset GridPoint)
  | 0 => {{(0,0)}}
  | k+1 => (generatedLayer k).biUnion successors

theorem normalize_singleton (p : GridPoint) :
    normalize {p} (Finset.singleton_nonempty _) = {(0,0)} := by
  simp [normalize, lowerCorner, translate]

theorem grown_normalized_mem {P : Finset GridPoint} (h : Grown P) :
    normalize P (growth_sound h).1 ∈ generatedLayer (P.card-1) := by
  induction h with
  | singleton p => simp [normalize_singleton, generatedLayer]
  | @insert Q a b hg ha hb hab ih =>
    have hc : 1 ≤ Q.card := Finset.card_pos.mpr ⟨a,ha⟩
    have hi := normalized_insert_successor (growth_sound hg).1 ha hb hab
    rw [Finset.card_insert_of_notMem hb]
    have he : Q.card+1-1 = (Q.card-1)+1 := by omega
    rw [he, generatedLayer]
    exact Finset.mem_biUnion.mpr ⟨_,ih,hi⟩

theorem connected_normalized_mem {P : Finset GridPoint} (h : EdgeConnected P) :
    normalize P h.1 ∈ generatedLayer (P.card-1) :=
  grown_normalized_mem (growth_complete h)

-- Supplied certificates can avoid evaluating generatedLayer: check local closure.
def layerClosureCheck (A B : Finset (Finset GridPoint)) : Bool :=
  decide (∀ Q ∈ A, ∀ S ∈ successors Q, S ∈ B)

theorem layerClosureCheck_sound (A B : Finset (Finset GridPoint))
    (h : layerClosureCheck A B = true) : ∀ Q ∈ A, successors Q ⊆ B :=
  of_decide_eq_true h

theorem certified_layers_cover (L : ℕ → Finset (Finset GridPoint)) (n : ℕ)
    (base : {(0,0)} ∈ L 0)
    (step : ∀ k < n, layerClosureCheck (L k) (L (k+1)) = true) :
    generatedLayer n ⊆ L n := by
  have aux : ∀ k, k ≤ n → generatedLayer k ⊆ L k := by
    intro k
    induction k with
    | zero => intro _ Q hQ; simpa [generatedLayer] using (Finset.mem_singleton.mp hQ ▸ base)
    | succ k ih =>
      intro hk Q hQ
      obtain ⟨P,hP,hPQ⟩ := Finset.mem_biUnion.mp hQ
      exact layerClosureCheck_sound _ _ (step k (by omega)) P (ih (by omega) hP) hPQ
  exact aux n le_rfl
end Polyomino57
