import CountR6Bridge
noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace ChanLevine.Round7T
open Round6
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- A closed binary state word, indexed at each transfer factor. -/
abbrev StateWord (n : ℕ) := ZMod n → Fin 2

def Admissible (q : StateWord n) : Prop :=
  ∀ k, q k = 1 → q (k+1) = 0

/-- The excursion beginning at k selects the oriented edge (k,k+1). -/
def selected (q : StateWord n) : Finset (ZMod n) :=
  Finset.univ.filter (fun k => q (k+1) = 1)

@[simp] theorem mem_selected (q : StateWord n) (k : ZMod n) :
    k ∈ selected q ↔ q (k+1) = 1 := by simp [selected]

theorem selected_matching (q : StateWord n) (hq : Admissible q) :
    Matching (selected q) := by
  intro k hk hn
  have ha := hq (k+1) (mem_selected q k |>.mp hk)
  have hb := mem_selected q (k+1) |>.mp hn
  rw [ha] at hb
  exact Fin.zero_ne_one hb

/-- State 1 is exactly the right endpoint of a chosen edge. -/
def matchingWord (s : Finset (ZMod n)) : StateWord n :=
  fun k => if k ∈ rightEnds s then 1 else 0

omit [NeZero n] in
@[simp] theorem mem_rightEnds (s : Finset (ZMod n)) (k : ZMod n) :
    k ∈ rightEnds s ↔ k-1 ∈ s := by
  simp only [rightEnds, Finset.mem_image]
  constructor
  · rintro ⟨j,hj,h⟩
    have : j = k-1 := by rw [← h]; abel
    simpa [← this] using hj
  · intro h
    exact ⟨k-1,h,by abel⟩

@[simp] theorem matchingWord_selected (s : Finset (ZMod n)) :
    selected (matchingWord s) = s := by
  ext k
  simp [matchingWord]

@[simp] theorem selected_matchingWord (q : StateWord n) :
    matchingWord (selected q) = q := by
  funext k
  have hk : q k = 0 ∨ q k = 1 := by omega
  rcases hk with hk | hk <;> simp [matchingWord, hk]

theorem matchingWord_admissible (s : Finset (ZMod n)) (hs : Matching s) :
    Admissible (matchingWord s) := by
  intro k hk
  have hmem : k-1 ∈ s := by
    by_contra h
    simp [matchingWord,h] at hk
  have hnot : k ∉ s := by
    simpa using hs (k-1) hmem
  simp [matchingWord,hnot]

/-- A genuine inverse pair; wrap excursions and perfect matchings need no exceptions. -/
def stateMatchingEquiv : {q : StateWord n // Admissible q} ≃
    {s : Finset (ZMod n) // Matching s} where
  toFun q := ⟨selected q.val, selected_matching q.val q.property⟩
  invFun s := ⟨matchingWord s.val, matchingWord_admissible s.val s.property⟩
  left_inv q := Subtype.ext (selected_matchingWord q.val)
  right_inv s := Subtype.ext (matchingWord_selected s.val)
end ChanLevine.Round7T
