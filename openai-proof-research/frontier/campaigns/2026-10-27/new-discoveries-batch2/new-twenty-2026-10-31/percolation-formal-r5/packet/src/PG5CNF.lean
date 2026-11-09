import FiniteSystem
import TruthTableCNF
namespace Percolation
set_option autoImplicit false
set_option linter.unusedSimpArgs false

inductive SatVar where
  | a : Points 5 → SatVar
  | x : Points 5 → SatVar
  | i : Points 5 → SatVar
  | j : Points 5 → SatVar
  | b : Points 5 → Points 5 → SatVar

def assignment5 (a x i j : Infection 5) (b : Points 5 → Infection 5) : SatVar → Bool :=
  fun z => match z with
  | .a p => a p
  | .x p => x p
  | .i p => i p
  | .j p => j p
  | .b v p => b v p

def pts5 : List (Points 5) := List.finRange 31
def onLine5 (l : Points 5) := pts5.filter (fun p => PG5.inc p l)
def through5 (p : Points 5) := pts5.filter (fun l => PG5.inc p l)

theorem onLine_count5 (a : Infection 5) (l : Points 5) :
    (onLine5 l).countP a = countOn PG5 a l := by
  simp only [List.countP_map, List.countP_eq_length_filter, onLine5, List.filter_filter,
    countOn, card, pts5, Function.comp_def]

theorem through_any5 (i : Infection 5) (p : Points 5) :
    (through5 p).any i = pts5.any (fun l => PG5.inc p l && i l) := by
  simp only [through5, List.any_filter]

abbrev Gate5 := List SatVar × (List Bool → Bool)
def activationGate5 (src : Points 5 → SatVar) (out : SatVar) (l : Points 5) : Gate5 :=
  (out :: (onLine5 l).map src,
    fun bs => bs.headD false == decide (5 ≤ bs.tail.countP id))
def spreadGate5 (p : Points 5) : Gate5 :=
  (.x p :: .a p :: (through5 p).map SatVar.i,
    fun bs => bs.headD false == (bs.tail.headD false || bs.tail.tail.any id))
def finalGate5 (p : Points 5) : Gate5 :=
  (.x p :: (through5 p).map SatVar.j, fun bs => bs.any id)
def closedGate5 (v l : Points 5) : Gate5 :=
  ((onLine5 l).map (SatVar.b v), fun bs => !(decide (bs.countP id = 5)))

def gates5 : List Gate5 :=
  (pts5.map (fun l => activationGate5 SatVar.a (.i l) l)) ++
  (pts5.map (fun l => activationGate5 SatVar.x (.j l) l)) ++
  (pts5.map spreadGate5) ++ (pts5.map finalGate5) ++
  pts5.flatMap (fun v => pts5.map (closedGate5 v))

theorem closed_count5 (b : Infection 5) (hf : step PG5 5 b = b) (l : Points 5) :
    countOn PG5 b l ≠ 5 := by
  intro he
  have hh : ∀ p ∈ onLine5 l, b p = true := by
    intro p hp
    have hi := (List.mem_filter.mp hp).2
    have hs : step PG5 5 b p = true := by
      simp only [step, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨l, by simp, hi, by omega⟩
    rwa [hf] at hs
  have hlen : ((onLine5 l).filter b).length = (onLine5 l).length := by
    rw [List.filter_eq_self.mpr hh]
  have hc : countOn PG5 b l = 6 := by
    rw [← onLine_count5]
    simp only [List.countP_eq_length_filter]
    change ((onLine5 l).filter b).length = 6
    rw [hlen]
    exact PG5.line_degree l
  omega

theorem gates5_sound (a : Infection 5) (_hm : Minimal PG5 5 a) (ht : TimeIs PG5 5 a 2) :
    let x := step PG5 5 a
    let b := fun v => rounds PG5 5 (erase a v) 31
    let val := assignment5 a x (active5 a) (active5 x) b
    ∀ g ∈ gates5, g.2 (g.1.map val) = true := by
  dsimp only
  intro g hg
  simp only [gates5, List.mem_append, List.mem_map, List.mem_flatMap] at hg
  rcases hg with (((⟨l, _, rfl⟩ | ⟨l, _, rfl⟩) | ⟨p, _, rfl⟩) | ⟨p, _, rfl⟩) | ⟨v, _, l, _, rfl⟩
  · simp [activationGate5, assignment5, List.map_map, Function.comp_def, onLine_count5, active5]
  · simp [activationGate5, assignment5, List.map_map, Function.comp_def, onLine_count5, active5]
  · simp [spreadGate5, assignment5, List.map_map, Function.comp_def, through_any5, step, pts5, active5]
  · have h := ht.1 p
    change step PG5 5 (step PG5 5 a) p = true at h
    simpa [finalGate5, assignment5, List.map_map, Function.comp_def, through_any5,
      step, pts5, active5] using h
  · have hc := closed_count5 (rounds PG5 5 (erase a v) 31) (closure_stable PG5 5 _) l
    simp [closedGate5, assignment5, List.map_map, Function.comp_def, onLine_count5, hc]

def gateCNF5 : List (CNF.Clause SatVar) := gates5.flatMap (fun g => CNF.gate g.1 g.2)

theorem witness_satisfies_gateCNF5 (a : Infection 5)
    (hm : Minimal PG5 5 a) (ht : TimeIs PG5 5 a 2) :
    let x := step PG5 5 a
    let val := assignment5 a x (active5 a) (active5 x)
      (fun v => rounds PG5 5 (erase a v) 31)
    ∀ c ∈ gateCNF5, CNF.Holds val c := by
  dsimp only
  intro c hc
  obtain ⟨g, hg, hc⟩ := List.mem_flatMap.mp hc
  exact CNF.gate_sound _ g.1 g.2 (gates5_sound a hm ht g hg) c hc

def omitClause5 (v : Points 5) : CNF.Clause SatVar := [(.a v, true), (.b v v, true)]
def containClause5 (v p : Points 5) : CNF.Clause SatVar :=
  [(.a v, true), (.a p, true), (.b v p, false)]
def directCNF5 : List (CNF.Clause SatVar) :=
  [pts5.map (fun p => (SatVar.x p, true))] ++
  pts5.map omitClause5 ++
  pts5.flatMap (fun v => (pts5.filter (fun p => decide (p ≠ v))).map (containClause5 v))
def inputCNF5 := gateCNF5 ++ directCNF5

theorem witness_satisfies_directCNF5 (a : Infection 5)
    (hm : Minimal PG5 5 a) (ht : TimeIs PG5 5 a 2) :
    let x := step PG5 5 a
    let val := assignment5 a x (active5 a) (active5 x)
      (fun v => rounds PG5 5 (erase a v) 31)
    ∀ c ∈ directCNF5, CNF.Holds val c := by
  dsimp only
  intro c hc
  simp only [directCNF5, List.mem_append, List.mem_singleton, List.mem_map, List.mem_flatMap] at hc
  rcases hc with (rfl | ⟨v, _, rfl⟩) | ⟨v, _, p, hp, rfl⟩
  · have hn := ht.2 1 (by decide)
    have he : ∃ p, step PG5 5 a p ≠ true := by
      apply Classical.byContradiction
      intro hh
      apply hn
      intro p
      apply Classical.byContradiction
      intro hp
      exact hh ⟨p, hp⟩
    obtain ⟨p, hp⟩ := he
    exact ⟨(.x p, true), List.mem_map.mpr ⟨p, by simp [pts5], rfl⟩, hp⟩
  · by_cases hv : a v = true
    · have hs := (minimal_deletion_separator PG5 5 a hm v hv).2.2
      exact ⟨(.b v v, true), by simp [omitClause5], by simp [assignment5, hs]⟩
    · exact ⟨(.a v, true), by simp [omitClause5], hv⟩
  · have hpv : p ≠ v := of_decide_eq_true (List.mem_filter.mp hp).2
    by_cases hv : a v = true
    · by_cases ha : a p = true
      · have hs := (minimal_deletion_separator PG5 5 a hm v hv).1 p hpv ha
        exact ⟨(.b v p, false), by simp [containClause5], by simp [assignment5, hs]⟩
      · exact ⟨(.a p, true), by simp [containClause5], ha⟩
    · exact ⟨(.a v, true), by simp [containClause5], hv⟩

theorem witness_satisfies_inputCNF5 (a : Infection 5)
    (hm : Minimal PG5 5 a) (ht : TimeIs PG5 5 a 2) :
    let x := step PG5 5 a
    let val := assignment5 a x (active5 a) (active5 x)
      (fun v => rounds PG5 5 (erase a v) 31)
    ∀ c ∈ inputCNF5, CNF.Holds val c := by
  dsimp only
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact witness_satisfies_gateCNF5 a hm ht c hc
  · exact witness_satisfies_directCNF5 a hm ht c hc

def GeneratedCNFUnsat5 : Prop :=
  ¬ ∃ val : SatVar → Bool, ∀ c ∈ inputCNF5, CNF.Holds val c

theorem no_minimal_of_generated_unsat5 (h : GeneratedCNFUnsat5) : NoMinimalTwoRound5 := by
  rintro ⟨a, hm, ht⟩
  exact h ⟨_, witness_satisfies_inputCNF5 a hm ht⟩

theorem not_conjecture20_generated (h : GeneratedCNFUnsat5) : ¬ Conjecture20 :=
  not_conjecture20 (no_minimal_of_generated_unsat5 h)

#print axioms witness_satisfies_inputCNF5
#print axioms not_conjecture20_generated
end Percolation
