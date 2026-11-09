import Inputs026
namespace Percolation.Replay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_2625 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,false),(45,false),(61,false)]
theorem inp_2625 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2625 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2625 (by decide) v h
def cl_2626 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,false),(45,false),(61,false)]
theorem inp_2626 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2626 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2626 (by decide) v h
def cl_2627 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,false),(45,false),(61,false)]
theorem inp_2627 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2627 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2627 (by decide) v h
def cl_2628 : CNF.NClause := [(103,true),(41,true),(42,true),(43,false),(44,false),(45,false),(61,false)]
theorem inp_2628 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2628 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2628 (by decide) v h
def cl_2629 : CNF.NClause := [(103,true),(41,false),(42,false),(43,true),(44,false),(45,false),(61,false)]
theorem inp_2629 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2629 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2629 (by decide) v h
def cl_2630 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,false),(45,false),(61,false)]
theorem inp_2630 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2630 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2630 (by decide) v h
def cl_2631 : CNF.NClause := [(103,true),(41,false),(42,true),(43,true),(44,false),(45,false),(61,false)]
theorem inp_2631 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2631 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2631 (by decide) v h
def cl_2632 : CNF.NClause := [(103,true),(41,true),(42,true),(43,true),(44,false),(45,false),(61,false)]
theorem inp_2632 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2632 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2632 (by decide) v h
def cl_2641 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,false),(45,true),(61,false)]
theorem inp_2641 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2641 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2641 (by decide) v h
def cl_2657 : CNF.NClause := [(103,true),(41,false),(42,false),(43,false),(44,false),(45,false),(61,true)]
theorem inp_2657 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2657 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2657 (by decide) v h
def cl_2658 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,false),(45,false),(61,true)]
theorem inp_2658 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2658 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2658 (by decide) v h
def cl_2659 : CNF.NClause := [(103,true),(41,false),(42,true),(43,false),(44,false),(45,false),(61,true)]
theorem inp_2659 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2659 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2659 (by decide) v h
def cl_2660 : CNF.NClause := [(103,true),(41,true),(42,true),(43,false),(44,false),(45,false),(61,true)]
theorem inp_2660 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2660 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2660 (by decide) v h
def cl_2662 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,false),(45,false),(61,true)]
theorem inp_2662 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2662 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2662 (by decide) v h
def cl_2666 : CNF.NClause := [(103,true),(41,true),(42,false),(43,false),(44,true),(45,false),(61,true)]
theorem inp_2666 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2666 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2666 (by decide) v h
def cl_2670 : CNF.NClause := [(103,true),(41,true),(42,false),(43,true),(44,true),(45,false),(61,true)]
theorem inp_2670 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2670 := by
  exact input_gate (activationGate5 SatVar.x (.j 10) 10) (activationX_mem 10) cl_2670 (by decide) v h
def cl_2691 : CNF.NClause := [(104,true),(35,false),(38,true),(41,false),(49,false),(52,false),(59,false)]
theorem inp_2691 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2691 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2691 (by decide) v h
def cl_2692 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,false),(52,false),(59,false)]
theorem inp_2692 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2692 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2692 (by decide) v h
def cl_2695 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,false),(52,false),(59,false)]
theorem inp_2695 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2695 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2695 (by decide) v h
def cl_2696 : CNF.NClause := [(104,true),(35,true),(38,true),(41,true),(49,false),(52,false),(59,false)]
theorem inp_2696 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2696 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2696 (by decide) v h
def cl_2700 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,true),(52,false),(59,false)]
theorem inp_2700 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2700 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2700 (by decide) v h
def cl_2704 : CNF.NClause := [(104,true),(35,true),(38,true),(41,true),(49,true),(52,false),(59,false)]
theorem inp_2704 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2704 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2704 (by decide) v h
def cl_2708 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,false),(52,true),(59,false)]
theorem inp_2708 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2708 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2708 (by decide) v h
def cl_2711 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,false),(52,true),(59,false)]
theorem inp_2711 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2711 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2711 (by decide) v h
def cl_2712 : CNF.NClause := [(104,true),(35,true),(38,true),(41,true),(49,false),(52,true),(59,false)]
theorem inp_2712 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2712 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2712 (by decide) v h
def cl_2716 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,true),(52,true),(59,false)]
theorem inp_2716 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2716 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2716 (by decide) v h
def cl_2724 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,false),(52,false),(59,true)]
theorem inp_2724 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2724 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2724 (by decide) v h
def cl_2727 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,false),(52,false),(59,true)]
theorem inp_2727 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2727 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2727 (by decide) v h
def cl_2728 : CNF.NClause := [(104,true),(35,true),(38,true),(41,true),(49,false),(52,false),(59,true)]
theorem inp_2728 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2728 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2728 (by decide) v h
def cl_2732 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,true),(52,false),(59,true)]
theorem inp_2732 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2732 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2732 (by decide) v h
def cl_2740 : CNF.NClause := [(104,true),(35,true),(38,true),(41,false),(49,false),(52,true),(59,true)]
theorem inp_2740 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2740 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2740 (by decide) v h
def cl_2741 : CNF.NClause := [(104,true),(35,false),(38,false),(41,true),(49,false),(52,true),(59,true)]
theorem inp_2741 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2741 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2741 (by decide) v h
def cl_2743 : CNF.NClause := [(104,true),(35,false),(38,true),(41,true),(49,false),(52,true),(59,true)]
theorem inp_2743 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2743 := by
  exact input_gate (activationGate5 SatVar.x (.j 11) 11) (activationX_mem 11) cl_2743 (by decide) v h
def cl_2753 : CNF.NClause := [(105,true),(33,false),(37,false),(41,false),(50,false),(54,false),(60,false)]
theorem inp_2753 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2753 := by
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2753 (by decide) v h
def cl_2755 : CNF.NClause := [(105,true),(33,false),(37,true),(41,false),(50,false),(54,false),(60,false)]
theorem inp_2755 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2755 := by
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2755 (by decide) v h
def cl_2767 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,true),(54,false),(60,false)]
theorem inp_2767 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2767 := by
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2767 (by decide) v h
def cl_2799 : CNF.NClause := [(105,true),(33,false),(37,true),(41,true),(50,true),(54,false),(60,true)]
theorem inp_2799 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2799 := by
  exact input_gate (activationGate5 SatVar.x (.j 12) 12) (activationX_mem 12) cl_2799 (by decide) v h
def cl_2817 : CNF.NClause := [(106,true),(34,false),(40,false),(41,false),(47,false),(53,false),(57,false)]
theorem inp_2817 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2817 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2817 (by decide) v h
def cl_2818 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,false),(53,false),(57,false)]
theorem inp_2818 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2818 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2818 (by decide) v h
def cl_2819 : CNF.NClause := [(106,true),(34,false),(40,true),(41,false),(47,false),(53,false),(57,false)]
theorem inp_2819 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2819 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2819 (by decide) v h
def cl_2821 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,false),(53,false),(57,false)]
theorem inp_2821 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2821 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2821 (by decide) v h
def cl_2823 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,false),(53,false),(57,false)]
theorem inp_2823 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2823 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2823 (by decide) v h
def cl_2826 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,true),(53,false),(57,false)]
theorem inp_2826 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2826 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2826 (by decide) v h
def cl_2829 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,true),(53,false),(57,false)]
theorem inp_2829 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2829 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2829 (by decide) v h
def cl_2830 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,true),(53,false),(57,false)]
theorem inp_2830 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2830 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2830 (by decide) v h
def cl_2842 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,true),(53,true),(57,false)]
theorem inp_2842 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2842 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2842 (by decide) v h
def cl_2845 : CNF.NClause := [(106,true),(34,false),(40,false),(41,true),(47,true),(53,true),(57,false)]
theorem inp_2845 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2845 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2845 (by decide) v h
def cl_2846 : CNF.NClause := [(106,true),(34,true),(40,false),(41,true),(47,true),(53,true),(57,false)]
theorem inp_2846 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2846 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2846 (by decide) v h
def cl_2855 : CNF.NClause := [(106,true),(34,false),(40,true),(41,true),(47,false),(53,false),(57,true)]
theorem inp_2855 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2855 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2855 (by decide) v h
def cl_2858 : CNF.NClause := [(106,true),(34,true),(40,false),(41,false),(47,true),(53,false),(57,true)]
theorem inp_2858 (v : SatVar → Bool) (h : ∀ d ∈ inputCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_2858 := by
  exact input_gate (activationGate5 SatVar.x (.j 13) 13) (activationX_mem 13) cl_2858 (by decide) v h
end Percolation.Replay
