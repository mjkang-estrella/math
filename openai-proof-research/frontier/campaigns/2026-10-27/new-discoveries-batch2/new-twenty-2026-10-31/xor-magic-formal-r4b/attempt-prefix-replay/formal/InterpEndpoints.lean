import InterpAssembly
set_option linter.unusedSectionVars false
namespace XorMagic
variable {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {d n : ℕ}
namespace EdgeTransport
variable (T : EdgeTransport G) (F : MatchingDecomposition G d)
  (H : MatchingDecomposition Gᶜ (Fintype.card V-1-d))

include F H
theorem open_interval_exists (l : V ≃ Bits n) (hG : G.Connected) (hT : T.graph.Connected)
    (hm : ∀ p, ∑ q ∈ T.graph.neighborFinset p, label l q = 0)
    (hd : 1 ≤ d) (hcard : d+1 ≤ Fintype.card V) (hdo : Odd d)
    (q : ℕ) (hqo : Odd q) (hl : d ≤ q) (hu : q ≤ 4*Fintype.card V-4-d) :
    OpenExists (n+2) q := by
  obtain ⟨k,j,hk,hj,he⟩ := interp_open_interval (Fintype.card V) d q hd hcard hdo hqo hl hu
  refine ⟨V × Four,inferInstance,inferInstance,T.interpGraph F H k j hj,inferInstance,?_,
    T.interp_open F H k j hj l hG hT hm⟩
  rw [he]
  exact T.interpGraph_regular F H k j hk hj

theorem closed_interval_exists (l : V ≃ Bits n) (hG : G.Connected) (hT : T.graph.Connected)
    (hm : ∀ p, label l p + ∑ q ∈ T.graph.neighborFinset p, label l q = 0)
    (hd : 1 ≤ d) (hcard : d+1 ≤ Fintype.card V) (hde : Even d)
    (q : ℕ) (hqe : Even q) (hl : d ≤ q) (hu : q ≤ 4*Fintype.card V-4-d) :
    ClosedExists (n+2) q := by
  obtain ⟨k,j,hk,hj,he⟩ := interp_closed_interval (Fintype.card V) d q hd hcard hde hqe hl hu
  refine ⟨V × Four,inferInstance,inferInstance,T.interpGraph F H k j hj,inferInstance,?_,
    T.interp_closed F H k j hj l hG hT hm⟩
  rw [he]
  exact T.interpGraph_regular F H k j hk hj

noncomputable def complementMatching_exact (hcard : d+1 ≤ Fintype.card V) :
    MatchingDecomposition T.graphᶜ (Fintype.card (V × Four)-1-d) := by
  have he : 3+3*d+4*(Fintype.card V-1-d) = Fintype.card (V × Four)-1-d := by
    rw [Fintype.card_prod,show Fintype.card Four = 4 by decide]
    omega
  exact he ▸ T.complementMatching F H
end EdgeTransport
end XorMagic
