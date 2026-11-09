import InterpConnectivity
import InterpSums
import InterpolationArithmetic
set_option linter.unusedSectionVars false
namespace XorMagic
variable {V : Type} [Fintype V] [LinearOrder V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {d c n : ℕ}
theorem label_fibre_zero (l : V ≃ Bits n) (v : V) :
    ∑ x : Four, EdgeTransport.label l (v,x) = 0 := by
  change (∑ x : Four, bitsFourAddHom n (l v,x)) = 0
  rw [← map_sum]
  have he : (∑ x : Four, (l v,x)) = (0 : Bits n × Four) := by
    apply Prod.ext
    · simp only [← Finset.sum_apply, Prod.fst_sum]
      ext i
      simp only [Finset.sum_apply]
      have hc : ∀ a : ZMod 2, (∑ _ : Four, a) = 0 := by decide
      exact hc _
    · simpa only [Prod.snd_sum, Prod.snd_zero] using four_sum
  rw [he,map_zero]
namespace EdgeTransport
variable (T : EdgeTransport G) (F : MatchingDecomposition G d) (H : MatchingDecomposition Gᶜ c)

theorem interp_label_sum (k j : ℕ) (hj : j ≤ c) (l : V ≃ Bits n) (p : V × Four) :
    ∑ q ∈ (T.interpGraph F H k j hj).neighborFinset p, label l q =
      ∑ q ∈ T.graph.neighborFinset p, label l q :=
  T.interpGraph_sum F H k j hj (label l) (label_fibre_zero l) bits_add_self p

theorem interp_open (k j : ℕ) (hj : j ≤ c) (l : V ≃ Bits n)
    (hG : G.Connected) (hT : T.graph.Connected)
    (hm : ∀ p, ∑ q ∈ T.graph.neighborFinset p, label l q = 0) :
    OpenMagic (T.interpGraph F H k j hj) (n+2) := by
  refine ⟨T.interpGraph_connected F H k j hj hG hT, label l, ?_⟩
  intro p
  rw [T.interp_label_sum F H k j hj l,hm]

theorem interp_closed (k j : ℕ) (hj : j ≤ c) (l : V ≃ Bits n)
    (hG : G.Connected) (hT : T.graph.Connected)
    (hm : ∀ p, label l p + ∑ q ∈ T.graph.neighborFinset p, label l q = 0) :
    ClosedMagic (T.interpGraph F H k j hj) (n+2) := by
  refine ⟨T.interpGraph_connected F H k j hj hG hT, label l, ?_⟩
  intro p
  rw [T.interp_label_sum F H k j hj l,hm]
end EdgeTransport

theorem interp_parity_interval (m d q : ℕ) (hd : 1 ≤ d) (hm : d+1 ≤ m)
    (hl : d ≤ q) (hu : q ≤ 4*m-4-d) (hp : q % 2 = d % 2) :
    ∃ k j : ℕ, k ≤ d ∧ j ≤ m-1-d ∧ q = d+2*k+4*j := by
  have ht : q = d+2*((q-d)/2) := by omega
  obtain ⟨k,j,hk,hj,he⟩ := interpolation_degree d m ((q-d)/2) hd hm (by omega)
  exact ⟨k,j,hk,hj,by omega⟩

theorem interp_open_interval (m d q : ℕ) (hd : 1 ≤ d) (hm : d+1 ≤ m)
    (hdo : Odd d) (hqo : Odd q) (hl : d ≤ q) (hu : q ≤ 4*m-4-d) :
    ∃ k j : ℕ, k ≤ d ∧ j ≤ m-1-d ∧ q = d+2*k+4*j := by
  apply interp_parity_interval m d q hd hm hl hu
  obtain ⟨a,ha⟩ := hdo
  obtain ⟨b,hb⟩ := hqo
  omega

theorem interp_closed_interval (m d q : ℕ) (hd : 1 ≤ d) (hm : d+1 ≤ m)
    (hde : Even d) (hqe : Even q) (hl : d ≤ q) (hu : q ≤ 4*m-4-d) :
    ∃ k j : ℕ, k ≤ d ∧ j ≤ m-1-d ∧ q = d+2*k+4*j := by
  apply interp_parity_interval m d q hd hm hl hu
  obtain ⟨a,ha⟩ := hde
  obtain ⟨b,hb⟩ := hqe
  omega
end XorMagic
