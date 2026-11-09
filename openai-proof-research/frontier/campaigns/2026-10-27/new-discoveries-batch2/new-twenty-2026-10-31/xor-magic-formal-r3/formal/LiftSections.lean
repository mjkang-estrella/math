import LiftFibres
import AffineLift
namespace XorMagic.EdgeTransport
variable {V : Type} {G : SimpleGraph V} (T : EdgeTransport G)

theorem section_of_singleton (r : V × Four)
    (hs : ∀ v, (T.fibre r v).card = 1) :
    ∃ b : V → Four, ∀ u v, G.Adj u v → T.map u v (b u) = b v := by
  classical
  choose b hb using fun v => Finset.card_eq_one.mp (hs v)
  refine ⟨b, fun u v h => ?_⟩
  have hmem : b u ∈ T.fibre r u := by rw [hb u]; simp
  have ht := (T.fibre_transport r h (b u)).mp hmem
  simpa only [hb v, Finset.mem_singleton] using ht

theorem section_of_three (r : V × Four)
    (hs : ∀ v, (T.fibre r v).card = 3) :
    ∃ b : V → Four, ∀ u v, G.Adj u v → T.map u v (b u) = b v := by
  classical
  have hc : ∀ v, (T.fibre r v)ᶜ.card = 1 := by
    intro v
    rw [Finset.card_compl, hs v]
    decide
  choose b hb using fun v => Finset.card_eq_one.mp (hc v)
  refine ⟨b, fun u v h => ?_⟩
  have hn : b u ∉ T.fibre r u := by
    have hm : b u ∈ (T.fibre r u)ᶜ := by rw [hb u]; simp
    simpa using hm
  have ht : T.map u v (b u) ∉ T.fibre r v :=
    fun ht => hn ((T.fibre_transport r h _).mpr ht)
  have hm : T.map u v (b u) ∈ (T.fibre r v)ᶜ := by simpa using ht
  simpa only [hb v, Finset.mem_singleton] using hm
end XorMagic.EdgeTransport
namespace XorMagic

theorem scalar_zero : ∀ s, scalar s 0 = 0 := by decide
theorem four_add_self : ∀ x : Four, x+x = 0 := by decide

variable {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]

/-- The vertex-to-oriented-edge incidence map, using exactly the lift's scalar choices. -/
def incidenceD (s : OrientedEdge G → Fin 3) :
    (Fin m → Four) →+ (OrientedEdge G → Four) where
  toFun b e := b e.val.2 + scalar (s e) (b e.val.1)
  map_zero' := by funext e; simp only [Pi.zero_apply, scalar_zero, add_zero]
  map_add' b b' := by
    funext e
    simp only [Pi.add_apply, scalar_add]
    abel

theorem constants_in_range_of_section (s : OrientedEdge G → Fin 3)
    (c : OrientedEdge G → Four)
    (h : ∃ b : Fin m → Four, ∀ u v, G.Adj u v → (affineTransport G s c).map u v (b u) = b v) :
    c ∈ (incidenceD G s).range := by
  obtain ⟨b,hb⟩ := h
  refine ⟨b, ?_⟩
  funext e
  have h := hb e.val.1 e.val.2 e.property.2
  rw [forward_affine] at h
  have hh := congrArg (fun z => z + scalar (s e) (b e.val.1)) h
  have he : c e = b e.val.2 + scalar (s e) (b e.val.1) := by
    simpa [add_assoc, add_comm, add_left_comm, four_add_self] using hh
  exact he.symm

theorem constants_in_range_of_singleton (s : OrientedEdge G → Fin 3)
    (c : OrientedEdge G → Four) (r : Fin m × Four)
    (h : ∀ v, ((affineTransport G s c).fibre r v).card = 1) :
    c ∈ (incidenceD G s).range :=
  constants_in_range_of_section G s c ((affineTransport G s c).section_of_singleton r h)

theorem constants_in_range_of_three (s : OrientedEdge G → Fin 3)
    (c : OrientedEdge G → Four) (r : Fin m × Four)
    (h : ∀ v, ((affineTransport G s c).fibre r v).card = 3) :
    c ∈ (incidenceD G s).range :=
  constants_in_range_of_section G s c ((affineTransport G s c).section_of_three r h)
end XorMagic
