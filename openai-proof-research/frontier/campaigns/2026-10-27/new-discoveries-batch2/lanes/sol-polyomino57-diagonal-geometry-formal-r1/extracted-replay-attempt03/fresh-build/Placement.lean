import Diagonal
set_option autoImplicit false
namespace Polyomino57.Diagonal
open Polyomino57

theorem mem_square (p : GridPoint) : p ∈ square ↔
    -5 ≤ p.1 ∧ p.1 ≤ 5 ∧ -5 ≤ p.2 ∧ p.2 ≤ 5 := by
  simp [square,List.mem_flatMap]
  constructor
  · rintro ⟨x,hx,y,hy,hp⟩
    have h1 := congrArg Prod.fst hp
    have h2 := congrArg Prod.snd hp
    dsimp at h1 h2
    omega
  · intro h
    refine ⟨(p.1+5).toNat,by omega,(p.2+5).toNat,by omega,?_⟩
    apply Prod.ext <;> dsimp <;> omega

theorem mem_witness (p : GridPoint) : p ∈ witness ↔
    p.1.natAbs+p.2.natAbs ≤ 5 ∧ ¬ (p.1.natAbs = 2 ∧ p.2.natAbs = 2) := by
  rw [witness_literal]
  simp only [diamondMinusFour,Finset.mem_filter,mem_square]
  omega

theorem collision_cartesian {c p : GridPoint} (hc : Parity c.1 c.2) :
    Collision c p ↔
      (p.1-(inverse c.1 c.2).1).natAbs = 2 ∧
      (p.2-(inverse c.1 c.2).2).natAbs = 2 := by
  have h := inverse_coordinates hc
  dsimp [Collision,u,v,inverse] at *
  omega

theorem diamond_cartesian {c p : GridPoint} (hc : Parity c.1 c.2) :
    ((u p-c.1).natAbs ≤ 5 ∧ (v p-c.2).natAbs ≤ 5) ↔
    (p.1-(inverse c.1 c.2).1).natAbs +
      (p.2-(inverse c.1 c.2).2).natAbs ≤ 5 := by
  have hn := norm (p.1-(inverse c.1 c.2).1,p.2-(inverse c.1 c.2).2)
  have hi := inverse_coordinates hc
  dsimp [u,v] at *
  omega

theorem placement_iff {P : Finset GridPoint} {c : GridPoint} (hc : Parity c.1 c.2) :
    translate (-(inverse c.1 c.2).1,-(inverse c.1 c.2).2) P ⊆ witness ↔
      DiamondAt P c ∧ ∀ p ∈ P, ¬ Collision c p := by
  constructor
  · intro h
    have point : ∀ p ∈ P, (u p-c.1).natAbs ≤ 5 ∧
        (v p-c.2).natAbs ≤ 5 ∧ ¬ Collision c p := by
      intro p hp
      have hm := (mem_witness _).mp (h (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
      dsimp at hm
      have hd := (diamond_cartesian (p := p) hc).mpr (by simpa only [sub_eq_add_neg] using hm.1)
      have hh : ¬ Collision c p := by
        rw [collision_cartesian hc]; simpa only [sub_eq_add_neg] using hm.2
      exact ⟨hd.1,hd.2,hh⟩
    exact ⟨fun p hp => ⟨(point p hp).1,(point p hp).2.1⟩,fun p hp => (point p hp).2.2⟩
  · rintro ⟨hd,hh⟩ q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    apply (mem_witness _).mpr
    have h1 := (diamond_cartesian (p := p) hc).mp (hd p hp)
    have h2 := hh p hp
    rw [collision_cartesian hc] at h2
    simpa only [sub_eq_add_neg] using And.intro h1 h2

theorem groups_hits_iff {P : Finset GridPoint} {a b e : ℤ}
    (hP : P ⊆ domain a b e) : HitsAll P (groups a b e) ↔
      ExactExtrema P a b e ∧ ∀ c ∈ centers a b e, ∃ p ∈ P, Collision c p := by
  constructor
  · intro h
    refine ⟨(boundary_hits_iff hP).mp (fun g hg => h g (Finset.mem_union_left _ hg)),?_⟩
    intro c hc
    obtain ⟨p,hp,hpg⟩ := h (collisionGroup a b e c)
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c,hc,rfl⟩))
    exact ⟨p,hp,((mem_collisionGroup a b e c p).mp hpg).2⟩
  · rintro ⟨he,hc⟩ g hg
    rcases (mem_groups a b e g).mp hg with hb | ⟨c,hc',rfl⟩
    · exact (boundary_hits_iff hP).mpr he g hb
    · obtain ⟨p,hp,hcol⟩ := hc c hc'
      exact ⟨p,hp,(mem_collisionGroup a b e c p).mpr ⟨hP hp,hcol⟩⟩

-- All-center obstruction is exact, including an empty center list.
theorem obstruction_iff {P : Finset GridPoint} {a b e : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e)
    (hP : P ⊆ domain a b e) (hx : ExactExtrema P a b e) :
    HitsAll P (groups a b e) ↔ ¬ ∃ t : GridPoint, translate t P ⊆ witness := by
  rw [groups_hits_iff hP]
  constructor
  · rintro ⟨_,h⟩ ⟨t,ht⟩
    let c : GridPoint := (u (-t.1,-t.2),v (-t.1,-t.2))
    have hc : Parity c.1 c.2 := parity (-t.1,-t.2)
    have hi : inverse c.1 c.2 = (-t.1,-t.2) := inverse_signed (-t.1,-t.2)
    have hp : translate (-(inverse c.1 c.2).1,-(inverse c.1 c.2).2) P ⊆ witness := by
      simpa only [hi,neg_neg] using ht
    have hh := (placement_iff hc).mp hp
    have hcen := centers_complete hx hc hh.1
    obtain ⟨p,hp,hcol⟩ := h c hcen
    exact hh.2 p hp hcol
  · intro h
    refine ⟨hx,?_⟩
    intro c hc
    by_contra! hn
    have hs := centers_sufficient (fun p hp => (mem_domain ha hb he p).mp (hP hp)) hc
    have hp := (placement_iff ((mem_centers a b e c).mp hc).2.2.2.2).mpr ⟨hs,hn⟩
    exact h ⟨_,hp⟩

-- A finite-case assertion already yields every exact-extrema placement in that domain.
theorem domain_reduction {a b e : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e)
    (finiteCase : ∀ P : Finset GridPoint, P ⊆ domain a b e → EdgeConnected P →
      P.card = 11 → ¬ HitsAll P (groups a b e))
    {P : Finset GridPoint} (hP : P ⊆ domain a b e) (hc : EdgeConnected P)
    (hcard : P.card = 11) (hx : ExactExtrema P a b e) :
    ∃ t : GridPoint, translate t P ⊆ witness := by
  by_contra hn
  exact finiteCase P hP hc hcard ((obstruction_iff ha hb he hP hx).mpr hn)
end Polyomino57.Diagonal
