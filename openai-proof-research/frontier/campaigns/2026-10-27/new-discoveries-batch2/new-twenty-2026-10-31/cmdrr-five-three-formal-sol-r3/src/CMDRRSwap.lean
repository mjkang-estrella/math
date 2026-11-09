import CMDRRSourceTransport

open scoped Classical
namespace CMDRR
variable {M W O : Type}
namespace Game
def swap (g : Game M W) : Game W M where
  teams := g.teams.map (Equiv.prodComm M W).toEmbedding
  two := by simpa using g.two
  men_distinct := by
    intro a ha b hb hn
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hb
    exact g.women_distinct x hx y hy (fun he => hn (congrArg Prod.swap he))
  women_distinct := by
    intro a ha b hb hn
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hb
    exact g.men_distinct x hx y hy (fun he => hn (congrArg Prod.swap he))

@[simp] theorem swap_partners (g : Game M W) (m w) :
    g.swap.Partners w m ↔ g.Partners m w :=
  Finset.mem_map' (Equiv.prodComm M W).toEmbedding (a := (m,w)) (s := g.teams)

@[simp] theorem swap_men (g : Game M W) (w v) :
    g.swap.Men w v ↔ g.Women w v := by
  simp only [Men, Women, swap, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,hw,hv,hab⟩
    exact ⟨a,ha,b,hb,hw,hv,fun he => hab (congrArg Prod.swap he)⟩
  · rintro ⟨a,ha,b,hb,hw,hv,hab⟩
    exact ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,hw,hv,
      fun he => hab ((Equiv.prodComm M W).injective he)⟩

@[simp] theorem swap_women (g : Game M W) (m n) :
    g.swap.Women m n ↔ g.Men m n := by
  simp only [Men, Women, swap, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,hm,hn,hab⟩
    exact ⟨a,ha,b,hb,hm,hn,fun he => hab (congrArg Prod.swap he)⟩
  · rintro ⟨a,ha,b,hb,hm,hn,hab⟩
    exact ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,hm,hn,
      fun he => hab ((Equiv.prodComm M W).injective he)⟩

@[simp] theorem swap_opposes (g : Game M W) (m w) :
    g.swap.Opposes w m ↔ g.Opposes m w := by
  simp only [Opposes, swap, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,hw,hm,hab⟩
    exact ⟨b,hb,a,ha,hm,hw,fun he => hab (congrArg Prod.swap he.symm)⟩
  · rintro ⟨a,ha,b,hb,hm,hw,hab⟩
    exact ⟨_,⟨b,hb,rfl⟩,_,⟨a,ha,rfl⟩,hw,hm,
      fun he => hab ((Equiv.prodComm M W).injective he).symm⟩

@[simp] theorem swap_shares (g : Game M W) (m w) :
    g.swap.Shares w m ↔ g.Shares m w := by
  simp only [Shares, swap, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨⟨_,⟨a,ha,rfl⟩,hw⟩,⟨_,⟨b,hb,rfl⟩,hm⟩⟩
    exact ⟨⟨b,hb,hm⟩,⟨a,ha,hw⟩⟩
  · rintro ⟨⟨a,ha,hm⟩,⟨b,hb,hw⟩⟩
    exact ⟨⟨_,⟨b,hb,rfl⟩,hw⟩,⟨_,⟨a,ha,rfl⟩,hm⟩⟩
end Game

namespace Matching
def swap (s : Matching M W) : Matching W M where
  spouse w m := s.spouse m w
  right_unique _ _ _ := s.left_unique _ _ _
  left_unique _ _ _ := s.right_unique _ _ _
end Matching
namespace Schedule
def swap (d : Schedule M W O) : Schedule W M O := ⟨fun o => (d.game o).swap⟩
end Schedule

namespace Source
variable [Fintype O] {s : Matching M W} {d : Schedule M W O}
 theorem swap (h : Source s d) : Source s.swap d.swap := by
  have hp (m w) : count (fun o => (d.swap.game o).Partners w m) =
      count (fun o => (d.game o).Partners m w) := count_congr (fun o => Game.swap_partners _ _ _)
  have ho (m w) : count (fun o => (d.swap.game o).Opposes w m) =
      count (fun o => (d.game o).Opposes m w) := count_congr (fun o => Game.swap_opposes _ _ _)
  have hm (m n) : count (fun o => (d.swap.game o).Women m n) =
      count (fun o => (d.game o).Men m n) := count_congr (fun o => Game.swap_women _ _ _)
  have hw (w v) : count (fun o => (d.swap.game o).Men w v) =
      count (fun o => (d.game o).Women w v) := count_congr (fun o => Game.swap_men _ _ _)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro w m hs o
    exact fun he => h.1 m w hs o ((d.game o).swap_shares m w |>.mp he)
  · intro w m hs
    rw [hp,ho]
    exact h.2.1 m w hs
  · intro w hs v hv
    rw [hw]
    exact h.2.2.2.1 w hs v hv
  · intro m hs n hn
    rw [hm]
    exact h.2.2.1 m hs n hn
  · intro w hs
    obtain ⟨v,hv,hvs,hc,ht⟩ := h.2.2.2.2.2 w hs
    refine ⟨v,hv,hvs,?_,?_⟩
    · rw [hw]; exact hc
    · intro t htw htv; rw [hw]; exact ht t htw htv
  · intro m hs
    obtain ⟨n,hn,hns,hc,ht⟩ := h.2.2.2.2.1 m hs
    refine ⟨n,hn,hns,?_,?_⟩
    · rw [hm]; exact hc
    · intro t htm htn; rw [hm]; exact ht t htm htn
end Source
end CMDRR
