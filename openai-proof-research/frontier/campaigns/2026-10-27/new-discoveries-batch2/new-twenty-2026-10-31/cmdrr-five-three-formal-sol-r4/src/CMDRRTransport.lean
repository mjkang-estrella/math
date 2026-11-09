import CMDRROccurrence

open scoped Classical
namespace CMDRR
variable {M W N V O : Type}
namespace Game
/-- Bijective relabeling, preserving the unordered set of teams. -/
def relabel (e : M ≃ N) (f : W ≃ V) (g : Game M W) : Game N V where
  teams := g.teams.map (Equiv.prodCongr e f).toEmbedding
  two := by simpa using g.two
  men_distinct := by
    intro a ha b hb hn
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hb
    exact fun he => g.men_distinct x hx y hy
      (fun heq => hn (congrArg (Equiv.prodCongr e f) heq)) (e.injective he)
  women_distinct := by
    intro a ha b hb hn
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hb
    exact fun he => g.women_distinct x hx y hy
      (fun heq => hn (congrArg (Equiv.prodCongr e f) heq)) (f.injective he)

@[simp] theorem relabel_partners (e : M ≃ N) (f : W ≃ V) (g : Game M W) (m w) :
    (g.relabel e f).Partners (e m) (f w) ↔ g.Partners m w := by
  exact Finset.mem_map' (Equiv.prodCongr e f).toEmbedding (a := (m,w)) (s := g.teams)

@[simp] theorem relabel_men (e : M ≃ N) (f : W ≃ V) (g : Game M W) (m n) :
    (g.relabel e f).Men (e m) (e n) ↔ g.Men m n := by
  simp only [Men, relabel, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,hm,hn,hab⟩
    exact ⟨a,ha,b,hb,e.injective hm,e.injective hn,
      fun h => hab (congrArg (Equiv.prodCongr e f) h)⟩
  · rintro ⟨a,ha,b,hb,hm,hn,hab⟩
    exact ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,congrArg e hm,congrArg e hn,
      fun h => hab ((Equiv.prodCongr e f).injective h)⟩

@[simp] theorem relabel_women (e : M ≃ N) (f : W ≃ V) (g : Game M W) (w v) :
    (g.relabel e f).Women (f w) (f v) ↔ g.Women w v := by
  simp only [Women, relabel, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,hw,hv,hab⟩
    exact ⟨a,ha,b,hb,f.injective hw,f.injective hv,
      fun h => hab (congrArg (Equiv.prodCongr e f) h)⟩
  · rintro ⟨a,ha,b,hb,hw,hv,hab⟩
    exact ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,congrArg f hw,congrArg f hv,
      fun h => hab ((Equiv.prodCongr e f).injective h)⟩

@[simp] theorem relabel_opposes (e : M ≃ N) (f : W ≃ V) (g : Game M W) (m w) :
    (g.relabel e f).Opposes (e m) (f w) ↔ g.Opposes m w := by
  simp only [Opposes, relabel, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,hm,hw,hab⟩
    exact ⟨a,ha,b,hb,e.injective hm,f.injective hw,
      fun h => hab (congrArg (Equiv.prodCongr e f) h)⟩
  · rintro ⟨a,ha,b,hb,hm,hw,hab⟩
    exact ⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,congrArg e hm,congrArg f hw,
      fun h => hab ((Equiv.prodCongr e f).injective h)⟩

@[simp] theorem relabel_shares (e : M ≃ N) (f : W ≃ V) (g : Game M W) (m w) :
    (g.relabel e f).Shares (e m) (f w) ↔ g.Shares m w := by
  simp only [Shares, relabel, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨⟨_,⟨a,ha,rfl⟩,hm⟩,⟨_,⟨b,hb,rfl⟩,hw⟩⟩
    exact ⟨⟨a,ha,e.injective hm⟩,⟨b,hb,f.injective hw⟩⟩
  · rintro ⟨⟨a,ha,hm⟩,⟨b,hb,hw⟩⟩
    exact ⟨⟨_,⟨a,ha,rfl⟩,congrArg e hm⟩,⟨_,⟨b,hb,rfl⟩,congrArg f hw⟩⟩
end Game

namespace Matching
def relabel (s : Matching M W) (e : M ≃ N) (f : W ≃ V) : Matching N V where
  spouse m w := s.spouse (e.symm m) (f.symm w)
  right_unique := by
    intro m w v hw hv
    exact f.symm.injective (s.right_unique _ _ _ hw hv)
  left_unique := by
    intro m n w hm hn
    exact e.symm.injective (s.left_unique _ _ _ hm hn)

@[simp] theorem relabel_spouse (s : Matching M W) (e : M ≃ N) (f : W ≃ V) (m w) :
    (s.relabel e f).spouse (e m) (f w) ↔ s.spouse m w := by simp [relabel]

@[simp] theorem relabel_singleMan (s : Matching M W) (e : M ≃ N) (f : W ≃ V) (m) :
    (s.relabel e f).SingleMan (e m) ↔ s.SingleMan m := by
  simp only [SingleMan, relabel, Equiv.symm_apply_apply]
  exact not_congr (f.symm.surjective.exists.symm)

@[simp] theorem relabel_singleWoman (s : Matching M W) (e : M ≃ N) (f : W ≃ V) (w) :
    (s.relabel e f).SingleWoman (f w) ↔ s.SingleWoman w := by
  simp only [SingleWoman, relabel, Equiv.symm_apply_apply]
  apply not_congr
  constructor
  · rintro ⟨m,hm⟩; exact ⟨e.symm m,hm⟩
  · rintro ⟨m,hm⟩; exact ⟨e m,by simpa using hm⟩
end Matching

namespace Schedule
def relabel (d : Schedule M W O) (e : M ≃ N) (f : W ≃ V) : Schedule N V O :=
  ⟨fun o => (d.game o).relabel e f⟩
end Schedule

end CMDRR
