import CMDRRTransport

namespace CMDRR
variable {M W N V O : Type} [Fintype O]

namespace Schedule
variable (d : Schedule M W O) (e : M ≃ N) (f : W ≃ V)
@[simp] theorem relabel_partner_count (m w) :
    count (fun o => ((d.relabel e f).game o).Partners (e m) (f w)) =
      count (fun o => (d.game o).Partners m w) :=
  count_congr (fun o => (d.game o).relabel_partners e f m w)
@[simp] theorem relabel_opposition_count (m w) :
    count (fun o => ((d.relabel e f).game o).Opposes (e m) (f w)) =
      count (fun o => (d.game o).Opposes m w) :=
  count_congr (fun o => (d.game o).relabel_opposes e f m w)
@[simp] theorem relabel_men_count (m n) :
    count (fun o => ((d.relabel e f).game o).Men (e m) (e n)) =
      count (fun o => (d.game o).Men m n) :=
  count_congr (fun o => (d.game o).relabel_men e f m n)
@[simp] theorem relabel_women_count (w v) :
    count (fun o => ((d.relabel e f).game o).Women (f w) (f v)) =
      count (fun o => (d.game o).Women w v) :=
  count_congr (fun o => (d.game o).relabel_women e f w v)
end Schedule

namespace Source
variable {s : Matching M W} {d : Schedule M W O}
/-- Source conditions are preserved by arbitrary independent bijections of
male and female players. No numerical or cycle hypotheses are introduced. -/
theorem relabel (h : Source s d) (e : M ≃ N) (f : W ≃ V) :
    Source (s.relabel e f) (d.relabel e f) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro m w
    obtain ⟨m,rfl⟩ := e.surjective m
    obtain ⟨w,rfl⟩ := f.surjective w
    intro hs o
    simpa only [Schedule.relabel, Game.relabel_shares] using
      h.1 m w ((s.relabel_spouse e f m w).mp hs) o
  · intro m w
    obtain ⟨m,rfl⟩ := e.surjective m
    obtain ⟨w,rfl⟩ := f.surjective w
    simpa only [Matching.relabel_spouse, Schedule.relabel_partner_count,
      Schedule.relabel_opposition_count] using h.2.1 m w
  · intro m hm n hn
    obtain ⟨m,rfl⟩ := e.surjective m
    obtain ⟨n,rfl⟩ := e.surjective n
    obtain ⟨w,hw⟩ := hm
    obtain ⟨w,rfl⟩ := f.surjective w
    simpa only [Schedule.relabel_men_count] using
      h.2.2.1 m ⟨w,(s.relabel_spouse e f m w).mp hw⟩ n
        (fun he => hn (congrArg e he))
  · intro w hw v hv
    obtain ⟨w,rfl⟩ := f.surjective w
    obtain ⟨v,rfl⟩ := f.surjective v
    obtain ⟨m,hm⟩ := hw
    obtain ⟨m,rfl⟩ := e.surjective m
    simpa only [Schedule.relabel_women_count] using
      h.2.2.2.1 w ⟨m,(s.relabel_spouse e f m w).mp hm⟩ v
        (fun he => hv (congrArg f he))
  · intro m hm
    obtain ⟨m,rfl⟩ := e.surjective m
    obtain ⟨n,hn,hs,hc,ht⟩ := h.2.2.2.2.1 m
      ((s.relabel_singleMan e f m).mp hm)
    refine ⟨e n,(fun he => hn (e.injective he)),
      (s.relabel_singleMan e f n).mpr hs,?_,?_⟩
    · simpa only [Schedule.relabel_men_count] using hc
    · intro t htm htn
      obtain ⟨t,rfl⟩ := e.surjective t
      simpa only [Schedule.relabel_men_count] using
        ht t (fun he => htm (congrArg e he)) (fun he => htn (congrArg e he))
  · intro w hw
    obtain ⟨w,rfl⟩ := f.surjective w
    obtain ⟨v,hv,hs,hc,ht⟩ := h.2.2.2.2.2 w
      ((s.relabel_singleWoman e f w).mp hw)
    refine ⟨f v,(fun he => hv (f.injective he)),
      (s.relabel_singleWoman e f v).mpr hs,?_,?_⟩
    · simpa only [Schedule.relabel_women_count] using hc
    · intro t htw htv
      obtain ⟨t,rfl⟩ := f.surjective t
      simpa only [Schedule.relabel_women_count] using
        ht t (fun he => htw (congrArg f he)) (fun he => htv (congrArg f he))
end Source
end CMDRR
