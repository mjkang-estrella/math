import SemFinal3
import Cardinality
namespace ChanLevine.Sem5
variable {n : ℕ} [NeZero n]

/-- Positive sink execution: vertex zero is never fired. -/
def SinkBefore (a b : Config n) : Prop :=
  ∃ w, w ≠ [] ∧ (0 : ZMod n) ∉ w ∧ LegalWord a.lift w b.lift

omit [NeZero n] in
theorem sinkBefore_trans {a b c : Config n} (hab : SinkBefore a b)
    (hbc : SinkBefore b c) : SinkBefore a c := by
  obtain ⟨u, hu, hz, hl⟩ := hab
  obtain ⟨v, _, hz', hl'⟩ := hbc
  exact ⟨u++v, by intro hh; apply hu; exact (List.append_eq_nil_iff.mp hh).1, by simp_all, Sem3.word_append hl hl'⟩

theorem sinkBefore_irrefl (hn : 3 ≤ n) (a : Config n) : ¬ SinkBefore a a := by
  rintro ⟨w, hw, hz, hl⟩
  exact hz (Sem3.closedCoverage n hn a.lift w hw hl 0)

/-- Finite fixed-level sink dynamics is acyclic, hence terminating. -/
theorem sink_terminal_exists (hn : 3 ≤ n) (c : Config n) :
    ∃ d : Config n, Reach c.lift d.lift ∧ (∀ v, v ≠ 0 → d.x v = 0) ∧ d.q 0 = c.q 0 := by
  classical
  let A := {d : Config n // chipLevel d = chipLevel c}
  let r : A → A → Prop := fun b a => SinkBefore a.val b.val
  have : IsTrans A r := ⟨fun _ _ _ hab hbc => sinkBefore_trans hbc hab⟩
  have : Std.Irrefl r := ⟨fun a => sinkBefore_irrefl hn a.val⟩
  have wf : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  have hall : ∀ a : A, ∃ d : Config n, Reach a.val.lift d.lift ∧
      (∀ v, v ≠ 0 → d.x v = 0) ∧ d.q 0 = a.val.q 0 := by
    intro a
    induction a using wf.induction with
    | h a ih =>
      by_cases ht : ∀ v, v ≠ 0 → a.val.x v = 0
      · exact ⟨a.val, .refl, ht, rfl⟩
      · push Not at ht
        obtain ⟨v, hv, hx⟩ := ht
        have hp : 0 < a.val.x v := Nat.pos_of_ne_zero hx
        let b := a.val.fire v
        have hl : b.lift = fire a.val.lift v := Config.lift_fire _ _ hp
        have hb : chipLevel b = chipLevel c := by
          have hh := level_fire a.val.lift v
          rw [← hl, level_lift, level_lift] at hh
          exact (Int.ofNat_inj.mp hh).trans a.property
        have hr : r ⟨b,hb⟩ a := by
          refine ⟨[v], by simp, by simpa using Ne.symm hv, ?_⟩
          rw [hl]
          exact .cons v (by change 0 < (a.val.x v : ℤ); omega) (.nil _)
        obtain ⟨d, hd, ht, hq⟩ := ih ⟨b,hb⟩ hr
        refine ⟨d, (Relation.ReflTransGen.single ⟨v, by change 0 < (a.val.x v : ℤ); omega, hl⟩).trans hd, ht, ?_⟩
        exact hq.trans (by simp [b, Config.fire, Ne.symm hv])
  exact hall ⟨c,rfl⟩

/-- Recurrence propagates along every forward legal execution. -/
theorem recurrent_forward (hn : 3 ≤ n) {a b : SignedConfig n}
    (ha : Recurrent a) (hab : Reach a b) : Recurrent b := by
  obtain ⟨w, hw, hl⟩ := recurrent_closed_word ha
  obtain ⟨_, v, hv, hvl⟩ := Sem3.closed_reach hn hab ⟨w,hw,hl⟩
  exact Sem3.closedWordRecurrence n hn b v hv hvl

/-- Every recurrent configuration reaches a recurrent sink state with rotor zero right. -/
theorem sink_right_exists (hn : 3 ≤ n) (c : Config n) (hc : NatRecurrent c) :
    ∃ d : Config n, Reach c.lift d.lift ∧ NatRecurrent d ∧
      (∀ v, v ≠ 0 → d.x v = 0) ∧ d.q 0 = true := by
  obtain ⟨d, hd, ht, hq⟩ := sink_terminal_exists hn c
  have hdr : NatRecurrent d := recurrent_forward hn hc hd
  cases he : d.q 0 with
  | true => exact ⟨d,hd,hdr,ht,he⟩
  | false =>
    have hp : 0 < d.x 0 := by
      obtain ⟨e,v,hv,_⟩ := hdr.1
      by_cases hz : v = 0
      · subst v; change 0 < (d.x 0 : ℤ) at hv; omega
      · have hh := ht v hz
        change 0 < (d.x v : ℤ) at hv
        simp [hh] at hv
    let e := d.fire 0
    have hel : e.lift = fire d.lift 0 := Config.lift_fire _ _ hp
    have hde : Reach d.lift e.lift := Relation.ReflTransGen.single ⟨0, by change 0 < (d.x 0 : ℤ); omega, hel⟩
    obtain ⟨f, hef, hft, hfq⟩ := sink_terminal_exists hn e
    refine ⟨f, hd.trans (hde.trans hef), recurrent_forward hn hdr (hde.trans hef), hft, ?_⟩
    simpa [e, Config.fire, he] using hfq
end ChanLevine.Sem5
