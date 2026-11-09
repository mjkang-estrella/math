from pathlib import Path
import os,subprocess,resource,time,json,hashlib
R=Path(__file__).resolve().parent;W=R/'extracted';B=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin');P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
s=(R/'replay.py').read_text();exec(s[s.index('cpus='):s.index("assert run('strict-rebuild'")])
(W/'Bridge.lean').write_text('''import Game
set_option autoImplicit false
namespace Review
open MathDB355140
theorem number_le_iff {n : ℕ} (G : SimpleGraph (Fin n)) (turn : Bool) (B : ℕ) :
    winningNumber G turn ≤ (B : WithTop ℕ) ↔ Wins G ∅ Finset.univ turn B := by
  classical
  unfold winningNumber
  split_ifs with h
  · constructor
    · intro hle
      have hn : Nat.find h ≤ B := by exact_mod_cast hle
      exact (Nat.find_spec h).mono B hn
    · intro hw
      have hn := Nat.find_min' h hw
      exact_mod_cast hn
  · constructor
    · intro hle
      have ht : (B : WithTop ℕ) = ⊤ := top_le_iff.mp hle
      simp at ht
    · intro hw
      exact False.elim (h ⟨B,hw⟩)
example : check (⊥ : SimpleGraph (Fin 0)) ∅ ∅ false 5 = false := by decide +kernel
example : check (⊥ : SimpleGraph (Fin 1)) ∅ ∅ false 5 = false := by decide +kernel
example : check (⊥ : SimpleGraph (Fin 1)) ∅ Finset.univ true 1 = true := by decide +kernel
example : check (⊥ : SimpleGraph (Fin 1)) ∅ Finset.univ false 1 = false := by decide +kernel
example : (7+1)/2-2+1 = (3 : ℕ) := by decide
#print axioms number_le_iff
end Review
''')
run('bridges-and-edge-controls',[str(B/'lean'),'-j1','-DwarningAsError=true','Bridge.lean'])
(W/'BadBound.lean').write_text('import Game\nexample : MathDB355140.check MathDB355140.graph ∅ Finset.univ true 3 = true := by rw [MathDB355140.three_check]; decide\n')
assert run('negative-false-bound',[str(B/'lean'),'-j1','-DwarningAsError=true','BadBound.lean'])!=0
(W/'Corrupt.olean').write_bytes((W/'Game.olean').read_bytes()[:64])
assert run('negative-corrupt-module',[str(B/'leanchecker'),'Corrupt'])!=0
