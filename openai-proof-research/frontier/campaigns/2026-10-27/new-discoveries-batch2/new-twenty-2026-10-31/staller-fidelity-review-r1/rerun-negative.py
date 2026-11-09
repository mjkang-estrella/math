from pathlib import Path
exec((Path(__file__).parent/'controls.py').read_text().split("(W/'Bridge.lean')")[0])
(W/'BadBound.lean').write_text('import Game\nexample : MathDB355140.check MathDB355140.graph ∅ Finset.univ true 3 = true := by rw [MathDB355140.three_check]; decide\n')
assert run('negative-false-bound-final',[str(B/'lean'),'-j1','-DwarningAsError=true','BadBound.lean'])!=0
