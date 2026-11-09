from run import *
B='/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin'
P=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
F=R/'fresh/proof';E=os.environ.copy();E.update(LEAN_PATH=':'.join([str(F)]+[str(p) for p in P.glob('*/.lake/build/lib/lean')]),LEAN_NUM_THREADS='1',MALLOC_ARENA_MAX='2')
H='import MathDB378395\nset_option warningAsError true\n'
controls={
 'Wrong':(H+'example : MathDB378395.CollapsingConjecture := MathDB378395.Main.collapsing_conjecture_false\n',False),
 'Sorry':(H+'example : False := by sorry\n',False),
 'Axiom':(H+'axiom cheat : False\nopen Lean Elab Command in\nrun_cmd do\n let axs ← Lean.collectAxioms `cheat\n for ax in axs do\n  unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do\n   throwError "forbidden {ax}"\n',False),
 'OwnSanity':(H+'open MathDB378395 MathDB378395.Main MathDB378395.Cert\nexample : col (0,0,4) ∈ F := (col_mem_F_iff _).mpr (by decide +kernel)\nexample : col (0,0,0) ∉ F := by\n intro h\n have z := (col_mem_F_iff _).mp h\n have h1 : onCol ellZ (0,0,0) = 1 := by decide +kernel\n omega\nexample : Module.finrank ℝ (Submodule.span ℝ F) = 43 := finrank_span_F\nexample : ¬ CollapsingConjecture := collapsing_conjecture_false\n',True)}
s=(F/'MathDB378395.lean').read_text(); anchor='theorem ell_nonneg : ∀ c : Cell 4 4 5, 0 ≤ onCol ellZ c := by decide +kernel'
prefix=s[:s.index(anchor)+len(anchor)]+'\nend MathDB378395.Cert\n'
controls['GoodPrefix']=(prefix,True)
controls['Perturbed']=(prefix.replace('![0, 0, 0, 1]', '![0, 0, 0, -2]',1),False)
for label,(src,ok) in controls.items():
 (F/(label+'.lean')).write_text(src)
 code=run(label,[B+'/lean','-j1','-DwarningAsError=true',label+'.lean'],F,E)
 assert (code==0)==ok,(label,code)
(F/'Bad.olean').write_bytes(b'invalid olean\n')
assert run('BadOlean',[B+'/leanchecker','Bad'],F,E)!=0
