from pathlib import Path
root=Path('work/lean')
mods=[]
for a,p,q in [(3,2,6),(6,3,4)]:
 for l in range(11):
  names=[]
  for b in range(11):
   name=f'ChainFirst{a}_{l}_{b}'; mods.append(name); names.append(name)
   cond=f'((({b}:V) = 1 ∧ c = 8) ∨ ({b} = 8 ∧ c = 1)) ∧ (({l} = {p} ∧ m = {q}) ∨ ({l} = {q} ∧ m = {p}))'
   (root/f'{name}.lean').write_text(f'''import ChainBool
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
theorem check{a}_{l}_{b} : all2 (fun c m => !fastFits (first {a} {b} c {l} m) || decide ({cond})) = true := by decide +kernel
theorem case{a}_{l}_{b} (c m : V) (hf : Fits (first {a} {b} c {l} m)) : {cond} := by
  have hh := all2_sound check{a}_{l}_{b} c m
  have ht := (fastFits_iff _).mpr hf
  simpa only [ht, Bool.not_true, Bool.false_or, decide_eq_true_eq] using hh
end ChainPrefix
''')
  name=f'ChainCase{a}_{l}'; mods.append(name)
  cond=f'((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ (({l}:V) = {p} ∧ m = {q} ∨ {l} = {q} ∧ m = {p})'
  (root/f'{name}.lean').write_text(''.join(f'import {n}\n' for n in names)+f'namespace ChainPrefix\ntheorem case{a}_{l} (b c m : V) (hf : Fits (first {a} b c {l} m)) : {cond} := by\n  fin_cases b\n'+''.join(f'  · exact case{a}_{l}_{b} c m hf\n' for b in range(11))+'end ChainPrefix\n')
Path('work/chain-modules.txt').write_text('\n'.join(mods)+'\n')
