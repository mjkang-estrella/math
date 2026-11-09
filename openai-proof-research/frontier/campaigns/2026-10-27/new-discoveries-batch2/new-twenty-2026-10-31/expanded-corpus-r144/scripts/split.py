import pathlib
D=pathlib.Path(__file__).resolve().parents[1]
s='import Base\nnamespace Rainbow\nset_option synthInstance.maxSize 1000\nset_option maxRecDepth 3000\nset_option maxHeartbeats 3000000\n'
for i in range(2):
 for x in range(8):
  for y in range(8):
   if x==y:continue
   g='G' if i==0 else 'Gᶜ'
   s+=f'theorem cert{i}_{x}_{y} : CutCert {g} color{i} {x} {y} (cut{i} {x} {y}) (side{i} {x} {y}) := by\n  dsimp [CutCert, RainbowOn, cut{i}, side{i}, color{i}]\n  decide\n'
for i in range(2):
 g='G' if i==0 else 'Gᶜ'
 s+=f'theorem cert{i} : ∀ x y, x ≠ y → CutCert {g} color{i} x y (cut{i} x y) (side{i} x y) := by\n  intro x y h\n  fin_cases x <;> fin_cases y\n'
 for x in range(8):
  for y in range(8):
   s+=('  · exact (h rfl).elim\n' if x==y else f'  · exact cert{i}_{x}_{y}\n')
s+='end Rainbow\n'
(D/'Certificates.lean').write_text(s)
