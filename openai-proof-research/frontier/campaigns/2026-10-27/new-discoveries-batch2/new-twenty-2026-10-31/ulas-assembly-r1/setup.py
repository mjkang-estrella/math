from pathlib import Path
import shutil,re,json
L=Path(__file__).resolve().parent
src=L/'merged/src'
(src/'UlasFinal5.lean').write_text('''import UlasEven5Final
import UlasOdd5Final

namespace Ulas.Final5

theorem full_theorem_E2 :
    EvenFormula ∧ OddOneBound ∧ OddThreeBound ∧ OddOneEquality ∧
    OddThreeEquality ∧ FifteenBound ∧ NeverFifteen :=
  Ulas.full_theorem ⟨Ulas.Even5.evenFormula_proved, Ulas.Round5Odd.odd_theorem⟩

theorem mathdb_342364 : ¬ Conj61 :=
  Ulas.mathdb_342364 ⟨Ulas.Even5.evenFormula_proved, Ulas.Round5Odd.odd_theorem⟩

theorem conj61_some : Conj61Some :=
  Ulas.conj61_some ⟨Ulas.Even5.evenFormula_proved, Ulas.Round5Odd.odd_theorem⟩

#print full_theorem_E2
#print mathdb_342364
#print conj61_some
#print axioms full_theorem_E2
#print axioms mathdb_342364
#print axioms conj61_some
end Ulas.Final5
''')
# Preserve all inherited sources; scripts are separate replay instrumentation.
for f in ['run.sh','bounded.py']:
 shutil.copyfile(L/'input-ulas-formal-r5b/scripts'/f,L/'scripts'/f)
a=(src/'UlasOdd5Audit.lean').read_text().replace('import UlasOdd5Final','import UlasFinal5')
start=a.index('    let localDecl :=');end=a.index('\n    let deps :=',start)
a=a[:start]+'    let localDecl := mod.any (fun m => m.toString.startsWith "Ulas")'+a[end:]
(L/'scripts/audit-final.lean').write_text(a)
a=(L/'input-ulas-formal-r5b/scripts/analyze_audit5.py').read_text().replace('UlasOdd5Final','UlasFinal5')
a=a.replace("['Ulas.Round5Odd.full_theorem','Ulas.Round5Odd.mathdb_342364','Ulas.Round5Odd.conj61_some'", "['Ulas.Final5.full_theorem_E2','Ulas.Final5.mathdb_342364','Ulas.Final5.conj61_some'")
(L/'scripts/analyze-final.py').write_text(a)
# topological order
mods={f.stem:re.findall(r'^import (\S+)',f.read_text(),re.M) for f in src.glob('*.lean')}
order=[]
def visit(m):
 if m in order:return
 for d in mods[m]:
  if d in mods:visit(d)
 order.append(m)
for m in sorted(mods):visit(m)
(L/'module-order.json').write_text(json.dumps(order,indent=2))
print(order)
