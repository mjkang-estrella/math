from pathlib import Path
import json,hashlib,zipfile,shutil
r=Path(__file__).resolve().parent
new=['ColourOrientation','ColourScalar','ColouredSeed','ColourSeed16Closed4','ColourSeed16Open5','ColourSeed32Closed4','ColourSeed32Open5','ChosenLiftMagic','ChosenLiftExists','ColourWalks','ColourPersistence','ChosenSeedLiftData']
modules=json.loads((r/'inputs/xor-magic-formal-r4a/modules.json').read_text()) if (r/'inputs/xor-magic-formal-r4a/modules.json').exists() else json.loads((r/'modules.json').read_text())[:61]
# The inherited module order is taken from the read-only parent driver metadata.
modules=json.loads((r.parent/'xor-magic-formal-r4a/modules.json').read_text())+new
(r/'modules.json').write_text(json.dumps(modules,indent=2)+'\n')
a=(r/'formal/AuditR4a.lean').read_text();a=''.join('import '+x+'\n' for x in new)+a
old='["LiftWalks", "LiftHolonomy", "LiftCycleWalk", "LiftScalarWalk", "LiftOrientedCycle", "LiftConstantSum", "LiftMagicBridge"]'
a=a.replace(old,json.dumps(new)).replace('audit-r4a-dag','audit-r4c-dag')
(r/'formal/AuditR4c.lean').write_text(a)
s=(r/'tools/check_dag_r4a.py').read_text().replace('AuditR4a','AuditR4c').replace('audit-r4a','audit-r4c');(r/'tools/check_dag_r4c.py').write_text(s)
(r/'negative/BadColour.lean').write_text('import ColourSeed16Closed4\nopen XorMagic\nexample : Seed16Closed4.colouring.colour 0 = Seed16Closed4.colouring.colour (Seed16Closed4.decomposition0.mate 0 0) := by decide\n')
(r/'negative/BadChosenSlope.lean').write_text('import ColourSeed16Closed4\nopen XorMagic\nexample : outgoingSlope Base16Closed4.graph (chosenSlopes Base16Closed4.graph Seed16Closed4.colouring) 0 9 = 2 := by decide\n')
(r/'negative/BadColourScalar.lean').write_text('import ColourScalar\nopen XorMagic\nexample : (4 : ℕ) • ((1,0) : Four) + (1,0) = 0 := by decide\n')
s=(r/'inputs/xor-magic-formal-r4a/replay.py').read_text().replace("'AuditR4a']","'AuditR4a','AuditR4c']")
s=s.replace("for m in ['BadDegree'", "run('audit-r4c-dag-check',[sys.executable,'-I','tools/check_dag_r4c.py','logs/audit-r4c-dag.jsonl'])\nfor m in ['BadColour','BadChosenSlope','BadColourScalar','BadDegree'")
s=s.replace("'negative_controls':['BadDegree'","'negative_controls':['BadColour','BadChosenSlope','BadColourScalar','BadDegree'")
(r/'replay.py').write_text(s)
files=[r/f'formal/{m}.lean' for m in modules+['Audit','AuditR3','AuditR4a','AuditR4c']]+list((r/'negative').glob('*.lean'))+list((r/'tools').glob('*.py'))+[r/'modules.json',r/'replay.py']
manifest={str(f.relative_to(r)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files}
(r/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(r/'xor-magic-r4c-partial-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for f in files+[r/'source-manifest.json']:z.write(f,str(f.relative_to(r)))
fresh=r/'fresh-replay';fresh.mkdir()
with zipfile.ZipFile(r/'xor-magic-r4c-partial-source.zip') as z:z.extractall(fresh)
print(len(modules),len(files))
