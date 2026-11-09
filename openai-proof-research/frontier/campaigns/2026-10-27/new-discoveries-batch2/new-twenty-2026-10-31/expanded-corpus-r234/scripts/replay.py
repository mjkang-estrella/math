import pathlib,subprocess,sys,json,re,hashlib,zipfile
D=pathlib.Path(__file__).resolve().parents[1]
source=(D/'lean/Hurlbert.lean').read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',source)
names=re.findall(r'^LOCAL (.+)$',(D/'logs/inventory.log').read_text(),re.M)
(D/'lean/AllAxioms.lean').write_text('import Hurlbert\nset_option linter.auxLemma false\n'+''.join('#print axioms '+n+'\n' for n in names))
packet=D/'proof-packet-v2.zip'
with zipfile.ZipFile(packet,'x',zipfile.ZIP_DEFLATED) as z:
 for f in ['Hurlbert.lean','Inventory.lean','AllAxioms.lean']:z.write(D/'lean'/f,f)
R=D/'replay-v2';R.mkdir();
with zipfile.ZipFile(packet) as z:z.extractall(R)
runs=[('fresh2-build',['lean','-o','Hurlbert.olean','Hurlbert.lean']),('fresh2-inventory',['lean','Inventory.lean']),('fresh2-axioms',['lean','AllAxioms.lean']),('fresh2-checker',['checker','Hurlbert'])]
for name,args in runs:
 subprocess.run([sys.executable,'-I','-B',str(D/'scripts/limited.py'),name,sys.executable,'-I','-B',str(D/'scripts/lean_exec.py'),str(R),*args],check=True)
 rec=json.loads((D/'logs'/f'{name}.receipt.json').read_text());assert rec['returncode']==0,(name,(D/'logs'/f'{name}.log').read_text())
text=(D/'logs/fresh2-axioms.log').read_text();assert 'sorryAx' not in text
for line in text.splitlines():
 if 'depends on axioms:' in line:
  ax=re.search(r'\[([^]]*)\]',line)[1];assert set(ax.split(', '))<={'propext','Classical.choice','Quot.sound'},line
assert set(re.findall(r'^LOCAL (.+)$',(D/'logs/fresh2-inventory.log').read_text(),re.M))==set(names)
(D/'replay-result.json').write_text(json.dumps({'status':'PASS','strict_build':True,'all_local_declarations_including_generated':names,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'lean':'4.34.1','mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612','certificate_sha256':hashlib.sha256(source.encode()).hexdigest(),'trust_limit':'Prebuilt dependency oleans trusted; no full upstream source rebuild. leanchecker checks local module using trusted imports.'},indent=2)+'\n')
