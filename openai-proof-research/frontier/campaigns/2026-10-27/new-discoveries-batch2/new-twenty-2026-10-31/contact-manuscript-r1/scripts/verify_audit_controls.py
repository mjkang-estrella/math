from pathlib import Path
import subprocess,sys,json
p=Path(__file__).resolve().parents[1];out=p/'receipts/audit-controls';out.mkdir(exist_ok=True)
base='DECL test\nMODULE Control\nUNSAFE false\nPARTIAL false\nAXIOMS []\nTYPE_REF 0\nBODY_NONE\nNODE 0 sort zero\nEND_DECL\nTOTAL_LOCAL_DECLARATIONS 1\n'
cases={'valid':base,'unsafe':base.replace('UNSAFE false','UNSAFE true'),'partial':base.replace('PARTIAL false','PARTIAL true'),'compiler-recursion':base.replace('DECL test','DECL test._unsafe_rec'),'extra-axiom':base.replace('AXIOMS []','AXIOMS [ForbiddenAxiom]')}
results={}
for name,s in cases.items():
 f=out/(name+'.dag');f.write_text(s)
 c=subprocess.run([sys.executable,'-I','-B',str(p/'scripts/audit_inventory.py'),str(f),str(out/(name+'.json'))],capture_output=True,text=True)
 (out/(name+'.log')).write_text(c.stdout+c.stderr)
 assert c.returncode==(0 if name=='valid' else 1),(name,c.returncode)
 results[name]={'returncode':c.returncode,'expected_rejection':name!='valid'}
(out/'controls.json').write_text(json.dumps({'status':'PASS','cases':results},indent=2)+'\n')
print('PASS: valid inventory accepted; unsafe, partial, compiler recursion and extra axiom rejected')
