from pathlib import Path
import json,hashlib,subprocess,sys,datetime
L=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(L/'prepare.py')],check=True)
p=json.loads((L/'provenance.json').read_text())
p.update(status='broad scout: 19 statements, seven primary papers, five qualified leads; zero nominations',
 target='scout.md ranked shortlist; original D4 attempt preserved in discovery.md',
 shortlist=['Richardson Conj5.1','Tyszka Conj3 arbitrary G','Akman division-graph completeness','Tyszka Conj5','Del Donno D4 prolongation'],
 broad_alias_screens=['broad-alias-screen.json','broad-alias-reference-screen.json'],
 exclusions='Tyszka determinant complete routine bridge; Farhi-Kane public proof; public matroid counterexample')
(L/'provenance.json').write_text(json.dumps(p,indent=2)+'\n')
v=json.loads((L/'source-versions.json').read_text())
mapping={'contact':'contact','os':'os','cdor':'cdor','filbert':'filbert','tyszka':'tyszka','akman':'akman','newman':'newman','lcm':'lcm','matroid':'matroid','berg':'berg','later':'tyszka-later','counter':'matroid-counter'}
for r in v:
 key=Path(r['file']).name.removesuffix('-abs.html');q=L/(mapping[key]+'.txt')
 r['body_header']='\n'.join(q.read_text().splitlines()[:42]) if q.exists() else None
 r['publication_limit']='Current arXiv body authenticated; journal version not independently compared'
(L/'source-versions.json').write_text(json.dumps(v,indent=2)+'\n')
exclusions=['finalmanifest.json','verification-receipt.json']
files={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in exclusions}
(L/'finalmanifest.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),exclusions=exclusions,files=files),indent=2)+'\n')
print('Manifest finalized:',len(files),'files. Separate guarded verify.py must follow.')
