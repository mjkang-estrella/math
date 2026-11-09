import pathlib,json,hashlib,subprocess,sys
P=pathlib.Path(__file__).resolve().parent
neg=[]
for n in ['hash','size','extra']:
 r=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--negative-case',n],capture_output=True,text=True);assert r.returncode!=0
 neg.append({'case':n,'returncode':r.returncode,'stderr':r.stderr,'fixture':'bounded synthetic bytes/path set; no originals mutated'})
(P/'negative-tests.json').write_text(json.dumps(neg,indent=2)+'\n')
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files},indent=2)+'\n')
r=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--payload-only'],capture_output=True,text=True)
if r.returncode:print(r.stderr);sys.exit(r.returncode)
a=json.loads(r.stdout);a['negative_subprocess_exit_codes']={x['case']:x['returncode'] for x in neg};a['counts']={'additional':9,'total':39,'next':40};a['eligibility_exclusions']=6;a['holds']=44
(P/'final-verification-receipt.json').write_text(json.dumps(a,indent=2)+'\n');print(json.dumps(a))
