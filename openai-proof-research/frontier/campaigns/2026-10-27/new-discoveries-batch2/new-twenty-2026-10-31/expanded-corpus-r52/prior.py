import pathlib,json,hashlib,re,subprocess,urllib.request,datetime,resource,os
R=pathlib.Path(__file__).resolve().parent;resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(80,80));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);rec=json.loads((R/'records.json').read_text()); docs=[]
paths=[R.parent/'fresh-corpus-r10/sources/registry-preprints.json',R.parent/'staller-parent-final-r1/omega-D5-correct.json',R.parent/'staller-parent-final-r1/omega-Problems-correct.json']
for p in paths:
 d=json.loads(p.read_text()); assert not d['truncated'];terms='Taylor|Chung|Dirichlet|Ring.Lattice|Arc.Connectivity|Mostar|Faught|Kempton|Knudson|Secord|Absorbing';hits=[x['path'] for x in d['tree'] if re.search(terms,x['path'],re.I)];docs.append({'file':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'tree':d['sha'],'entries':len(d['tree']),'matches':hits,'review':'path-name screen only; bodies not read unless separately documented'})
(R/'registry-screen.json').write_text(json.dumps(docs,indent=2)+'\n')
# Strongly delimited IDs plus literal titles/source identifiers; omit mirrored upstream trees.
args=['rg','--no-ignore','-n','--pcre2','--max-columns','1200','--max-columns-preview','--glob','*.md','--glob','*results*.json','--glob','*review*.json','--glob','*ledger*.json','--glob','!**/fresh/**','--glob','!**/packet/**','--glob','!**/verification/**','--glob','!**/expanded-corpus-r52/**']
pat=r'(?<![0-9A-Za-z])(?:'+'|'.join(rec)+r')(?![0-9A-Za-z])|'+'|'.join(re.escape(v['record']['title']) for v in rec.values())
p=subprocess.run(args+['-e',pat,str(R.parents[3])],capture_output=True,text=True,timeout=80);assert p.returncode in [0,1],p.stderr
(R/'history-delimited.txt').write_text(p.stdout);print('delimited matches',len(p.stdout.splitlines()))
u='https://discovery.ucl.ac.uk/id/eprint/9064/1/9064.pdf';t=datetime.datetime.now(datetime.timezone.utc).isoformat()
try:
 with urllib.request.urlopen(u,timeout=25) as f:b=f.read();s=f.status
 p=R/'sources/sokal.pdf';p.write_bytes(b);receipt={'url':u,'status':s,'utc':t,'sha256':hashlib.sha256(b).hexdigest(),'file':str(p)}
 if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],timeout=20)
except Exception as e:receipt={'url':u,'utc':t,'error':str(e)}
(R/'sokal-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(receipt)
