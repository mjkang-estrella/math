import pathlib,json,hashlib,subprocess,datetime
O=pathlib.Path(__file__).resolve().parent;L=O.parent
load=lambda p:json.loads(p.read_text())
def dump(n,x):(O/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def entry(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size}
f=load(O/'failures.json');f['inherited_r714_failed_checks']=load(L/'sol-mathdb-primary-qualified-breadth-r714/failures.json')['new_failed_checks'];dump('failures.json',f)
refs=load(O/'flat-bindings.json');known={x['path'] for x in refs}
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parent/'AGENTS.md',L.parents[4]/'AGENTS.md']:
 if p.exists() and str(p) not in known:refs.append(entry(p));known.add(str(p))
dump('flat-bindings.json',refs)
exclude=['manifest.json','final-verification-receipt.json'];files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and str(p.relative_to(O)) not in exclude:
  e=entry(p);e['path']=str(p.relative_to(O));files.append(e)
dump('manifest.json',{'excluded_exact_paths':exclude,'files':files})
runs=[]
for mode in [None,'hash','size','extra']:
 cmd=['sh',str(O/'verify.sh')]+([mode] if mode else [])
 p=subprocess.run(cmd,capture_output=True,text=True)
 runs.append({'mode':mode or 'normal','exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
 assert p.returncode==(0 if mode is None else 1),runs[-1]
e=entry(O/'manifest.json')
dump('final-verification-receipt.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':e,'runs':runs,'all_positive_and_negative_checks_passed':True,'integrity_only':True,'math_status':'No new full-scope proof; registry/successor/dependencies HOLD; zero credit.'})
# Recheck final exact payload with receipt now present, no output file mutation by verifier.
p=subprocess.run(['sh',str(O/'verify.sh')],capture_output=True,text=True);assert p.returncode==0,(p.stdout,p.stderr)
print(json.dumps({'manifest':e,'final_verifier':json.loads(p.stdout),'negative_exits':[x['exit'] for x in runs[1:]]},indent=2))
