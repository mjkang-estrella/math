from retrieve import *
guard=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
write_guard={'path':str(guard),'sha256':sha(guard),'AS_bytes':512*1024*1024,'group_RSS_bytes':512*1024*1024,'CPU_seconds':210,'wall_seconds':230,'cap_raises':False}
(L/'guard-binding.json').write_text(json.dumps(write_guard,indent=2))
for name in ['checks.py','direct_check.py','certificates.py']:
 p=subprocess.run([sys.executable,str(L/name)],capture_output=True,text=True,check=False)
 (L/(name+'.log')).write_text(p.stdout+'\nSTDERR\n'+p.stderr+'\nEXIT '+str(p.returncode)+'\n')
 assert p.returncode==0,name
for row in map(json.loads,(L/'bindings.jsonl').read_text().splitlines()):
 assert sha(Path(row['copy']))==row['sha256']
 if not row['administrative']:assert sha(Path(row['original']))==row['sha256']
manifest={str(p.relative_to(L)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','final-verification.json']}
(L/'final-manifest.json').write_text(json.dumps({'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'excludes':['final-manifest.json','final-verification.json'],'files':manifest},indent=2))
print('FINAL MANIFEST',len(manifest),'files')
