from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/'sol-fresh-source-discovery-r123'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
m=json.loads((S/'finalmanifest.json').read_text())['files']
for k,v in m.items():assert sha(S/k)==v['sha256'] and (S/k).stat().st_size==v['bytes'],k
shutil.copy2(S/'checks.py',P/'copied-checks.py');shutil.copy2(S/'http.jsonl',P/'http.jsonl')
for line in (P/'http.jsonl').read_text().splitlines():
 row=json.loads(line)
 if 'copy' in row:
  dst=P/row['copy'];dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(S/row['copy'],dst)
r=subprocess.run([sys.executable,str(P/'copied-checks.py')],capture_output=True,text=True,check=True)
(P/'checks.log').write_text(r.stdout+r.stderr);j=json.loads(r.stdout)
assert j['status']=='PASS' and len(j['exact_source_coefficient_rows'])==40 and j['IBP_checks']==9
for k,v in m.items():assert sha(S/k)==v['sha256'],k
out={'status':'PASS','manifest_entries':len(m),'copied_checker_sha256':sha(P/'copied-checks.py'),'coefficient_comparisons':40,'kernel_checks':9,'HTTP_hash_bindings':len(j['HTTP_byte_bindings']),'credit':0,'counts':[9,39],'qualification':'Copied checker replay, not independent implementation. Root checked routine kernel argument; no unrestricted printed-index conclusion or public proof certification.'}
(P/'ADOPTION.json').write_text(json.dumps(out,indent=2)+'\n')
n=(B/'NEXT.md').read_text()
intro='''r123 adopted zero nominees: noncentralchi-square/Krasniqi public proofs,
old beta-prime exclusion and already-credited Mills; Xu–Yang natural n>=2
remainder follows by routine source-kernel two-IBP/Taylor argument. Printed
lower-index ambiguity is not repaired or counted. Root verifies55 manifest
entries and replays40 coefficient/9kernel checks with HTTP bindings. See
root-r123-handback. Sol r126 replaces r123; r124/r125 continue. Counts9/39.

'''
(B/'NEXT.md').write_text(n.replace('# Current continuation — 29 October 2026\n','# Current continuation — 29 October 2026\n\n'+intro,1))
paths=[B/'NEXT.md'];bulk=[]
for base in [P,S]:
 for p in sorted(base.rglob('*')):
  if not p.is_file() or '__pycache__' in p.parts or p.name=='commit-paths.txt' or p.suffix in {'.pyc','.olean','.ilean','.ir','.o','.so'}:continue
  if p.stat().st_size>10485760:bulk.append({'path':str(p.relative_to(repo)),'bytes':p.stat().st_size,'sha256':sha(p)})
  else:paths.append(p)
bp=P/'unstaged-bulk-evidence.json';bp.write_text(json.dumps(bulk,indent=2)+'\n');paths.append(bp)
ps=P/'commit-paths.txt';ps.write_text(''.join(str(p.relative_to(repo))+'\n' for p in sorted(set(paths))))
git=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-c','index.threads=1','-c','core.preloadIndex=false','-c','gc.auto=0']
subprocess.run(git+['add','-f','--pathspec-from-file='+str(ps)],cwd=repo,check=True)
subprocess.run(git+['commit','-m','Record r123 public exclusions and routine remainder argument','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(out))
