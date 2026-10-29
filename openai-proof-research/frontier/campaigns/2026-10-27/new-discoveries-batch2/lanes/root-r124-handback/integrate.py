from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;B=P.parents[1];repo=B.parents[4];S=P.parent/'sol-fresh-source-discovery-r124'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
m=json.loads((S/'finalmanifest.json').read_text())
for r in m:assert sha(S/r['path'])==r['sha256'] and (S/r['path']).stat().st_size==r['bytes'],r['path']
for n in ('checks.py','http.jsonl','scientific-freeze.json'):shutil.copy2(S/n,P/('copied-checks.py' if n=='checks.py' else n))
copyset={r['path'] for r in json.loads((P/'scientific-freeze.json').read_text())}
for line in (P/'http.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'copy' in r:copyset.add(r['copy'])
for n in copyset:
 d=P/n;d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(S/n,d)
r=subprocess.run([sys.executable,str(P/'copied-checks.py')],capture_output=True,text=True,check=True)
(P/'checks.log').write_text(r.stdout+r.stderr);j=json.loads(r.stdout)
assert j['status']=='PASS' and j['denominator_reconstructions']==12 and len(j['agoh_public_witness_finite_jets'])==8
assert j['old_mixed_obstruction']['mixed']==-206
for r in m:assert sha(S/r['path'])==r['sha256'],r['path']
out={'status':'PASS','manifest_entries':len(m),'copied_checker_sha256':sha(P/'copied-checks.py'),'denominator_reconstructions':12,'finite_Agoh_jets':8,'scientific_files_verified':j['scientific_files_verified'],'HTTP_receipts_verified':j['http_receipts_verified'],'credit':0,'counts':[9,39],'qualification':'Copied checker replay and old diagnostic reproduction only; no universal proof, novelty clearance or external Lean replay.'}
(P/'ADOPTION.json').write_text(json.dumps(out,indent=2)+'\n')
n=(B/'NEXT.md').read_text()
intro='''r124 adopted zero nominees. Exact early historical screen identifies public
Agoh/subsum-coprimality proofs and old unresolved denominator/Koizumi targets.
Root verifies67 manifest entries and replays12 denominator constructions/eight
finite Agoh jets with scientific/HTTP hashes. These reproduce old diagnostics,
not new source resolutions. See root-r124-handback. Sol r127 replaces r124;
fresh r125/r126 continue. Counts unchanged9additional/39total.

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
subprocess.run(git+['commit','-m','Record r124 early public and historical exclusions','--pathspec-from-file='+str(ps)],cwd=repo,check=True,stdout=subprocess.DEVNULL)
subprocess.run(git+['log','-1','--format=%h %s'],cwd=repo,check=True)
print(json.dumps(out))
