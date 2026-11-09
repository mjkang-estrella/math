from pathlib import Path
import hashlib,json,stat,subprocess,sys
r=Path(__file__).resolve().parents[1];p=r/'packet';pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(path,x):path.write_text(json.dumps(x,indent=2,sort_keys=True,ensure_ascii=False)+'\n')
files={};dirs={'':stat.S_IMODE(p.stat().st_mode)}
for x in sorted(p.rglob('*')):
 st=x.lstat();name=x.relative_to(p).as_posix()
 if stat.S_ISDIR(st.st_mode):dirs[name]=stat.S_IMODE(st.st_mode)
 else:
  assert stat.S_ISREG(st.st_mode) and st.st_nlink==1
  data=x.read_bytes();files[name]={'sha256':sha(data),'bytes':len(data),'mode':stat.S_IMODE(st.st_mode)}
dump(r/'MANIFEST.json',{'format':'r123-exact-packet-v1','pin':pin,'files':files,'directories':dirs})
reporthash=sha((p/'public/report.md').read_bytes());mh=sha((r/'MANIFEST.json').read_bytes())
f={'format':'r123-detached-final-v1','pin':pin,'status':'PREFREEZE_NO_NOMINEE','frozen':False,'nominee':None,'count_assignment':None,'gate_assignment':None,'manifest_sha256':mh,'report_sha256':reporthash,'canonical_tree_sha256':'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','payload_files':len(files),'directories_including_root':len(dirs),'mathematical_gate':False}
dump(r/'FINAL.json',f);fh=sha((r/'FINAL.json').read_bytes())
handoff=f'''# Analytic r123 handoff

Prefreeze: no target frozen, no nominee, no count/gate assignment. Four unequal operative families278/290/366/090. See [public report](packet/public/report.md), [Kohn–Sham feasibility](packet/public/kohn-sham.md), [operator screens](packet/public/operators.md), [geometric/history screens](packet/public/geometric-screens.md), and [reading limits](packet/public/reading-limits.md).

The main strengthened comparison repairs a premature symmetry inference through classical occupation convexity, then uses the effective two-dimensional quadratic-form interface with the source's complete global endgame. No additional unpaid operation was identified or full enlarged-potential theorem submitted. Countable core-commutant simultaneity fits a weighted diagonal product. Actual r120 contains the exact crack-tip and stationary Gaussian calculations; late timing is disclosed. Endpoint sheet concentration and enlarged ensemble domains remain unclosed interfaces, not substitute nominees or full-target counterexamples.

Detached FINAL SHA256: `{fh}`

Detached public report SHA256: `{reporthash}`

Manifest SHA256: `{mh}`

The exact packet has {len(files)} files and {len(dirs)} directories including its root:12 canonical source bodies,6 removed-acquisition metadata records,4 successful primary PDF/text pairs,1 failed primary URL,1 primary page image and7 selected historical bodies/excerpts. Private evidence retains original rights. No upload/publication/browser UI, git mutation/shared edit, nested agent or formal/manuscript work occurred.

Run from this directory:

```sh
python -B packet/public/verify.py . --finalhash {fh} --reporthash {reporthash} --tree /home/mj-kang/Documents/Dev/math/openai-proof-research/sources/preprints-tree.json
```

Final disposable-copy controls are recorded at `scratch/final-controls/receipt.json`; final direct verification is `final-verification.json`. Read their actual results. They authenticate bytes only and do not supply mathematical or contribution gates. The runner checks the whole preexisting actual owned root unchanged, excluding only its newly created controls-output subtree. Parent integrates.
'''
(r/'HANDOFF.md').write_text(handoff)
command=[sys.executable,'-B',str(p/'public/verify.py'),str(r),'--finalhash',fh,'--reporthash',reporthash,'--tree',str(r.parents[3]/'sources/preprints-tree.json')]
z=subprocess.run(command,capture_output=True,text=True);assert z.returncode==0,z.stderr
(r/'final-verification.json').write_text(z.stdout)
print(json.dumps({'final_sha256':fh,'report_sha256':reporthash,'manifest_sha256':mh,'files':len(files),'directories':len(dirs),'verification':json.loads(z.stdout)},indent=2))
