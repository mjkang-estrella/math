import hashlib,json,shutil,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone

here=Path(__file__).resolve().parent
batch=here.parent.parent
lane=batch/'lanes/sol-fresh-source-discovery-r66'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((lane/'SHA256SUMS.json').read_text())
rows=[{'path':k,'expected':v,'actual':sha(lane/k)} for k,v in manifest.items()]
assert all(r['expected']==r['actual'] for r in rows)
copy=here/'check-copy';copy.mkdir(exist_ok=True)
shutil.copyfile(lane/'obstructions.py',copy/'obstructions.py')
with (here/'obstructions.log').open('w') as log:
    subprocess.run([sys.executable,'obstructions.py'],cwd=copy,stdout=log,stderr=subprocess.STDOUT,check=True)
assert (copy/'obstructions.json').read_bytes()==(lane/'obstructions.json').read_bytes()
receipt={
 'utc':datetime.now(timezone.utc).isoformat(),'status':'UNRESOLVED handback preserved','credit':0,'counts':[7,37],
 'target':'Sra Conjecture4.1, aligned-principal-specialization Macdonald polynomial Turan-ratio monotonicity',
 'root_validation':'Both exact rational route obstructions replayed in an own copy, output byte-identical. Manifest verified before and after.',
 'scope':'Positive symmetric homogeneous mixture fails the generalized sign claim; genuine one-box specialization fails the transferred Schur-Toda identity. Neither refutes source monotonicity.',
 'remaining_gap':'Uniform all-partition sign using actual Macdonald branching coefficients: tilted-prefix expectation comparison or cleared derivative positivity, including strictness off rectangles.',
 'full_worker_suite_rerun_by_root':False,
 'limitations':['Root did not independently rederive full branching implementation or authenticate every source claim.','No source theorem or counterexample is nominated.','Registry freshness HOLD retained.','No Lean, formal PASS, paper, acceptance or count change.'],
 'input_hashes':rows,
}
(here/'ADOPTION.json').write_text(json.dumps(receipt,indent=2)+'\n')
assert all(sha(lane/k)==v for k,v in manifest.items())
nxt=batch/'NEXT.md';s=nxt.read_text()
s=s.replace('Three fresh Sol high/default research lanes r68 finite structures, r66 analysis,\nr67 arithmetic/algebra are active; no children.', 'r66 Macdonald Turan-ratio monotonicity remains unresolved; generic positive-\nsymmetric and Schur-Toda routes fail, not the source claim. Root exact obstruction\nreplay and frozen manifest checks are saved in root-fresh-source-r66-handback.\nThree fresh Sol high/default research lanes r68 finite structures, r69 analysis,\nr67 arithmetic/algebra are active; no children.')
nxt.write_text(s)
paths=[str(nxt.relative_to(Path.cwd()))]
paths += [str(p.relative_to(Path.cwd())) for root in (lane,here) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='pathspec.txt']
(here/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({'hashes':len(rows),'obstruction_replay':'PASS','credit':0,'counts':[7,37]}))
