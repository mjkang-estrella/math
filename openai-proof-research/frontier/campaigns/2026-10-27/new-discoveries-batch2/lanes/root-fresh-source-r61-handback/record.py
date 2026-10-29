import hashlib, itertools, json, shutil, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path

here = Path(__file__).resolve().parent
batch = here.parent.parent
lane = batch / 'lanes/sol-fresh-source-discovery-r61'
prov = json.loads((lane / 'provenance.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
hashes = [{'path':k,'expected':v['sha256'] if isinstance(v,dict) else v,'actual':sha(lane/k)} for k,v in prov['files'].items()]
mismatches = [r for r in hashes if r['expected'] != r['actual']]
assert all(r['path'] in {'finalize.log','finalize-guard.json'} for r in mismatches), mismatches
copy = here/'check-copy'
copy.mkdir(exist_ok=True)
shutil.copyfile(lane/'check.py',copy/'check.py')
with (here/'check.log').open('w') as log:
    subprocess.run([sys.executable,'check.py'],cwd=copy,stdout=log,stderr=subprocess.STDOUT,check=True)
assert (copy/'checks.json').read_bytes() == (lane/'checks.json').read_bytes()
reps = [(0,1,0,1),(0,1,0,2),(0,1,2,0),(0,1,2,1)]
matrix = [[sum(all(r[k] != p[s[k]] for k in range(4)) for p in itertools.permutations(range(3))) for s in reps] for r in reps]
assert matrix == [[3,2,1,2],[2,2,1,2],[1,1,2,1],[2,2,1,2]]
v=[1]*4
for _ in range(3):
    v=[sum(a*b for a,b in zip(row,v)) for row in matrix]
assert v == [399,342,219,342] and sum(v)==1302
assert 41869995708%4==0
receipt = {
 'utc':datetime.now(timezone.utc).isoformat(),
 'decision':'EXCLUDE discovery credit as a routine classical/counting corollary',
 'credit':0,'counts':{'additional':7,'total':37},
 'ordinary_math':'PASS for the odd-grid congruence refutation at 7x7; no determination of AO-Hamiltonicity or other conjectured families',
 'root_checks':'Own-copy checker PASS with byte-identical checks.json; independent six-permutation evaluation of every 4x4 transfer entry and three matrix products PASS',
 'root_source_read':'Cached source Conjecture1(1), Stanley Cor1.3 and OEIS A182406 definition/value inspected as text; no fresh network or PDF visual check by root',
 'complete_bridge':'For integer-coefficient chromatic polynomial C, C(-1)=C(3) mod4. Stanley gives a(G)=(-1)^49 C(-1). The existing same-object count C(P7 square P7,3)=41869995708 is divisible by4. This closes the refutation without a new estimate or construction.',
 'independent_proof':'Color permutations act freely; middle-column reflection fixes two colors, hence a fixed color orbit is genuinely reflection-invariant. Two foldings reduce parity of color orbits from7x7 to4x4, where the explicit transfer matrix gives1302. The alternative certificate does not undo the complete known-count bridge.',
 'strongest_countercase':'An explicit open conjecture is false and the independent reflection proof supplies a small certificate. The campaign nevertheless excludes routine consequences of already-public same-object results.',
 'limits':['Current registry freshness HOLD.','Current OEIS bytes do not authenticate an immutable 2012 snapshot.','No exact prior printed refutation claimed.','No Lean, paper, acceptance or credit.'],
 'input_hashes':hashes,'hash_mismatches':mismatches,
 'root_failure':'Initial manifest reader compared {bytes,sha256} objects to strings and failed before edits/replay. Corrected to extract sha256; no evidence changed.',
}
(here/'ADOPTION.json').write_text(json.dumps(receipt,indent=2)+'\n')
nextp=batch/'NEXT.md'
s=nextp.read_text().replace('Three fresh Sol high/default research lanes r61 finite structures, r62 analysis,\nr64 arithmetic/algebra are active; no children.', 'r61 odd-grid congruence refutation is also excluded: the public same-object\nthree-color count and Stanley Corollary1.3 supply a complete routine bridge.\nSee lanes/root-fresh-source-r61-handback/ADOPTION.json.\nThree fresh Sol high/default research lanes r65 finite structures, r62 analysis,\nr64 arithmetic/algebra are active; no children.')
nextp.write_text(s)
paths=[str(nextp.relative_to(Path.cwd()))]
paths += [str(p.relative_to(Path.cwd())) for root in (lane,here) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name != 'pathspec.txt']
(here/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({'checks':'PASS','hashes':len(hashes),'mismatches':mismatches,'counts':[7,37]}))
