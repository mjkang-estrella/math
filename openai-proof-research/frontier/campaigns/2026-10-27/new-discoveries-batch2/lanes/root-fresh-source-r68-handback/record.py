import hashlib,json,shutil,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
here=Path(__file__).resolve().parent;batch=here.parent.parent
lane=batch/'lanes/sol-fresh-source-discovery-r68'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=json.loads((lane/'provenance.json').read_text())
hashes=[{'path':k,'expected':v,'actual':sha(lane/k)} for k,v in p['files_sha256'].items()]
bad=[r for r in hashes if r['expected']!=r['actual']]
assert all(r['path'] in {'finalize.log','finalize-guard.json'} for r in bad),bad
copy=here/'check-copy';copy.mkdir(exist_ok=True)
for name in ('check.py','routes.py'):shutil.copyfile(lane/name,copy/name)
with (here/'routes.log').open('w') as log:
    subprocess.run([sys.executable,'-B','routes.py'],cwd=copy,stdout=log,stderr=subprocess.STDOUT,check=True)
assert (copy/'routes.json').read_bytes()==(lane/'routes.json').read_bytes()
receipt={
 'utc':datetime.now(timezone.utc).isoformat(),'status':'UNRESOLVED handback preserved','credit':0,'counts':[7,37],
 'target':'Rather Conjecture1: ordinary independence polynomial unimodality of all zero-divisor graphs of Z/nZ',
 'root_validation':'Own-copy routes.py PASS and byte-identical routes.json: complete16-vertex subset enumeration, five p^2q formula comparisons, literal n45 comparison, extension moments and actual n16 ultra-log-concavity obstruction.',
 'scope':'The K10 join E6 valley occurs only in an induced class subgraph of G847. Full G847 remains log-concave in the checked computation. Neither this valley nor failure of stronger ultra-log-concavity refutes the source.',
 'gap':'Uniform valuation-sensitive aggregate comparison, or extension-moment variance bound for every n and rank; no all-order closure theorem proved.',
 'full_worker_sweep_rerun':False,
 'source_registry':'Freshness HOLD retained. Root has not independently revalidated every source/prior-proof comparison; no new novelty clearance.',
 'formal':'No Lean, paper, acceptance or count change',
 'input_hashes':hashes,'hash_mismatches':bad,
}
(here/'ADOPTION.json').write_text(json.dumps(receipt,indent=2)+'\n')
assert all(sha(lane/r['path'])==r['actual'] for r in hashes)
nxt=batch/'NEXT.md';s=nxt.read_text()
s=s.replace('Three fresh Sol high/default research lanes r68 finite structures, r69 analysis,\nr67 arithmetic/algebra are active; no children.', 'r68 Rather zero-divisor independence unimodality remains unresolved. Its\ninduced-class obstruction is not a source counterexample; exact root route\nreplay is saved in root-fresh-source-r68-handback.\nThree fresh Sol high/default research lanes r70 finite structures, r69 analysis,\nr67 arithmetic/algebra are active; no children.')
nxt.write_text(s)
paths=[str(nxt.relative_to(Path.cwd()))]
paths += [str(p.relative_to(Path.cwd())) for root in (lane,here) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='pathspec.txt']
(here/'pathspec.txt').write_text('\n'.join(paths)+'\n')
print(json.dumps({'hashes':len(hashes),'mismatches':bad,'root_routes':'PASS','counts':[7,37]}))
