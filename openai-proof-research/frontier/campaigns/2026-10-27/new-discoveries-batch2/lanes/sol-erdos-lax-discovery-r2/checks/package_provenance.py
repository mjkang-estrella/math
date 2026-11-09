"""Package local source receipts; all writes stay inside this lane."""
import pathlib,json,hashlib,datetime,shutil
L=pathlib.Path(__file__).resolve().parents[1];B=L.parents[1];R=B.parents[3]
# Resolve from lane instead of relying on any shell working directory.
R=next(p for p in L.parents if p.name=='openai-proof-research')
E=B/'lanes/root-erdos-lax-r1'
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
inputs=[]
paths=[R/'AGENTS.md',R/'sources/upstream.json',R/'sources/CONTENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json']
paths += [p for p in E.rglob('*') if p.is_file() and (p.suffix in ['.md','.json','.py','.txt','.html'] or p.name=='source-conjecture2.png')]
paths += [B/'lanes/root-new-targets-r14/sources'/('2309.02047v2'+s) for s in ['.pdf','.txt']]
for p in paths:
 inputs.append({'path':str(p),'sha256':h(p),'bytes':p.stat().st_size})
for suf in ['.pdf','.txt']:
 shutil.copyfile(B/'lanes/root-new-targets-r14/sources'/('2309.02047v2'+suf),L/'sources'/('2309.02047v2'+suf))
queries=['"Bergman" "Rubin" "Erdős" conjecture','"generalized polynomials" "Erdős-Lax"','"Bernstein" "Markov" "generalized nonnegative polynomials" Erdelyi 1991','"2309.02047" conjecture proof','"rational powers" "Lax" inequality','"generalized polynomials" "sharp" "unit circle" derivative','"Bergman" "Rubin" "vanishing weight" proof conjecture','"generalized" "Erdos-Lax" inequality powers polynomials -quaternionic','"generalized polynomials" "Bernstein" "sharp constant"']
(L/'search-log.json').write_text(json.dumps({'queries':queries,'method':'public web search; no browser actions','outcome':'No verified full resolution located. Search-result abstracts are not theorem-body clearance.','primary_bodies_consumed':['https://people.tamu.edu/~terdelyi/papers-online/BMIGNP.pdf','https://people.tamu.edu/~terdelyi/papers-online/WMB.pdf'],'unconsumed_neighboring_hits':['https://insa.nic.in/writereaddata/UpLoadedFiles/IJPAM/Vol54_2023_3_ART29.pdf','https://files.ele-math.com/articles/mia-25-25.pdf'],'limits':'Search receipts are manual query/outcome notes; not a saved exhaustive search-engine result corpus.'},indent=2)+'\n')
receipts=json.loads((L/'retrieval.json').read_text())+json.loads((L/'retrieval-extra.json').read_text())
manifest=[{'path':str(p.relative_to(L)),'sha256':h(p),'bytes':p.stat().st_size} for p in (L/'sources').iterdir() if p.is_file()]
prov={'status':'UNRESOLVED','credit':0,'created_runtime_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'task_current_date':'2026-10-28','clock_limit':'Runtime receipts read 2026-10-29; kept verbatim.','target':{'arxiv':'https://arxiv.org/abs/2309.02047v2','pdf':'https://arxiv.org/pdf/2309.02047v2','label':'Conjecture 2 printed p27','mathdb_id':359807,'published_doi':'https://doi.org/10.1016/j.jat.2024.106048'},'receipts':receipts,'frozen_lane_sources':manifest,'local_inputs':inputs,'historical_commit_limit':'No git operations; current local bytes hashed, historical root commit 3a32fdd737 not independently authenticated.','access_limits':['Published journal body unread; inherited publisher403 respected and not repeated.','Intro-only thesis downloads do not include appended journal article; no contrary claim.','Registry path/catalogue and complete delta screen only, not all theorem bodies.','No worldwide priority or open-status certification.'],'mathematics':'Auxiliary exact counterexample to radial-monotonicity route and limited variational lemma; no full source proof/counterexample.','formal_status':'NOT ATTEMPTED; no closed endpoint','count_baseline':{'additional_accepted':3,'total_accepted':33,'this_lane_credit':0}}
(L/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
print('Packaged',len(manifest),'lane sources;',len(inputs),'hashed local inputs')
