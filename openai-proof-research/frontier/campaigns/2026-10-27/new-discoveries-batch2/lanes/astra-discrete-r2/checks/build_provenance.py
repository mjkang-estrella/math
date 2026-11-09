from pathlib import Path
import hashlib,json,datetime
lane=Path(__file__).resolve().parent.parent
root=Path('/home/mj-kang/Documents/Dev/math')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
roles={
'hoggatt.html':'Primary source: definition, Conjecture 4.1, Theorems 1.2/2.1/2.2 and q=1 proof read.',
'hoggatt-abs.html':'Live revision history: only v1 displayed.',
'lamprecht.html':'Closest q-separation input: definitions and Theorems 25/29/30 read; not claiming these ingredients new.',
'leake-ryder.html':'Theorem 1.7, Proposition 3.6 q-polar derivative context read.',
'q-convolution-2026.html':'Section 2.4, Propositions 3.4/3.5 and hypergeometric context read.',
'dilks-thesis.pdf':'Theorem 3.8 and proof read through web PDF text; local PDF saved.',
'mao-shi.html':'Definition 1.1, Theorem 2.4 and q=1 context read.',
'chern-shi-logconvex.html':'Definitions and Theorems 1.1-1.4 read; distinguish row variable q from two-variable problem.',
'liu-mao.html':'Definitions and Theorems 6.6/6.7 read; log-concavity, not Sturm endpoint.',
'cigler-proof.html':'Theorem 1.1 of related but distinct Cigler positivity problem read.',
'registry-companion-2403.html':'False registry match: general criteria for split real polynomials.',
'narayana-symmetry.html':'False registry match: different Narayana refinement; Conjectures 5.4/5.5 already resolved per v2.',
'registry-companion-2212.html':'Revision history for false-match Narayana paper.',
'mathdb-368343.json':'Live registry response. Empty solution/comment arrays do not establish novelty.',
'mathdb-372432.json':'BBK registry response; not evidence of novelty.',
'realrooted-hoggatt-issues.json':'Public issue search only; one q=1-related issue. Not exhaustive code audit.',
'formal-conjectures-hoggatt-issues.json':'Public issue search only, zero results. Not exhaustive code audit.',
'bbk.html':'BBK Conjectures 5.1/5.2/5.4 source and hypotheses read.',
'bbk-abs.html':'BBK live source revision metadata.',
'chern-wang.html':'Original positivity proved, not full BBK refinement.',
'sign-resolved.html':'Resolution of companion unbounded-sign conjecture; excluded.',
'kumar-martino.html':'Conjecture 4.8 screening; gcd scaling defect rejected as ineligible.',
}
sources=json.loads((lane/'sources/manifest.json').read_text())
for s in sources:
 if 'file' in s:
  assert sha(lane/'sources'/s['file'])==s['sha256']
  s['inspection']=roles.get(s['file'],'BBK companion primary text inspected for stated resolution; no full-refinement proof identified.')
local=[]
for p in [root/'openai-proof-research/AGENTS.md',lane.parents[1]/'AGENTS.md',lane.parents[1]/'ledger.json',lane.parents[1]/'prior-campaign-context.json',lane.parent/'root-nearline-r1/screening.md',lane.parent/'pi-discrete-r1/progress.md']:
 if p.exists():local.append({'path':str(p),'sha256':sha(p),'access':'read only'})
old=root/'openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-discrete-discovery-r7'
for name in ['FINDINGS.md','discovery.md','progress.md','provenance.json']:
 p=old/name
 if p.exists():local.append({'path':str(p),'sha256':sha(p),'access':'read only'})
queries=['"Hoggatt" "Sturm" q conjecture proof','"Hoggatt" "2505.05873" proof conjecture','"Hoggatt" "Ideosphere"','"Garloff" "Wagner" "THEOREM 4"','"Lamprecht" "Theorem 25" q Rolle','"Hoggatt" "q" "interlacing" proof 2026','site:ideosphere.ai "Hoggatt"','site:github.com "Hoggatt" "q" "Sturm"','"Suffridge" "Lamprecht" arxiv','"Strong q-log-convexity" "Hoggatt" arxiv','"Pfaffian–Toeplitz identities" Liu Mao']
web_only=[{'url':'https://www-home.htwg-konstanz.de/~garloff/Garloff_Wagner_Hadamard_Products.pdf','inspection':'Indexed original page 800 Theorem 4 full statement read; direct PDF fetch timed out. FZZ full restatement independently agrees.','sha256':None,'access_limit':'No local full PDF bytes or full original proof; no fabricated hash.'},{'url':'https://www.sciencedirect.com/science/article/abs/pii/S0022247X26002271','inspection':'Accessible primary publication preview/introduction/conclusion inspected, including retained conjecture context.','sha256':None,'access_limit':'Web-rendered preview only; not a downloaded full journal article.'},{'url':'https://doi.org/10.1016/j.jmaa.2026.130615','inspection':'DOI of journal version.','sha256':None,'access_limit':'Bibliographic link; not downloaded separately.'},{'url':'https://qseries.org/alladi70/talks/keithw/','inspection':'Talk abstract read using web tool; direct urllib returned HTTP406.','sha256':None,'access_limit':'No local full bytes.'},{'url':'https://github.com/PerAlexandersson/RealRooted/issues/1332','inspection':'Search result and API search item concern q=1-related Hoggatt formalization.','sha256':None,'access_limit':'Not a full repository or all-comments audit; corresponding search JSON saved.'}]
artifacts=[]
for p in sorted(lane.rglob('*')):
 if not p.is_file() or p.name=='provenance.json' or 'sources' in p.relative_to(lane).parts:continue
 artifacts.append({'path':str(p.relative_to(lane)),'sha256':sha(p)})
out={'lane':str(lane),'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'candidate-written-proof-not-accepted-not-counted','target':'Fang-Zhang-Zhao arXiv2505.05873 Conjecture4.1; MathDB368343','claim':'For real q>1 and integer m>=2, all Hoggatt H_n have simple negative roots and consecutive strict interlacing; implies integer-q conjecture with known q=1 case.','scope':'One family only. No credit proposed for helpers, parameter cases, q=1, or BBK finite computations.','strongest_objection':'Routine adaptation/subsumption of FZZ q=1 induction via classical q-separation. Independent review needed.','sources':sources,'web_only_sources':web_only,'public_search_queries':queries,'search_limits':['Bounded public search, not an assertion of absolute priority.','Ideosphere searched through public search engine only; no authenticated/private index accessed.','GitHub searches were issue searches only, not exhaustive code search.','MathDB status and empty arrays explicitly not used as novelty proof.','No independent adversarial reviewer used because this is a solo lane.'],'local_context':local,'artifacts':artifacts,'formal':json.loads((lane/'formal/replay.json').read_text()),'remaining':['Independent validation of written proof','Nonroutine eligibility and novelty/subsumption decision','Full literal Lean source endpoint, including published dependencies','Final paper and extracted strict endpoint replay'],'mutations':'Only files inside assigned lane. No git, posting, messages, account/browser mutations, or ledger edits.'}
(lane/'provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print('Wrote provenance:',len(sources),'source records,',len(local),'context records,',len(artifacts),'artifact hashes')
