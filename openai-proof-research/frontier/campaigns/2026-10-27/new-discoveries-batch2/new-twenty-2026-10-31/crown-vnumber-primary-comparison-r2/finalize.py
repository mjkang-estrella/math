from pathlib import Path
import json, hashlib, re, datetime
q=Path(__file__).resolve().parent;p=q.parent;r=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
def put(n,v): (q/n).write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
inventory=[]
def inv(f,depth):
 f=Path(f);inventory.append(dict(path=str(f),bytes=f.stat().st_size,sha256=sha(f),read_depth=depth))
for f in [r/'AGENTS.md',p.parent/'AGENTS.md',p/'AGENTS.md',q/'TASK.txt',p/'crown-vnumber-parent-review-integration-r2.json',p/'crown-vnumber-independent-review-r1/REVIEW.md',p/'crown-vnumber-source-ideation-r1/REVIEW.md',p/'crown-vnumber-source-ideation-r1/ORDINARY-PROOF.md',p/'crown-vnumber-root-proof-r1/ORDINARY-PROOF.md']:
 inv(f,'Full instructions/review/proof text read; ordinary algebra audit not repeated. Large combined initial outputs had truncation; independent REVIEW tail and author REVIEW separately reread.')
inv(p/'crown-vnumber-source-ideation-r1/source-read-inventory.json','Read inherited depth claims and source routing; not adoption of their full source audit as this lane own reading.')
for lane in ['crown-vnumber-independent-review-r1','crown-vnumber-source-ideation-r1']:
 inv(p/lane/'http-receipts.jsonl','Full relevant URL/access/version receipt entries read; no failed route retried.')
inv(p/'crown-vnumber-independent-review-r1/registry-review.json','Full bounded previous heads/screen/chronology report.')
inv(p/'STATUS.md','Opening count and acceptance summary only.')
for f in [p/'ledger.json',p.parent/'ledger.json',p.parent/'prior-campaign-context.json']:
 d=json.loads(f.read_text());hits=[]
 def walk(v,path=''):
  if isinstance(v,dict):
   for k,a in v.items(): walk(a,path+'/'+str(k))
  elif isinstance(v,list):
   for i,a in enumerate(v):walk(a,path+'/'+str(i))
  elif re.search(r'369163|2507\.03889|crown|binomial.edge',str(v),re.I):hits.append(dict(key=path,value=v))
 walk(d)
 put('history-'+f.parent.name+'-'+f.name,dict(path=str(f),sha256=sha(f),depth='Machine targeted ID/title/source-family projection; not whole historical theorem-body read',hits=hits))
 inv(f,'Count/keyed ancestor context and accepted/excluded source-family projections only; initial broad output truncated. Saved targeted machine projection is not semantic full-read evidence.')
inv(p/'expanded-corpus-r292/history-focused.txt','Focused historical source-family excerpts; broad display truncated at tool output limit, no whole-family clearance.')
inv(r/'sources/upstream.json','Full immutable pin.')
inv(p/'crown-vnumber-source-ideation-r1/http/journal.html','Relevant actual publisher body read: arbitrary field, §3 cut primes/Thm3.3 and proof, all §5.1 Lem5.1 through Lem5.7 proof, dates/access/correction metadata. Other sections not fully read. Initial display truncation followed by separate complete Lem5.7 read.')
inv(q/'http/older-journal.html','Relevant publisher body read: §2 C convention/Def2.3, §3.1 definitions/Theorems3.3,3.5 full proofs, §4 two-component setup/Def4.6, full Prop4.13, Cor4.14/Thm4.15 proofs, publisher dates. Earlier auxiliary proofs not all audited; remaining sections heading/routing screen only.')
inv(q/'http/older-v1.pdf','Text-converted with pdftotext; title stamp/date, §2 convention/Def2.3, full Thm3.3/3.5 proofs, Cor4.14 and Thm4.15 statements/proofs read. Not a full-paper/layout audit.')
inv(q/'http/older-v1.pdf.txt','Same targeted passages as PDF entry; source-text conversion, not visual layout review.')
inv(p/'crown-vnumber-source-ideation-r1/http/cuts.html','Internal date, minimal-cut wording and relevant theorem routing; inherited complete proof audit not repeated.')
for n in ['older.abs','newer.abs']:
 inv(q/'http'/n,'Actual current submission/version history, DOI/version routing read; not theorem body.')
inv(q/'http/generalized.pdf','Actual source scope/Setting4.1, Thm4.12 statement and initial proof read; headings and crown citation screened. Not full-paper or proof audit.')
inv(q/'http/generalized.abs','Metadata routing fetched, not independently relied on for theorem scope; PDF read.')
for n in ['liwski-author.html','liwski-repository.html','kumar-author.html']:
 f=q/'http'/n
 if f.exists(): inv(f,'Author repository link or redirect-shell routing only; no accessible authenticated accepted-manuscript identity established.')
heads={}
for n in ['openai','pool','omega']:
 f=q/'http'/(n+'.html');heads[n]=re.findall(r'"currentOid":"([0-9a-f]{40})"',f.read_text())[0];inv(f,'Current repository head metadata only; not full tree/read history.')
cf=q/'http/omega-head-commit.html';cs=cf.read_text();paths=sorted(set(re.findall(r'"path":"([^"]+)"',cs)));dates=re.findall(r'"(?:committedDate|authoredDate)":"([^"]+)"',cs)
inv(cf,'Head commit dates and changed path names screened; diffs/theorem bodies and intervening commits not semantically read.')
screens=[]
for f in [r/'sources/CONTENTS.md',p/'expanded-corpus-r292/http/openai-CONTENTS-current.md',p/'expanded-corpus-r292/http/pool-projects-current.yml',q/'http/omega-readme-current.md']:
 lines=f.read_text().splitlines();hits=[dict(line=i+1,text=t[:1200]) for i,t in enumerate(lines) if re.search(r'369163|2507\.03889|2507\.02161|2610\.18213|binomial.edge|local.{0,5}v.number|crown',t,re.I)]
 screens.append(dict(path=str(f),sha256=sha(f),hits=hits,depth='Machine routing screen only; not absence evidence'));inv(f,'Machine targeted ID/source/name routing screen, not whole-index semantic reading or import audit.')
put('registry-review.json',dict(utc=now(),heads=heads,previous_heads=json.loads((p/'crown-vnumber-independent-review-r1/registry-review.json').read_text())['heads'],omega_current_head_dates=dates,omega_changed_paths=paths,omega_head_dates_utc='2026-11-06T02:34:04Z',scope='Only current head commit metadata/path screen, not all intervening changes; no head date used as theorem priority date.',screens=screens,clearance=False))
put('read-inventory.json',inventory)
residuals=['Publisher institutional-access banner: relevant body observed via ordinary no-credential HTTP; unrestricted-public/OA status not certified; retain acquisition-policy HOLD if parent public-only rule excludes it.','Cause of current older HTML August24,2026 date versus actual v1 July2025 stamp/internalJuly4 remains unexplained; dated PDF already contains theorem4.15, but every HTML sentence is not backdated.','Correction/citation search bounded: no exhaustive Crossmark or citing-tree clearance.','Omega changed beyond unchanged README; entire current trees/imports/intervening commits not audited.','Formal implementation/replay and acceptance handled separately.']
verdicts=dict(O1=dict(verdict='RELEVANT VOR BODY COMPARISON PASS; BOUNDED CORRECTION CHECK; PUBLIC-COPY QUALIFICATION',body='Frozen publisher response contains complete §5.1; conjecture5.6 retained; no full-side lower theorem; previous landing-only classification corrected only here.',residual=residuals[0]),O2=dict(verdict='DATED V1 AND JOURNAL SCOPE RESOLVED; HTML DATE PROVENANCE HOLD',scope='Both actual dated PDF and journal Thm4.15: connected graph, cut-point set leaving exactly2 components, overC. Q/R/M give4; PX/PY leave n>=4 components. Thm3.5 equality requires additional radicality; no all-field transfer supplied.',chronology='arXiv v1 stampJuly2,2025; internalPDFJuly4,2025; journal receivedJuly29,2025 acceptedMar5,2026 VORApr9,2026; currentHTMLinternalAug24,2026 not a new version-history entry.'),O3=dict(verdict='UNCHANGED; NO NEW APPLICABLE SPECIFIC EVIDENCE FOUND',scope='Current abstract unchanged: v2Oct16,2026. Prior v^-_X=3 and failedH inherited, not reproved.'),source_fidelity='INHERITED ordinary/literal PASS retained; relevant VOR bodies now inspected with explicit access qualification.',prior='PARTIAL PRIOR ESTABLISHED; NO COMPLETE SUBSUMPTION BRIDGE FOUND',novelty='QUALIFIED BOUNDED FAVORABLE RECOMMENDATION; STRICT GLOBAL PRIORITY NOT CERTIFIED',significance='QUALIFIED FAVORABLE uniform completion; root final HOLD; no ease-only exclusion',acceptance='HOLD',credit=0,campaign_count=52,campaign_target=60)
put('review.json',dict(utc=now(),mathdb_id=369163,verdicts=verdicts,residuals=residuals,all_hypothesis_subsumption_bridge=None,no_bridge_reason='No actual prior theorem covers full-side n-component lower4/allfields under verified hypotheses. Q/M bridge fully specified in REVIEW.md.',forbidden_actions_performed=[],pi_lane_touched=False,ordinary_algebra_reaudited=False,bounded_jobs_reaped=True,frozen_expected=79))
put('source-version-review.json',dict(utc=now(),O1=verdicts['O1'],O2=verdicts['O2'],O3=verdicts['O3'],correction_scope='No attached notice in two publisher response screens; finite exact DOI/title correction searches, no identified actual correction; not exhaustive.',comparison='Relevant mathematical statements/proof routes; no byte identity claim for publisher versus arXiv.',source_receipts='http-receipts.jsonl and frozen author http-receipts.jsonl'))
put('search-receipts.json',dict(utc_window='2026-11-06 02:36 through 02:39 UTC (bounded approximate orchestration window; exact managed request timestamps unavailable)',batches=[['10.1007/s10801-025-01464-w correction full text','10.1007/s13348-026-00511-4','Liwski 2507.02161 pdf','2610.18213 correction'],['Binomial edge ideals of crown graphs pdf Kumar Tran','Liwski 00511 correction','2610.18213 Liwski v3'],['Binomial edge ideals of crown graphs Correction site:link.springer.com','minimal cuts and cycle graphs Correction site:link.springer.com','The v-number of generalized binomial edge ideals of some graphs arxiv','crown graphs v-number Liwski lower bound']],second_batch_also_opened='https://www.kuleuven.be/wieiswie/nl/person/00165104',second_batch_raw_not_retained=True,tool='web.run',http_status=None,bytes=None,raw_sha256=None,error='Managed search does not expose underlying HTTP response/status/raw bytes or internal CPU/AS caps.',read_depth='Routing excerpts; not relied on for exact full theorem, OA-copy authorization or correction absence.',raw_results_retained=['search1-managed.json','search3-managed.json']))
with (q/'jobs.jsonl').open('a') as f:f.write(json.dumps(dict(utc=now(),job='bootstrap-and-auxiliary-synchronous-commands',state='all exited/reaped',deviation='Initial navigation and all direct inline shell read/write/inspection commands outside bounded.py lacked full CPU/AS/affinity/wall envelope; observed returned synchronously; no retroactive compliance claim.',managed_search='No internal cap claims',sessions_reaped=[95694,48592],other_background_jobs=0))+'\n')
expected=json.loads((q/'frozen-inputs.json').read_text());checks={f:dict(expected=h,actual=sha(Path(f))) for f,h in expected.items()};ok=all(v['expected']==v['actual'] for v in checks.values())
put('frozen-after.json',dict(utc=now(),count=len(checks),passed=ok,files=checks))
assert len(checks)==79 and ok
print(json.dumps(dict(frozen_count=len(checks),frozen_pass=ok,heads=heads,read_inventory_entries=len(inventory),acceptance='HOLD',credit=0)))
