import resource,signal,os,pathlib,json,hashlib,datetime,re
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));signal.alarm(140);os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=pathlib.Path(__file__).resolve().parent;b=p.parent;r=b/'expanded-corpus-r292';root=pathlib.Path('/home/mj-kang/Documents/Dev/math')
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def out(n,d):(p/n).write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
entries=[]
def read(q,depth,kind='actual bounded read'):
 entries.append({'path':str(q.resolve()),'sha256':sha(q),'bytes':q.stat().st_size,'depth':depth,'kind':kind})
for n in ['TASK.txt','frozen-inputs.json']:read(p/n,'Full task / all153 frozen path-hash entries processed')
for q in [root/'openai-proof-research/AGENTS.md',b/'AGENTS.md',b.parent/'AGENTS.md']:read(q,'Full applicable instructions')
for n in ['ORDINARY-ATTEMPTS.md','SEARCH-AND-LIMITS.md']:read(r/n,'Full document')
for n in ['results.json','literal-provenance.json']:read(r/n,'Complete keyed369163 record, not other IDs')
read(r/'raw/369163.jsonl','Literal raw record inspected; exact statement/provenance retained')
for n in ['source-read-inventory.json','http-receipts.jsonl','registry-review.json','source-family-history.txt','history-focused.txt','history-reconciled-excerpts.txt','resource-and-reservation.json']:
 read(r/n,'369163/source-family/access/registry/resource relevant entries; output of broad history excerpts truncated, no full-file semantic-read claim')
for n in ['ledger.json','STATUS.md']:read(b/n,'Current count and relevant keyed entries / status leading accepted summaries')
for q in [b.parent/'ledger.json',b.parent/'prior-campaign-context.json']:read(q,'Accepted/excluded ID/title/source-family projections and relevant hits; not full proof packets')
for q in [root/'openai-proof-research/sources/upstream.json',root/'openai-proof-research/sources/CONTENTS.md']:read(q,'Full pin / bounded relevant-name catalogue screen')
read(r/'http/369163.html','§1 field and local definitions; §3 decomposition; full Thm3.3 proof; §5.1 through full Lemma5.7 and upper witnesses; other sections not exhaustively read')
read(r/'http/crown-v1.html','Conj5.6 and full adjacent Lemma5.7 proof; §3/§5.1 textual equality compared below')
for n,depth in {
'current.abs':'Version history current live, journal acceptance comment; same bytes as r292',
'nmsu.pdf':'Text-converted; §5.1 constructions, mixed proof and conjecture, earlier numbering; remainder not fully read',
'nmsu.txt':'§5.1 actual text, including source constructions and mixed proof; not full manuscript',
'journal.html':'Landing metadata and explicit subscription access only; full body unread HOLD',
'domination.html':'Prop2.15 statement; Thm3.2, Lemma3.5 and Prop3.6 full proofs; edge-colon Thm3.4 statement, original proof unread',
'cuts.html':'Defs2.3,4.6; Thm3.3,3.5,4.15 full proofs; Cor4.14 proof; portions Lem4.3/Prop4.13; full dependency audit HOLD',
'cuts.abs':'v1 submission history; inconsistent internal HTML manuscript date noted',
'liwski.html':'§3 definitions, Lem3.8 full proof and Thm3.6 full proof, cited Thm3.9; H and Thm4.2 conditions/proof inspected in part; no full-paper read',
'liwski.abs':'Metadata/version routing only',
'openai.html':'Current exact head only',
'omega.html':'Current exact head only',
'pool.html':'Current exact head only',
'omega-readme.md':'Current pinned README bounded relevant-name screen; no theorem hit'
}.items():read(p/'http'/n,depth)
read(r/'http/openai-CONTENTS-current.md','Pinned to unchanged live head; bounded ID/source/crown/binomial-edge/local-v screen')
read(r/'http/pool-projects-current.yml','Same live head as r292; bounded relevant-name screen, no matching project')
out('source-read-inventory.json',entries)
# Relevant sections of the two available source versions are byte compared as text, not a mathematical search.
s1=(r/'http/crown-v1.html.txt').read_text();s2=(r/'http/369163.html.txt').read_text();cmp={}
for a,z in [('3. Krull dimension','4. Projective dimension'),('5. v-number','5.2. v-numbers')]:
 def section(s):i=s.find(a);j=s.find(z,i);return s[i:j]
 t1,t2=section(s1),section(s2);cmp[a]={'v1_chars':len(t1),'v2_chars':len(t2),'equal':t1==t2,'v1_sha256':hashlib.sha256(t1.encode()).hexdigest(),'v2_sha256':hashlib.sha256(t2.encode()).hexdigest()}
out('version-section-comparison.json',cmp)
heads={'openai':'4eaee87548250b2682affda7d05d947c05554bae','omega':'81c61ee7bd24606a14a1e078becd924ecaf81082','pool':'6814773d2f980caadeb58ea33cae432cf824b60c'}
reg={'heads':heads,'chronology':'All heads fetched 2026-11-06T02:12 UTC; OpenAI and LeanPool unchanged from r292; Omega changed but README hash unchanged. No full commit history/theorem chronology audit.','scope':'Bounded routing only; no complete absence clearance.','screens':[]}
for q in [r/'http/openai-CONTENTS-current.md',r/'http/pool-projects-current.yml',p/'http/omega-readme.md']:
 s=q.read_text();reg['screens'].append({'path':str(q.resolve()),'sha256':sha(q),'patterns':'369163|2507.03889|crown graph|binomial edge|vasconcelos|local v-number','hits':[s[max(0,m.start()-100):m.end()+200] for m in re.finditer(r'369163|2507\.03889|crown graph|binomial edge|vasconcelos|local v-number',s,re.I)]})
out('registry-review.json',reg)
prov=json.loads((r/'literal-provenance.json').read_text())['369163']
out('results.json',{'369163':{'mathdb_id':369163,'scope':'All fields K; all n>=4; every T in actual cut-point family; actual polynomial binomial edge ideal and exact colon local minimum','ordinary_status':'complete proof candidate, self-reviewed only','proof':'ORDINARY-PROOF.md','key_step':'Vertex support restriction retaining a_i; mixed prime M_ij kills every remaining possible cubic class at Q_i','gates':{'literal_scope':'PASS ordinary','ordinary_mathematics':'COMPLETE CANDIDATE, independent review pending','source_current_and_history':'HOLD journal body and exhaustive citing/corrections incomplete','bounded_subsumption':'HOLD; explicit C two-component bridge recorded, full-side not covered by inspected general bound','novelty_significance':'HOLD, no novelty claim','independent_review':'NOT RUN','Lean_literal_endpoint':'NOT RUN, no handoff','paper_replay':'NOT RUN'},'accepted_credit':0,'campaign_count':'52/60 unchanged','raw_provenance':prov,'execution_decision':'No Pi/Lean execution; root must qualify sources/novelty and independently review first','forbidden_actions_performed':False}})
# Fresh frozen after verification includes every path.
d=json.loads((p/'frozen-inputs.json').read_text());rows=[]
for f,h in d.items():
 q=pathlib.Path(f);a=sha(q) if q.exists() else None;rows.append({'path':f,'expected':h,'actual':a,'ok':a==h})
out('frozen-after.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'count':len(rows),'all_ok':all(x['ok'] for x in rows),'files':rows})
with (p/'jobs.jsonl').open('a') as f:f.write(json.dumps({'job':'all local/tool jobs','state':'reaped','exec_chunk_ids':['06e6e3','a97100','4b8798','274814','402450','7e36d9','fb05ce','314c36','67d712','3ce13a','debff8','e6d71a','3c8130','50e16c','18a7f0','892753','61f0e1','c330f2','082735','f251e2','d5a58c','7f968e','334b74','a35f53'],'sessions':{'20729':'reaped exit0','82962':'reaped exit0'},'failure':'3ce13a exit1 missing bs4 before network; no denied source fetch repeated','note':'fetch_more.py reused logger job label fetch_sources.py; distinguished by chunk18a7f0/892753. Initial navigation/baseline and shell writes lacked full envelope; all completed synchronously. Later read scripts capped. Finalization running synchronously with full caps.'})+'\n')
# Hash artifacts except the manifest itself, avoid self-reference.
out('artifact-hashes.json',{str(q.relative_to(p)):sha(q) for q in sorted(p.rglob('*')) if q.is_file() and q.name!='artifact-hashes.json'})
print(json.dumps({'frozen_count':len(rows),'frozen_all_ok':all(x['ok'] for x in rows),'inventory_entries':len(entries),'version_comparison':cmp,'credit':0,'jobs':'no live jobs'}))
