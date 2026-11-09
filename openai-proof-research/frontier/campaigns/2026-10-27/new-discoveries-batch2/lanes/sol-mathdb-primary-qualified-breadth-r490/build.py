from pathlib import Path
import json,hashlib,re,datetime
from fractions import Fraction
O=Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r489'
def dump(n,x): (O/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def sha(z):return hashlib.sha256(z).hexdigest()
rows=json.loads((O/'assigned-records.json').read_text());notes={int(a): (d,p,t) for a,d,p,t in (s.split('|',3) for s in (O/'assessments.txt').read_text().splitlines())};assert len(notes)==50
src={r['mathdb_id']:r for r in json.loads((O/'source-bindings.json').read_text())};dis=[];passages=[]
for x in rows:
 r=x['record'];id=r['mathdb_id'];d,anchor,reason=notes[id];text=(O/'sources'/f'{id}.txt').read_text();h=re.search(re.escape(anchor),text,re.I)
 if h:
  lo=max(0,h.start()-300);hi=min(len(text),h.end()+1400); start=text[:lo].count('\n')+1;end=text[:hi].count('\n')+1;fragment=text[lo:hi];scope='selected target passage'
 else:
  start=1;end=1;fragment='';scope='target anchor not recovered; related passages read as described in assessment'
 passages.append(dict(mathdb_id=id,source_url=src[id]['url'],text_path=src[id]['text']['path'],anchor=anchor,first_line=start,last_line=end,scope=scope,text=fragment))
 proof={349817:'concluding Theorem 4.7 proof read; supporting magnitude/sign lemmas not fully replayed',349959:'Theorem 3 proof and appendix Lemma 5 read; external reachability dependency not replayed',350050:'Theorem 1.3/1.4 construction proofs read; external Kleitman/discrepancy dependencies not replayed',350892:'successor 351437 Section 3 equations and bijective reduction passages read; external enumeration dependencies not replayed'}.get(id,'no complete proof review')
 dis.append(dict(mathdb_id=id,literal_statement=r['statement'],primary_url=r['source_url'],canonical_url=r['canonical_url'],original_chunk=x['original_chunk'],original_line=x['original_line'],statement_utf8_sha256=sha(r['statement'].encode()),canonical_record_sha256=sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),disposition=d,technical_reason=reason,source_locator=dict(anchor=anchor,text_first_line=start,text_last_line=end,anchor_located=bool(h)),evidence_levels=dict(literal='complete individual statement/quantifier assessment',primary='selected passages only; entire PDF retained',whole_body_review=False,proof=proof,dependency='no complete dependency audit',successor='source-internal results inspected; broader successor search incomplete; 350892 additionally matched to retained assigned successor 351437',registry='HOLD: current registry unavailable; zero MathDB requests; no novelty clearance'),duplicate_prior_status='r304/r363 and intake exclusion controls frozen; exact assigned-ID historical match scan retained separately; no global absence claim',accepted_credit=0))
dump('dispositions.json',dis);dump('selected-passages.json',passages);dump('proposals.json',[])
# Bounded exact checks, no finite-to-universal inference.
checks=[]
for d in range(5,21):
 vals=[Fraction(1,d)]*(d-1)+[Fraction(1,2*d)]*2;assert sum(vals)==1 and sorted(set([d]*(d-1)+[2*d]*2))[-2]==d
checks.append(dict(mathdb_id=351253,check='Fraction arithmetic for repeated-denominator construction d=5..20',status='PASS',scope='literal wording only; all-d algebraic identity preserved in literal-notes.md, not a distinct-denominator result'))
assert (1-Fraction(1,4)+Fraction(1,100))*5-1==Fraction(14,5)<4
checks.append(dict(mathdb_id=351063,check='K5 singleton-part degree threshold k=5 r=2 gamma=1/100: 4>=14/5; odd cardinality precludes a perfect matching',status='PASS',scope='missing-divisibility defect only'))
# Enumerate inversion subsets for the directed triangle: empty set cyclic; any two-vertex inversion acyclic.
edges={(0,1),(1,2),(2,0)}
def acyclic(e):return not (all((i,(i+1)%3) in e for i in range(3)) or all(((i+1)%3,i) in e for i in range(3)))
assert not acyclic(edges)
for a,b in [(0,1),(1,2),(2,0)]:
 e=edges-{(a,b)}|{(b,a)};assert acyclic(e)
checks.append(dict(mathdb_id=350634,check='Directed C3 has one vertex-disjoint cycle and inversion number exactly 1; log(1)=0',status='PASS',scope='all-k endpoint error only; no asymptotic refutation'))
dump('bounded-checks.json',checks)
# Filter prior administrative evidence to assigned IDs only, do not expand any historical bindings.
ids={r['record']['mathdb_id'] for r in rows};hist=[]
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 p=L/'root-mathdb-accepted-exclusions-r304'/n;t=p.read_text()
 hits=[i for i in sorted(ids) if re.search(r'(?<!\d)'+str(i)+r'(?!\d)',t)]
 hist.append(dict(path=str(p),exact_id_text_matches=hits,scope='administrative text match only; no literature clearance'))
dump('prior-assignment-scan.json',hist)
dump('coverage.json',dict(baseline_reported_literal_reviews=3483,this_lane_individual_literal_reviews=50,proposed_reported_total_if_root_reconciles=3533,root_reconciliation_performed=False,primary_pdfs_retained=50,derivative_texts_bound=50,whole_bodies_reviewed=0,qualified_briefs=0,accepted_credit=0,counts=dict(additional=9,total=39,next=40),current_registry='HOLD',scope='literal assessments individually recorded; primary passages selected; no exhaustive corpus/literature/proof/dependency review'))
dump('provenance.json',dict(date=datetime.datetime.now(datetime.timezone.utc).isoformat(),corpus='20 original chunks checked in place, no copies',frozen_inputs=8,intake='r489 exact manifest and direct original/copy bindings checked without running upstream code',external_access='50 successful arxiv primary PDF requests, no MathDB/Google/GitHub/ScienceDirect/browser requests',access_limits='Inherited 429 HOLD and all parked routes preserved; no current proof registry clearance',source_evidence='PDFs retained; hash recorded before extraction, derivative hash before searches; latest retrieved PDF bytes identify actual versions, not assumed original versions',mathematical_status='no promoted theorem; integrity PASS must not be read as mathematical or novelty PASS'))
# Add explicit instruction/helper/pinned metadata references without recursively expanding them.
refs=json.loads((O/'flat-bindings.json').read_text())
for p in [L.parent/'AGENTS.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md')]:
 z=p.read_bytes();refs.append(dict(path=str(p),size=len(z),sha256=sha(z)))
refs+=json.loads((O/'pinned-admin-bindings.json').read_text());dump('flat-bindings.json',list({r['path']:r for r in refs}.values()))
print('built',len(dis),'dispositions;',len([x for x in passages if x['text']]),'target anchors located;',hist)
