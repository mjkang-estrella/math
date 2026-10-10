"""Preparation only. Flat by-reference inheritance and one lexical corpus traversal."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i142_uniform_algebraic_allocation';OLD='frontier/sources/i139_diffuse_weighted_positivity'
sha=lambda b:hashlib.sha256(b).hexdigest()
def data(p):return json.loads((R/p).read_text())
def save(p,o):(S/p).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
assert not (S/'seal.json').exists()
old=data(OLD+'/inheritance.json');refs={x['path']:x['sha256'] for x in old['immutable']};ledgers=old['live_ledgers']
def add(p,h=None):
 assert p not in ledgers and not re.search(r'/(?:i|iteration)(140|141)[-_]',p),p
 h=h or sha((R/p).read_bytes())
 if p in refs:assert refs[p]==h,p
 refs[p]=h
sp=OLD+'/seal.json';h='28c614c838e376ae389c51b240a094f3444a7bfc3feefba910eddaa58cefa59e';assert sha((R/sp).read_bytes())==h;add(sp,h)
for p,hh in data(sp)['sha256'].items():add(p,hh)
anchors=old['anchors']+[dict(base=OLD,seal=sp,sha256=h,inventory=OLD+'/inventory.json')]
for x in data(str(S.relative_to(R))+'/input-freeze.json'):
 if x['path'] not in ledgers:add(x['path'],x['sha256'])
man=data(str(S.relative_to(R))+'/read-manifest.json')
manual=[('AGENTS.md',1,100),('sources/upstream.json',1,1000),('frontier/sources/i136_birational_positivity_discovery/context-reading.txt',1,140),('frontier/iterations/i139-diffuse-weighted-positivity.md',1,10000),('frontier/experiments/i139-parent-verification.json',1,10000)]
for p,lo,hi in manual:
 b=(R/p).read_bytes();ls=b.decode().splitlines();hi=min(hi,len(ls));man['passages'].append(dict(local=p,start=lo,end=hi,line_count=len(ls),file_sha256=sha(b),passage_sha256=sha('\n'.join(ls[lo-1:hi]).encode()),ending=ls[hi-1],convention='splitlines; LF joined without appended LF',reading='Complete earlier direct display, or full I139 report/finalized parent supplied in user task, byte-bound to on-disk original.'))
seen=set();out=[]
for p in man['passages']:
 key=(p['local'],p['start'],p['end'])
 if key not in seen:seen.add(key);out.append(p)
man['passages']=out;save('read-manifest.json',man)
for p in out:
 if not p['local'].startswith(str(S.relative_to(R))+'/'):add(p['local'],p['file_sha256'])
passages=old['inherited_passages']+data(OLD+'/read-manifest.json')['passages'];lex=old['lexical_records']+[OLD+'/lexical-search.json']
save('inheritance.json',dict(anchors=anchors,immutable=[dict(path=p,sha256=h) for p,h in sorted(refs.items())],inherited_passages=passages,lexical_records=lex,live_ledgers=ledgers,scope='One flat byte/corpus traversal per replay. No inherited executable invocation.'))
save('reading-notes.json',dict(mandatory_context_completed_before_audit=True,mandatory_i139_sha256='4efafb184bde0e6cd5b908107e0eb29670209d4488129be0cd8b8647bda40bbc',direct_decoded_lines=649,inherited_direct_decoded_lines=537,inherited_recursive_decoded_lines=4499,recursive_context='frontier/sources/i136_birational_positivity_discovery/context-reading.txt',recursive_coverage='frontier/sources/i136_birational_positivity_discovery/context-coverage.json',complete_context_coverage='All decoded ordinary fields of I139 and I136 plus all 1263 pieces / 2021 field coverage records of complete recursive context. Read before original audit checkpoint.',display_failures=['Broad ledger/catalogue searches were truncated; only visible relevant scope/status passages credited, not full unrelated ledger histories.','Recursive context display 1101-1450 exceeded outer budget; omitted 1268-1295 recovered in full.','One initial primary read used wrong cwd and failed without reading or editing anything; rerun at project root succeeded.','Initial combined web search/metadata output was truncated; search discovery only, not proof-read evidence. Current relied-upon metadata fetched, frozen and explicitly read.','Biran/catalogue and later Trusiani heading rg inventories were truncated; not credited as proof reads. Exact proof or statement passages are logged separately.','Lu 1-240 display omitted part of 115-130; exact 115-130 recovered.'],unread=['Trusiani full analytic proof: statements A-C only used as scope comparison, not as positivity premises.','Evans analytic chain not re-audited; current abstract/version scope comparator only.','Lu later example and referenced vanishing machinery not audited, and no Lu conclusion used as premise.','Biran later asymptotic case enumeration, symplectic discussion and cited Shustin general theory not audited; complete used section 3 read, and independent nef family proof used.','Other unrelated manuscript bodies are byte/lexical inventoried, not claimed semantically read.'],primary_versions={'Ito':'1202.6662v2','Roe-Ross':'0804.1662v1','Dumnicki':'math/0606716v1','Biran':'alg-geom/9705018v2','Evans':'2605.27574v3','Trusiani':'1804.02306v5','Lu':'2605.25185v1'},normalization='splitlines; passage LF join without appended LF. HTML extraction preserves MathML/TeX duplicates and collapses whitespace on nonempty lines.',diagnostic_development='One new finite-diagnostic development run passed. Combinatorial stress cases K=2,4 test allocation identities only, not the local entrance theorem K>=400. Preseal/final replay check ALL immutable bytes before diagnostics; no inherited reruns.',retrieval_failures='No HTTP fetch failed in this I142 owned retrieval set. Historical failed/truncated retrieval receipts remain immutable by reference.'))
patterns={'uniform_algebraic_allocation':r'(?i)(adaptiv.{0,40}(?:simplex|simplic|jet|support|partit)|(?:weighted|multipoint).{0,50}(?:okounkov|interpolat|refine)|(?:graded|nef).{0,40}(?:saturat|bubble)|(?:dyadic|multiscale).{0,35}(?:pack|allocat))'}
rxs={k:re.compile(v) for k,v in patterns.items()};hits={k:[] for k in patterns};domain=data('frontier/sources/i112_inverse_boundary_discovery/search-domain.json')
for x in domain:
 b=(R/x['local']).read_bytes();o=b if x['local']==x['original_local'] else (R/x['original_local']).read_bytes()
 assert sha(b)==x['sha256'] and sha(o)==x['original_sha256'];assert hashlib.sha1(b'blob '+str(len(o)).encode()+b'\0'+o).hexdigest()==x['git_sha']
 for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
  for key,rx in rxs.items():
   mm=list(rx.finditer(line))
   if mm:hits[key].append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
save('lexical-search.json',dict(patterns=patterns,results=hits,counts={k:dict(matched_lines=len(v),occurrences=sum(len(x['spans']) for x in v)) for k,v in hits.items()}))
print(json.dumps(dict(immutable=len(refs),inherited_passages=len(passages),new_passages=len(out),lexical_counts={k:len(v) for k,v in hits.items()})))
