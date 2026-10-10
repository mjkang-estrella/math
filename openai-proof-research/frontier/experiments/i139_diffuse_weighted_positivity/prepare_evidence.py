"""Preparation only, I139 owned paths only. Flat traversal; no inherited execution."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i139_diffuse_weighted_positivity';OLD='frontier/sources/i136_birational_positivity_discovery'
sha=lambda b:hashlib.sha256(b).hexdigest()
def data(p):return json.loads((R/p).read_text())
def save(p,o):(S/p).write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n')
assert not (S/'seal.json').exists()
old=data(OLD+'/inheritance.json');refs={x['path']:x['sha256'] for x in old['immutable']};ledgers=old['live_ledgers']
def add(p,h=None):
 assert p not in ledgers and not re.search(r'/(?:i|iteration)(137|138)[-_]',p),p
 h=h or sha((R/p).read_bytes())
 if p in refs:assert refs[p]==h,p
 refs[p]=h
sp=OLD+'/seal.json';h='b2027f24416364e79f6e05f6ecdee8e5328dcbf2e20c12d37cb8204936e15c2c';assert sha((R/sp).read_bytes())==h;add(sp,h)
for p,hh in data(sp)['sha256'].items():add(p,hh)
anchors=old['anchors']+[dict(base=OLD,seal=sp,sha256=h,inventory=OLD+'/inventory.json')]
for x in data(str(S.relative_to(R))+'/input-freeze.json'):
 if x['path'] not in ledgers:add(x['path'],x['sha256'])
man=data(str(S.relative_to(R))+'/read-manifest.json')
# These complete displayed readings predate the range-logging helper.
manual=[('AGENTS.md',1,100),('sources/upstream.json',1,1000),(OLD+'/context-reading.txt',1,4499),(str(S.relative_to(R))+'/direct-context.txt',1,537),('frontier/iterations/i136-birational-positivity-discovery.md',1,331),('frontier/experiments/i136-parent-verification.json',1,10000)]
for p,lo,hi in manual:
 b=(R/p).read_bytes();ls=b.decode().splitlines();hi=min(hi,len(ls));man['passages'].append(dict(local=p,start=lo,end=hi,line_count=len(ls),file_sha256=sha(b),passage_sha256=sha('\n'.join(ls[lo-1:hi]).encode()),ending=ls[hi-1],convention='splitlines; LF joined without appended LF',reading='Complete earlier display or full user-supplied report/parent content, byte-bound to original; context recovered in chunks'))
# Explicit complete current-version abstract records are read separately before sealing.
seen=set();out=[]
for p in man['passages']:
 key=(p['local'],p['start'],p['end'])
 if key not in seen:seen.add(key);out.append(p)
man['passages']=out;save('read-manifest.json',man)
for p in out:
 if not p['local'].startswith(str(S.relative_to(R))+'/'):add(p['local'],p['file_sha256'])
passages=old['inherited_passages']+data(OLD+'/read-manifest.json')['passages']
lex=old['lexical_records']+[OLD+'/lexical-search.json']
save('inheritance.json',dict(anchors=anchors,immutable=[dict(path=p,sha256=h) for p,h in sorted(refs.items())],inherited_passages=passages,lexical_records=lex,live_ledgers=ledgers,scope='One flat byte and corpus traversal; inherited verifiers and diagnostics never executed'))
save('reading-notes.json',dict(mandatory_context_completed_before_audit=True,mandatory_i136_sha256='fb761d762d453a405d6ce3a740f5c6ceea3c7863c372648aeed781d82ea306cd',direct_decoded_lines=537,inherited_decoded_lines=4499,inherited_context=OLD+'/context-reading.txt',inherited_coverage=OLD+'/context-coverage.json',context_complete_ranges=[[1,500],[501,1000],[1001,1550],[1551,1900],[1901,2250],[2251,2600],[2601,2920],[2921,3270],[3271,3610],[3611,3950],[3951,4300],[4301,4499]],recovery_ranges=[[125,225],[595,795],[1001,1320]],display_failures=['Initial broad recursive-context displays exceeded outer tool budget; all omitted pieces recovered in the ranges listed.','Combined H-reduction 580-767 and Ito 805-1000 display truncated; H-reduction 650-767 and Ito 805-867 recovered; other portions were visible.','Broad current-ledger and keyword inventories truncated. Only visible relevant status/scope passages credited, not full unrelated ledger histories.','Initial Evans v2 retrieval was not current; metadata identified v3, retrieved successfully and used for the scope comparison.','An rg primary heading inventory was truncated; this is not a proof read. Full credited proof ranges are separately listed.'],unread=['Evans earlier ironing and toric metric lemmas, not used as positivity premises','Dumnicki later bounded-multiplicity case enumeration','Biran original full article; Roé–Ross complete weighted operation and independent nef construction used instead','Ito earlier internal semigroup lemmas beyond the inherited complete relied-upon degeneration/comparison passages'],primary_versions={'Ito':'1202.6662v2','Roe-Ross':'0804.1662v1','Dumnicki':'math/0606716v1','Evans':'2605.27574v3'},normalization='splitlines; LF joined without appended LF. HTMLParser preserves MathML and TeX annotation duplication, collapses whitespace per nonempty line.',diagnostic_development='One standalone new-diagnostic development run passed before final immutable preflight; not claimed as an immutable replay. Preseal and final offline replay check all immutable bytes first. Inherited diagnostics never executed.'))
patterns={'diffuse_weighted_packing':r'(?i)(weighted.{0,50}(?:seshadri|jet|pack|degenerat)|(?:normal.cone|diagram.cut|support.partition|point.collision|multipoint).{0,35}(?:weight|nef|pack|degenerat)|(?:nef|pack).{0,35}(?:refin|unequal|nonhomogeneous))'}
rxs={k:re.compile(v) for k,v in patterns.items()};hits={k:[] for k in patterns};domain=data('frontier/sources/i112_inverse_boundary_discovery/search-domain.json')
for x in domain:
 b=(R/x['local']).read_bytes();o=b if x['local']==x['original_local'] else (R/x['original_local']).read_bytes()
 assert sha(b)==x['sha256'] and sha(o)==x['original_sha256']
 assert hashlib.sha1(b'blob '+str(len(o)).encode()+b'\0'+o).hexdigest()==x['git_sha']
 for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
  for key,rx in rxs.items():
   mm=list(rx.finditer(line))
   if mm:hits[key].append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
save('lexical-search.json',dict(patterns=patterns,results=hits,counts={k:dict(matched_lines=len(v),occurrences=sum(len(x['spans']) for x in v)) for k,v in hits.items()}))
print(json.dumps(dict(immutable=len(refs),inherited_passages=len(passages),new_passages=len(out),lexical_counts={k:len(v) for k,v in hits.items()})))
