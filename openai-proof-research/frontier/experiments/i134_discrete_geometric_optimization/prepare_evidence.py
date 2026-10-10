"""Development-only evidence preparation. Never imported by the verifier."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i134_discrete_geometric_optimization'
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
DRIFT={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def obj(p):return json.loads((ROOT/p).read_bytes())
def put(p,x):(ROOT/S/p).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
assert not (ROOT/S/'seal.json').exists(),'already sealed'
requests=[json.loads(l) for l in (ROOT/S/'read-requests.jsonl').read_text().splitlines()]
wrong=[r for r in requests if r['path'].endswith('/i05-parent-screen.md')]
reads=sorted({(r['path'],r['start'],r['end']):r for r in requests if r not in wrong}.values(),key=lambda r:(r['path'],r['start'],r['end']))
for r in reads:
 b=(ROOT/r['path']).read_bytes();assert sha(b)==r['sha256']
 ls=b.decode(errors='replace').splitlines();assert sha('\n'.join(ls[r['start']-1:r['end']]).encode())==r['passage_sha256']
 r['ending']=ls[r['end']-1]
 r['scope']='completed passage; overlapping truncated first displays completed by the rereads in read-history.json'
 if '/corpus/preprints/' in r['path']:r['pinned_url']='https://raw.githubusercontent.com/openai/math/'+PIN+'/preprints/'+r['path'].split('/corpus/preprints/',1)[1]
put('read-manifest.json',{'convention':'1-based inclusive splitlines; LF join, no appended newline; actual passages only, not semantic all-corpus coverage','passages':reads})
put('read-history.json',{
 'requests':len(requests),'unique_completed_passages':len(reads),'scope_error_excluded':wrong,
 'context':'Full decoded context and duplicate-prefix reading chronology is separately in context-reading.json. Immutable inheritance is not a claim of a new semantic read of every ancestor source.',
 'truncated_and_recovered':[
  {'display':'combined S introduction/consequences, K overview, U introduction','recovery':'K overview 1-126 and S consequences 1-137 were reread in full; U introduction 1-296 was complete in the visible output'},
  {'display':'C introduction 1-228 combined with web output','recovery':'175-228 completed the truncated ending'},
  {'display':'A main 1876-2036 in a combined call','recovery':'same full range reread separately'},
  {'display':'Bourne-Cristoferi 933-1078 combined with review headers, truncated around steps 5-6','recovery':'1020-1043 completed the proof ending; 1043-1070 was separately read'},
 ],
 'discovery_only_truncations':['initial 66075-token ledger display','broad source mapping grep 17462 tokens','current-ledger rg 7461 tokens','prior-header and external grep 11635 tokens','C geometry label grep 3813 tokens'],
 'failed_local_operations':['Attempt to read nonexistent I113 snapshots.json; actual inputs.json used instead.','Initial I125 parent stdout key lookup failed: KeyError; nested original_replay and ordering-only replay were subsequently decoded in full (context-reading.json).'],
 'retrievals':'All seven new frozen primary responses returned HTTP 200. Springer final URL has a cookie error query but the article body and proof ending are present. Initial Li-Liu v1 lead was superseded by actual current v2, not represented as a v2 proof read.',
 'verification_failures':[{'stage':'first read-only preseal, before seal','error':'ValueError: I125 original FAIL receipt','cause':'New verifier looked for the original canonical-inventory error in stderr; the immutable receipt stores its JSON error in stdout.','resolution':'Parse original stdout JSON and separately check ordering_only_replay stdout; no inherited artifact changed.'}]})

# Exact occurrence records over the union of actually read source lines.
patterns={'labels':r'\\label\{[^}]+\}', 'operations':r'stabil\w*|rigid\w*|defect\w*|thinn\w*|reserv\w*|periodi\w*|simultaneous|adaptive|deleted.jet|half.cell', 'versions':r'\[v[0-9]+\]|Submitted on|last revised|this version'}
occ={k:[] for k in patterns};lines_by_path={}
for r in reads:
 if r['path'].endswith('.tex') or r['path'].endswith('-abs.txt'):
  lines_by_path.setdefault(r['path'],set()).update(range(r['start'],r['end']+1))
for p,ns in sorted(lines_by_path.items()):
 ls=(ROOT/p).read_text().splitlines()
 for n in sorted(ns):
  for name,expr in patterns.items():
   for m in re.finditer(expr,ls[n-1],re.I):occ[name].append({'path':p,'line':n,'start':m.start(),'end':m.end(),'match':m.group(),'text':ls[n-1]})
put('focused-lexical.json',{'expressions':patterns,'flags':'IGNORECASE','positions':'1-based lines, zero-based Unicode-character half-open spans; every occurrence, deduplicated union of read lines','occurrences':occ,'counts':{k:len(v) for k,v in occ.items()}})

domain=obj('frontier/sources/i113_online_optimization_discovery/search-domain.json')
represented={d[k] for d in domain for k in ('local','original_local')}
refs={};queue=[];expanded=set()
def add(p,h=None):
 if p in DRIFT:return
 assert not re.search(r'(?:/i|iteration)(?:132|133)(?:[-_/])',p),p
 if p.startswith(S+'/'):return
 b=(ROOT/p).read_bytes();actual=sha(b);assert h is None or h==actual,(p,h,actual)
 if p in represented:return
 r={'path':p,'bytes':len(b),'sha256':actual}
 if p in refs:assert refs[p]==r
 else:refs[p]=r;queue.append(p)
def walk(x):
 if isinstance(x,list):
  for y in x:walk(y)
 elif isinstance(x,dict):
  if 'sha256' in x:
   for k in ('path','snapshot'):
    p=x.get(k)
    if isinstance(p,str) and (ROOT/p).is_file():add(p,x['sha256'])
   for k in ('original','live'):
    p=x.get(k)
    if isinstance(p,str) and not x.get('may_drift',x.get('drift',False)) and (ROOT/p).is_file():add(p,x['sha256'])
  if isinstance(x.get('text'),str) and 'text_sha256' in x:add(x['text'],x['text_sha256'])
  for y in x.values():
   if isinstance(y,(dict,list)):walk(y)
walk(obj(S+'/inherited-references.json'))
walk(obj('frontier/sources/i113_online_optimization_discovery/immutable-references.json'))
for r in reads:add(r['path'],r['sha256'])
for p in ['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md']:add(p)
for r in obj(S+'/context-manifest.json'):add(r['path'],r['sha256'])
# Only manifests and receipts in the required inheritance graph are expanded.
# The complete corpus mapping is reused by reference, never copied here.
while queue:
 p=queue.pop(0)
 if p in expanded:continue
 expanded.add(p)
 if p.endswith('.json') and not any(t in p for t in ['search-domain.json','preprints-tree.json','iteration','snapshots/']):
  walk(obj(p))
put('immutable-flat.json',{'corpus_map':'frontier/sources/i113_online_optimization_discovery/search-domain.json','note':'Each auxiliary immutable input once; complete corpus originals/representations are checked from the inherited map, not copied. No inherited verifier or diagnostic execution.','files':[refs[p] for p in sorted(refs)]})
put('reading-references.json',[{'path':r['path'],'sha256':r['sha256'],'bytes':r['bytes']} for r in sorted({r['path']:r for r in reads if not r['path'].startswith(S+'/')}.values(),key=lambda r:r['path'])])
print(json.dumps({'read_passages':len(reads),'flat_auxiliary_files':len(refs),'lexical_occurrences':sum(map(len,occ.values()))}))
