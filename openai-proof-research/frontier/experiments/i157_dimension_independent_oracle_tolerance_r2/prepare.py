"""I157 flat evidence preparation. Does not execute inherited code or seal."""
from pathlib import Path
import hashlib,json,re,time
R=Path(__file__).resolve().parents[3]
S='frontier/sources/i157_dimension_independent_oracle_tolerance_r2'
OLD='frontier/sources/i154_dimension_independent_oracle_tolerance'
def read(p): return (R/p).read_bytes()
def data(p): return json.loads(read(p))
def sha(b): return hashlib.sha256(b).hexdigest()
def save(p,x): (R/p).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
assert not (R/S/'seal.json').exists()
assert not (R/S/'flat-check.json').exists(), 'preparation traversal already recorded'
inh=data(OLD+'/inheritance.json')
refs={x['path']:x['sha256'] for x in inh['immutable']}
for p,h in data(OLD+'/seal.json')['sha256'].items(): refs[p]=h
refs[OLD+'/seal.json']=sha(read(OLD+'/seal.json'))
for p in ['frontier/iterations/iteration154-dimension-independent-oracle-tolerance-task.json','frontier/experiments/i154-parent-verification.json','AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json']:
    refs[p]=sha(read(p))
assert refs['frontier/iterations/iteration154-dimension-independent-oracle-tolerance-task.json']=='0fa43c233f6032d38f3b905cac2253321303e3a300342112ae8716e504897d97'
assert refs['frontier/iterations/iteration152-algorithmic-sampling-reconstruction-discovery-task.json']=='f13a8eb19fe9ee8cdd1a6fbeb6618529a48c0599f08a84272be5b68570bf7379'
for p,h in sorted(refs.items()):
    assert not re.search(r'/(?:i|iteration)(155|156)[-_]',p),p
    assert p not in inh['live_ledgers']
    assert sha(read(p))==h,p
snap=[]
for p in inh['live_ledgers']:
    dest=S+'/snapshots/'+p; (R/dest).parent.mkdir(parents=True,exist_ok=True)
    b=read(p); (R/dest).write_bytes(b); snap.append(dict(path=p,snapshot=dest,sha256=sha(b)))
save(S+'/snapshots.json',snap)
save(S+'/immutable.json',[dict(path=p,sha256=h) for p,h in sorted(refs.items())])
lexpaths=inh['lexical_records']+[OLD+'/lexical-search.json']
lex=[data(p) for p in lexpaths]
patterns={}
for item in lex:
    for k,v in item['patterns'].items():
        assert k not in patterns
        patterns[k]=v
rx={k:re.compile(v) for k,v in patterns.items()}; found={k:[] for k in rx}
domainpath='frontier/sources/i112_inverse_boundary_discovery/search-domain.json'
treepath='frontier/sources/i112_inverse_boundary_discovery/snapshots/sources/preprints-tree.json'
domain=data(domainpath);tree=data(treepath)['tree'];blobs={x['path']:x for x in tree if x['type']=='blob'}
assert len(tree)==13223 and len(domain)==len(blobs)==10373
assert sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree)==749
assert {x['path'] for x in domain}==set(blobs)
t=time.monotonic();pdfs=0
for x in domain:
    b=read(x['local']);o=b if x['local']==x['original_local'] else read(x['original_local'])
    assert sha(b)==x['sha256'] and sha(o)==x['original_sha256'],x['path']
    assert hashlib.sha1(b'blob '+str(len(o)).encode()+b'\0'+o).hexdigest()==x['git_sha']==blobs[x['path']]['sha']
    pdfs+=x['kind']=='outside_pdf'
    for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
        for k,pat in rx.items():
            matches=list(pat.finditer(line))
            if matches: found[k].append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(m.span()) for m in matches]))
assert pdfs==776
for item in lex:
    for k,v in item['results'].items(): assert found[k]==v,k
save(S+'/flat-check.json',dict(status='PASS',tree_entries=13223,manuscripts=749,original_blob_positions=10373,pdf_text_bindings=pdfs,domain=domainpath,domain_sha256=sha(read(domainpath)),tree=treepath,tree_sha256=sha(read(treepath)),lexical_records=lexpaths,lexical_lines={k:len(v) for k,v in found.items()},lexical_occurrences={k:sum(len(x['spans']) for x in v) for k,v in found.items()},elapsed_seconds=time.monotonic()-t,preparation_traversals=1,corpus_copies=0,ancestor_executions=0,pdf_reextractions=0,scope='Byte and exact lexical-occurrence verification; no semantic-reading or correctness claim.'))
print(json.dumps({'status':'PASS','immutable':len(refs),'corpus':len(domain),'pdfs':pdfs,'elapsed':time.monotonic()-t}))
