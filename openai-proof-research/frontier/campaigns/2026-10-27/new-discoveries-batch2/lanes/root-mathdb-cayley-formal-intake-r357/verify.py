from pathlib import Path
import hashlib,json,sys,datetime,tarfile
R=Path(__file__).resolve().parent
C=R/'frozen/sol-mathdb-cayley-source-formal-r353'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def check(p,h,s): assert p.stat().st_size==s and sha(p)==h,str(p)
def put(n,o): (R/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
bindings=json.loads((R/'bindings.json').read_text())
for e in bindings:
    check(Path(e['original']),e['sha256'],e['size']);check(R/e['copy'],e['sha256'],e['size'])
entries=json.loads((C/'manifest.json').read_text())['files']
assert {str(p.relative_to(C)) for p in C.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}==set(entries)
for n,e in entries.items(): check(C/n,e['sha256'],e['size'])
refs=[]
for name in ['input-bindings.json','administrative-bindings.json','audit-tool-binding.json']:
    x=json.loads((C/name).read_text());refs.extend(x if isinstance(x,list) else [x])
for e in refs: check(Path(e['path']),e['sha256'],e['size'])
sources=json.loads((C/'source-manifest.json').read_text())
for n,h in sources.items(): assert sha(C/n)==sha(C/'fresh-replay'/n)==h,n
with tarfile.open(C/'source-only.tar.gz') as t:
    assert len(t.getnames())==len(set(t.getnames()))
    assert set(t.getnames())==set(sources)|{'source-manifest.json'}
    for m in t:
        assert m.isfile() and m.mtime==0 and t.extractfile(m).read()==(C/m.name).read_bytes()
assert not list(C.rglob('*.olean'))
replay=json.loads((C/'fresh-replay/replay-receipt.json').read_text())
assert replay['component_status']=='PASS' and not replay['generated_partial_declarations']
assert replay['endpoint']=='Cayley.literal_source_claim_false'
def payload(): return {str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()}-{'manifest.json','verification-receipt.json'}
if sys.argv[1]=='build':
    put('manifest.json',{'files':[{'path':n,'sha256':sha(R/n),'size':(R/n).stat().st_size} for n in sorted(payload())]})
elif sys.argv[1]=='verify':
    own=json.loads((R/'manifest.json').read_text())['files'];assert payload()=={e['path'] for e in own}
    for e in own: check(R/e['path'],e['sha256'],e['size'])
    put('verification-receipt.json',{'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_bindings':len(bindings),'child_payloads':len(entries),'upstream_bindings':len(refs),'archive_members':len(sources)+1,'reported_declarations':replay['actual_declaration_count'],'independent_lean_replay':False,'novelty':'HOLD','acceptance':'HOLD'})
else: raise ValueError('build or verify')
print('PASS',sys.argv[1],len(entries),'child payloads',len(refs),'upstream bindings')
