from pathlib import Path
import hashlib,json,sys
sys.dont_write_bytecode=True
from primary_contracts import Blocks
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i17_six_point_ramsey_novelty_r3'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def run():
    inputs=read(S/'input-manifest.json')['files'];drift=[]
    for i in inputs:
        b=(ROOT/i['snapshot']).read_bytes();assert sha(b)==i['sha256'] and len(b)==i['bytes']
        live=ROOT/i['path'];h=sha(live.read_bytes()) if live.exists() else None
        if h!=i['sha256']:drift.append({'path':i['path'],'frozen_sha256':i['sha256'],'live_sha256':h})
    for name,h in [('frontier/iterations/i17-fresh-discovery.md','87b86401ed5c1d554715c78fa203e33acb0117fd8255357e495a882842c0feb8'),('frontier/reviews/i17-six-point-ramsey-r2.md','7c5dd819e5ffccd4b48b1db631c66e62fea5d0931af8b78b2ef62978416e5118')]:assert sha((S/'inputs'/name).read_bytes())==h
    cs=read(S/'inputs/frontier/sources/i17_six_point_ramsey_r2/source-contracts.json')
    for c in cs:
        b=(S/'inputs'/c['local']).read_bytes();git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert git==c['git_blob']
        t='\n'.join(b.decode().splitlines()[c['start_line']-1:c['end_line']]);assert t==c['exact_statement'] and sha(t.encode())==c['statement_sha256']
    pcs=read(S/'inputs/frontier/sources/i17_fresh_discovery/primary-statement-contracts.json')
    for c in pcs:
        t=(S/'inputs'/c['text_file']).read_text()[c['start_char']:c['end_char']];assert t==c['exact_statement'] and sha(t.encode())==c['statement_sha256']
    retrieved=read(S/'literature/manifest.json')
    for item in retrieved:
        assert 'error' not in item,item
        b=(ROOT/item['path']).read_bytes();assert sha(b)==item['sha256'] and len(b)==item['bytes']
        if 'text_path' in item:assert sha((ROOT/item['text_path']).read_bytes())==item['text_sha256']
    fresh=read(S/'primary-contracts.json');parsed={}
    for c in fresh:
        p=ROOT/c['file'];assert sha(p.read_bytes())==c['source_sha256']
        if c['file'] not in parsed:
            parser=Blocks();parser.feed(p.read_text());parsed[c['file']]={x['id']:x['passage'] for x in parser.blocks}
        t=parsed[c['file']][c['id']];assert t==c['passage'] and sha(t.encode())==c['passage_sha256']
    seals={};dependencies=[]
    for name in ['i17_fresh_discovery','i17_six_point_ramsey_r2']:
        old=read(S/f'inputs/frontier/sources/{name}/artifact-manifest.json')
        for i in old['files']:
            b=(ROOT/i['path']).read_bytes();assert len(b)==i['bytes'] and sha(b)==i['sha256'],i['path'];dependencies.append(i)
        seals[name]=len(old['files'])
    corpus=read(S/'corpus-audit.json')
    for i in corpus['verified_dependencies']:
        b=(ROOT/i['path']).read_bytes();assert sha(b)==i['sha256'] and len(b)==i['bytes'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==i['git_blob']
    result={'status':'PASS','frozen_inputs':len(inputs),'source_contracts':len(cs),'retained_primary_contracts':len(pcs),'fresh_primary_statement_inventory':len(fresh),'fresh_retrievals':len(retrieved),'prior_seals':seals,'corpus_files':len(corpus['verified_dependencies']),'live_input_drift':drift,'drift_policy':'Shared-index changes are reported separately and never replace frozen premises. Changed mathematical inputs require review.'}
    if '--record' in sys.argv:
        (S/'provenance-verification.json').write_text(json.dumps(result,indent=2)+'\n')
        (S/'external-dependencies.json').write_text(json.dumps({x['path']:x for x in dependencies+corpus['verified_dependencies']},indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':run()
