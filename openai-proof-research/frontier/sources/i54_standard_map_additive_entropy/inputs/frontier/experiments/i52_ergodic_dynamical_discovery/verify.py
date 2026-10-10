#!/usr/bin/env python3
"""Read-only I52 provenance and finite diagnostics; no analytic certification."""
import collections, hashlib, json, pathlib, subprocess, sys
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parents[3]
SRC=ROOT/'frontier/sources/i52_ergodic_dynamical_discovery'
EXP=ROOT/'frontier/experiments/i52_ergodic_dynamical_discovery'
COR=ROOT/'frontier/sources/i14_spectral_width_novelty_r3/corpus'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def blob(p):
    b=p.read_bytes();return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads(p.read_text())
def require(x,msg):
    if not x:raise AssertionError(msg)

def main():
    seal=read(SRC/'seal.json')
    for x in seal['artifacts']:require(sha(ROOT/x['path'])==x['sha256'],'artifact '+x['path'])
    inputs=read(SRC/'inputs-manifest.json');drift=[]
    for x in inputs:
        require(sha(SRC/'inputs'/x['path'])==x['sha256'],'frozen input '+x['path'])
        if sha(ROOT/x['path'])!=x['sha256']:
            if x['mutable_ledger']:drift.append(x['path'])
            else:raise AssertionError('immutable live input drift '+x['path'])
    tree=read(SRC/'inputs/sources/preprints-tree.json')
    require(len(tree['tree'])==13223 and not tree['truncated'],'complete tree metadata')
    names={x['path'].split('/')[1] for x in tree['tree'] if x['path'].count('/')>=2}
    require(len(names)==749,'manuscript count')
    index={x['path']:x for x in tree['tree'] if x['type']=='blob'}
    pin=read(SRC/'pinned-manifest.json')
    for x in pin:
        p=SRC/'pinned'/x['path'];require(sha(p)==x['sha256'],'pinned sha '+x['path'])
        require(blob(p)==x['blob']==index[x['path']]['sha'],'pinned blob '+x['path'])
    inv=read(SRC/'corpus-inventory.json')
    live=subprocess.check_output(['rg','--files','--no-ignore',str(COR)],cwd=ROOT,text=True).splitlines()
    require({str(pathlib.Path(p).relative_to(COR)) for p in live}=={x['path'] for x in inv},'corpus inventory set')
    require(len(inv)==9340,'corpus count')
    for x in inv:
        p=COR/x['path'];require(sha(p)==x['sha256'] and blob(p)==x['blob']==index[x['path']]['sha'],'corpus '+x['path'])
    passages=read(SRC/'passages.json')
    for x in passages:
        p=SRC/x['path'];require(sha(p)==x['sha256'],'passage source '+x['path'])
        lines=p.read_text().splitlines();s='\n'.join(lines[x['start']-1:x['end']])+'\n'
        require(hashlib.sha256(s.encode()).hexdigest()==x['passage_sha256'],'passage range '+x['path'])
        if x['anchor']:require(x['anchor'] in s,'passage anchor '+x['path'])
    responses=[]
    for f in sorted(SRC.glob('responses-*.json')):
        for x in read(f):
            if 'path' in x:require(sha(SRC/x['path'])==x['sha256'],'response body '+x['path'])
            responses.append(x)
    extractions=read(SRC/'pdf-extractions.json')
    for x in extractions:
        b=subprocess.check_output(['pdftotext','-layout',str(SRC/x['pdf']),'-'])
        require(hashlib.sha256(b).hexdigest()==x['text_sha256']==sha(SRC/x['text']),'PDF extraction '+x['pdf'])
    searches=read(SRC/'searches.json')
    for x in searches:
        z=subprocess.run(x['args'],cwd=ROOT,text=True,capture_output=True)
        require(z.returncode in [0,1],'search execution '+x['name'])
        require(collections.Counter(z.stdout.splitlines())==collections.Counter(read(SRC/x['result'])),'search multiset '+x['name'])
    diag=json.loads(subprocess.check_output([sys.executable,str(EXP/'diagnostics.py')],cwd=ROOT,text=True))
    require(diag==read(EXP/'diagnostics.json'),'diagnostic replay')
    # Verify diagnostic execution has not modified any sealed artifact.
    for x in seal['artifacts']:require(sha(ROOT/x['path'])==x['sha256'],'post-replay artifact '+x['path'])
    result={'status':'PASS','scope':'provenance and finite diagnostics only; no independent proof/novelty acceptance',
            'sealed_artifacts':len(seal['artifacts']),'frozen_inputs':len(inputs),'live_mutable_ledger_drift':drift,
            'pinned_files':len(pin),'pinned_manuscripts':len({x['path'].split('/')[1] for x in pin}),
            'complete_tree_entries':13223,'complete_manuscripts':749,'corpus_files':len(inv),'passages':len(passages),
            'http_responses':len(responses),'http_successes':sum(x.get('status')==200 for x in responses),
            'http_failures':[{'name':x['name'],'status':x.get('status'),'error':x.get('error')} for x in responses if x.get('status')!=200],
            'pdf_reextractions':len(extractions),'search_multisets':{x['name']:x['lines'] for x in searches},
            'finite_diagnostic_assertions':diag['assertions'],'read_only':True}
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
