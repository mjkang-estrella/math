"""Read-only I66 reproduction. No downloads, cache writes, or seal updates."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from collections import Counter
import hashlib, json, subprocess, importlib.util

ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i66_dispersive_equation_discovery'
E=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    obj=importlib.util.module_from_spec(spec);spec.loader.exec_module(obj);return obj

def verify():
    counts={}; mutable=[]
    sealed=read(S/'seal.json')
    for x in sealed['artifacts']:
        b=(ROOT/x['path']).read_bytes()
        assert sha(b)==x['sha256'],('sealed artifact changed',x['path'])
        assert len(b)==x['bytes']
    counts['sealed_artifacts']=len(sealed['artifacts'])
    ins=read(S/'inputs-manifest.json')
    allowed_mutable={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
    for x in ins:
        frozen=(ROOT/x['frozen']).read_bytes();assert sha(frozen)==x['sha256']
        current=(ROOT/x['path']).read_bytes()
        if sha(current)!=x['sha256']:
            assert x['mutable'] and x['path'] in allowed_mutable,('immutable input changed',x['path'])
            mutable.append(x['path'])
    counts['frozen_inputs']=len(ins)
    task=read(S/'inputs/frontier/iterations/iteration66-dispersive-equation-discovery-task.json')
    assert (S/'full-brief.txt').read_text()=='Act as the research sub-agent for this task.\n\n'+task['brief']+'\n'
    assert read(S/'inputs/sources/upstream.json')['commit']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    inventory=read(S/'inputs/sources/preprints-tree.json');assert not inventory['truncated']
    assert len(inventory['tree'])==13223
    assert len({x['path'].split('/')[1] for x in inventory['tree']})==749
    tree={x['path']:x['sha'] for x in inventory['tree'] if x['type']=='blob'}
    corpus=read(S/'corpus-manifest.json');cr=ROOT/corpus['root']
    actual=subprocess.check_output(['rg','--files','--no-ignore',str(cr)],text=True)
    actual={str(Path(x).relative_to(cr)) for x in actual.splitlines()}
    assert actual=={x['path'] for x in corpus['files']}
    assert len(actual)==9340
    for x in corpus['files']:
        b=(cr/x['path']).read_bytes()
        assert sha(b)==x['sha256'] and len(b)==x['bytes'],x['path']
        assert blob(b)==x['git_blob']==tree[x['path']],x['path']
    counts['corpus_files']=len(actual)
    pinned=read(S/'pinned-manifest.json')
    for x in pinned:
        b=(ROOT/x['local']).read_bytes()
        assert sha(b)==x['sha256'] and len(b)==x['bytes']
        assert blob(b)==x['git_blob']==tree[x['path']]
        assert x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    counts['pinned_files']=len(pinned)
    refs=read(S/'prior-evidence-references.json')
    for x in refs:
        b=(ROOT/x['path']).read_bytes();assert sha(b)==x['sha256'] and len(b)==x['bytes'],x['path']
    counts['prior_hash_references']=len(refs)
    searches=read(S/'searches.json');search_counts={}
    for q in searches:
        if q['domain']=='corpus-manifest.json':
            args=['rg','--no-ignore','--with-filename']+q['flags']+['-e',q['pattern'],corpus['root']]
            p=subprocess.run(args,cwd=ROOT,capture_output=True,text=True)
            assert p.returncode in (0,1),p.stderr
            lines=p.stdout.splitlines()
        else:
            paths=[str((S/'inputs'/f).relative_to(ROOT)) for f in q['domain']]
            args=['rg','--with-filename']+q['flags']+['-e',q['pattern']]+paths
            p=subprocess.run(args,cwd=ROOT,capture_output=True,text=True)
            assert p.returncode in (0,1),p.stderr
            prefix=str((S/'inputs').relative_to(ROOT))+'/'
            lines=[x.removeprefix(prefix) for x in p.stdout.splitlines()]
        expected=(S/q['output']).read_text().splitlines()
        assert Counter(lines)==Counter(expected),('line MULTISET differs',q['name'])
        assert len(lines)==q['count']
        search_counts[q['name']]=len(lines)
    counts['fixed_domain_line_multisets']=search_counts
    passages=read(S/'passages.json')
    for x in passages:
        lines=(ROOT/x['path']).read_text().splitlines(keepends=True)
        text=''.join(lines[x['start']-1:x['end']])
        assert text==x['text'] and sha(text.encode())==x['sha256'],x['path']
    counts['passages']=len(passages)
    responses=[]
    for name in ['responses.json','followup-responses.json']:
        responses+=read(S/'primary'/name)
    for x in responses:
        if 'file' in x:
            b=(S/'primary'/x['file']).read_bytes()
            assert sha(b)==x['sha256'] and len(b)==x['bytes']
    counts['primary_requests']=len(responses)
    counts['primary_successes']=sum(x.get('status')==200 for x in responses)
    failures=[{'url':x['url'],'status':x.get('status'),'error':x.get('error')} for x in responses if x.get('status')!=200]
    extraction=module('i66_extraction',E/'extract_primary.py')
    extractions=read(S/'primary/extractions.json')
    for x in extractions:
        src=S/'primary'/x['source']
        if x['method']=='HTMLParser/MathML alttext':
            b=extraction.extract(src.read_bytes()).encode()
        else:
            p=subprocess.run(['pdftotext','-layout',str(src),'-'],capture_output=True,check=True)
            b=p.stdout;assert p.stderr.decode()==x['stderr']
        assert sha(b)==x['sha256'] and b==(S/'primary'/x['text']).read_bytes(),x['source']
    counts['primary_text_replays']=len(extractions)
    raw=read(S/'raw-checks/responses.json')
    bypath={x['path']:x for x in pinned}
    for x in raw:
        assert x['status']==200 and x['matches_pin']
        b=(S/x['file']).read_bytes()
        assert sha(b)==x['sha256']==bypath[x['source']]['sha256']
    counts['fresh_raw_pin_comparisons']=len(raw)
    diagnostics=module('i66_diagnostics',E/'diagnostics.py').compute()
    assert diagnostics==read(E/'diagnostics.json')
    counts['finite_diagnostic_assertions']=diagnostics['exact_and_decimal_assertions']
    return {'evidence_status':'PASS','counts':counts,'mutable_ledgers_changed':mutable,
            'preserved_primary_failures':failures,
            'analytic_status':'Author proof proposed; independent proof and contribution reviews pending.',
            'scope':'Read-only reproducibility; no proof/priority certification; no staging, commit, publication, seal refresh, or ledger change.'}

if __name__=='__main__':
    print(json.dumps(verify(),indent=2,sort_keys=True))
