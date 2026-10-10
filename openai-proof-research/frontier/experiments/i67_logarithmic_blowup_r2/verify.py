"""Read-only I67 replay: no network, downloads, writes, bytecode or seal refresh."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from collections import Counter
import hashlib, importlib.util, json, re, subprocess

ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i67_logarithmic_blowup_r2'
E=Path(__file__).resolve().parent
OLD=ROOT/'frontier/sources/i66_dispersive_equation_discovery'

def read(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def check_record(x):
    b=(ROOT/x['path']).read_bytes()
    assert sha(b)==x['sha256'],('changed immutable file',x['path'])
    assert len(b)==x['bytes'],x['path']

def verify():
    counts={}
    seal=read(S/'seal.json')
    for x in seal['artifacts']:check_record(x)
    counts['sealed_artifacts']=len(seal['artifacts'])
    refs=read(S/'immutable-references.json')
    drift=[]
    for x in refs:
        b=(ROOT/x['path']).read_bytes()
        if sha(b)!=x['sha256'] or len(b)!=x['bytes']:
            drift.append({'path':x['path'],'expected_sha256':x['sha256'],'expected_bytes':x['bytes'],'observed_sha256':sha(b),'observed_bytes':len(b)})
    counts['immutable_old_references']=len(refs)
    counts['immutable_old_references_matching']=len(refs)-len(drift)
    task=read(ROOT/'frontier/iterations/iteration67-logarithmic-blowup-r2-task.json')
    assert (S/'review-brief.txt').read_text()=='Act as the review sub-agent for this task.\n\n'+task['brief']
    assert (S/'original-brief.txt').read_bytes()==(OLD/'full-brief.txt').read_bytes()
    mutable=[]
    ledgers=read(S/'mutable-ledgers.json')
    assert {x['path'] for x in ledgers}=={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
    for x in ledgers:
        b=(ROOT/x['frozen']).read_bytes();assert sha(b)==x['sha256'] and len(b)==x['bytes']
        if sha((ROOT/x['path']).read_bytes())!=x['sha256']:mutable.append(x['path'])
    counts['mutable_ledger_snapshots']=len(ledgers)
    tree=read(ROOT/'sources/preprints-tree.json')
    assert not tree['truncated'] and len(tree['tree'])==13223
    assert len({x['path'].split('/')[1] for x in tree['tree']})==749
    blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
    pinned=read(S/'pinned-references.json')
    for x in pinned:
        b=(ROOT/x['local']).read_bytes()
        assert sha(b)==x['sha256'] and blob(b)==x['git_blob']==blobs[x['path']]
        assert x['url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']
    counts['direct_pinned_interfaces']=len(pinned)
    passages=read(S/'passages.json')
    for x in passages:
        lines=(ROOT/x['path']).read_text().splitlines(keepends=True)
        text=''.join(lines[x['start']-1:x['end']])
        assert text==x['text'] and sha(text.encode())==x['sha256']
    counts['passages']=len(passages)
    searches=read(S/'searches.json');search_counts={}
    for x in searches:
        p=subprocess.run(x['args'],cwd=ROOT,capture_output=True,text=True,check=False)
        assert p.returncode in (0,1),p.stderr
        lines=p.stdout.splitlines()
        assert Counter(lines)==Counter((ROOT/x['output']).read_text().splitlines())
        assert len(lines)==x['line_count'];search_counts[x['name']]=len(lines)
    counts['search_line_multisets']=search_counts
    responses=read(S/'primary/responses.json')
    for x in responses:
        check_record(x)
        if x['name'].startswith('pin-'):
            pin=next(y for y in pinned if y['url']==x['url'])
            assert (ROOT/x['path']).read_bytes()==(ROOT/pin['local']).read_bytes()
    counts['fresh_requests']=len(responses)
    counts['fresh_successes']=sum(x['status']==200 for x in responses)
    extractor=module('i67_old_extractor',ROOT/'frontier/experiments/i66_dispersive_equation_discovery/extract_primary.py')
    extractions=read(S/'primary/extractions.json')
    for x in extractions:
        b=extractor.extract((ROOT/x['source']).read_bytes()).encode()
        assert sha(b)==x['sha256'] and b==(ROOT/x['text']).read_bytes()
        assert x['identical_to_old'] and b==(ROOT/x['old_text']).read_bytes()
    counts['fresh_primary_text_replays']=len(extractions)
    for x in read(S/'primary/versions.json'):
        text=(ROOT/x['path']).read_text()
        assert x['submission_history'] in text
        history=text.split('Submission history',1)[1].split('Full-text links:',1)[0]
        versions=[int(n) for n in re.findall(r'\[v(\d+)\]',history)]
        assert max(versions)==x['current_version']
    original=module('i67_original_verifier',ROOT/'frontier/experiments/i66_dispersive_equation_discovery/verify.py').verify()
    assert original['evidence_status']=='PASS'
    baseline=read(E/'original-replay.json')
    assert original['counts']==baseline['counts']
    assert original['preserved_primary_failures']==baseline['preserved_primary_failures']
    counts['inherited_corpus_files']=original['counts']['corpus_files']
    diagnostic=module('i67_diagnostics',E/'diagnostics.py').compute()
    assert diagnostic==read(E/'diagnostics.json')
    counts['independent_exact_assertions']=diagnostic['exact_assertions']
    counts['independent_decimal_assertions']=diagnostic['decimal_assertions']
    return {'evidence_status':'FAIL_REFERENCE_DRIFT' if drift else 'PASS','immutable_reference_drift':drift,'core_checks_status':'PASS','counts':counts,'current_i67_ledger_drift':mutable,
            'original_i66_replay_status':original['evidence_status'],
            'original_i66_live_ledger_drift':original['mutable_ledgers_changed'],
            'preserved_primary_failures':original['preserved_primary_failures'],
            'analytic_status':'See written I67 review: C66 PASS ORIGINAL WITHOUT REPAIRS under stipulated pinned premises.',
            'unpaid':'Construction II global weighted tail/remainder; fractal target B; contribution gate separate.',
            'scope':'Read-only evidence reproduction, not analytic proof or novelty certification.'}

if __name__=='__main__':
    result=verify()
    print(json.dumps(result,indent=2,sort_keys=True))
    sys.exit(0 if result['evidence_status']=='PASS' else 1)
