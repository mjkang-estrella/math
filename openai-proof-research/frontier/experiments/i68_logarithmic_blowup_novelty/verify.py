"""Read-only I68 replay: no downloads, writes, bytecode or seal refresh.

An explained immutable reference drift remains a failure with exit code 1.
Core evidence and analytic/contribution decisions are reported separately.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from collections import Counter
import hashlib, importlib.util, json, re, subprocess

ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i68_logarithmic_blowup_novelty'
E=Path(__file__).resolve().parent
OLD=ROOT/'frontier/sources/i66_dispersive_equation_discovery'
def read(p):return json.loads(p.read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def check(x,path=None):
    b=(ROOT/(path or x['path'])).read_bytes()
    assert len(b)==x['bytes'] and sha(b)==x['sha256'],('artifact mismatch',path or x['path'])

def verify():
    counts={};drift=[];mutable=[]
    sealed=read(S/'seal.json')['artifacts']
    for x in sealed:check(x)
    counts['sealed_artifacts']=len(sealed)
    refs=read(S/'references.json')
    allowed={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
    for x in refs:
        b=(ROOT/x['path']).read_bytes()
        if x['mutable']:
            assert x['path'] in allowed
            check(x,x['frozen'])
            if sha(b)!=x['sha256']:mutable.append(x['path'])
        elif sha(b)!=x['sha256'] or len(b)!=x['bytes']:
            drift.append({'path':x['path'],'expected_bytes':x['bytes'],'expected_sha256':x['sha256'],
                          'observed_bytes':len(b),'observed_sha256':sha(b)})
    counts['hash_references']=len(refs)
    counts['immutable_reference_drift']=len(drift)
    task=read(S/'current-task.json')
    assert (S/'current-review-brief.txt').read_text()=='Act as the review sub-agent for this task.\n\n'+task['brief']+'\n'
    assert (S/'original-full-brief.txt').read_bytes()==(OLD/'full-brief.txt').read_bytes()
    original=module('i68_original',ROOT/'frontier/experiments/i66_dispersive_equation_discovery/verify.py').verify()
    assert original['evidence_status']=='PASS'
    oldreplay=read(E/'i66-replay.json')
    assert original['counts']==oldreplay['counts']
    assert original['preserved_primary_failures']==oldreplay['preserved_primary_failures']
    counts['inherited_corpus_files']=original['counts']['corpus_files']
    search_counts={}
    for q in read(S/'searches.json'):
        result=subprocess.run(['rg','--no-ignore','--with-filename']+q['flags']+['-e',q['pattern'],q['domain']],cwd=ROOT,capture_output=True,text=True)
        assert result.returncode in (0,1),result.stderr
        lines=result.stdout.splitlines();expected=(S/q['output']).read_text().splitlines()
        assert Counter(lines)==Counter(expected),('line MULTISET mismatch',q['name'])
        assert len(lines)==q['count'];search_counts[q['name']]=len(lines)
    counts['fixed_domain_line_multisets']=search_counts
    pins={x['local']:x for x in read(OLD/'pinned-manifest.json')}
    passages=read(S/'passages.json')
    for x in passages:
        p=ROOT/x['path'];b=b''.join(p.read_bytes().splitlines(keepends=True)[x['start_line']-1:x['end_line']])
        assert sha(b)==x['sha256'] and b.decode()==x['text'],x['label']
        if 'git_blob' in x:
            assert blob(p.read_bytes())==x['git_blob']==pins[x['path']]['git_blob']
            assert x['url']==pins[x['path']]['url']
    counts['passages']=len(passages)
    for x in read(S/'raw-pin-comparisons.json'):
        b=(ROOT/x['path']).read_bytes();pin=pins[x['pinned_local']]
        assert b==(ROOT/x['pinned_local']).read_bytes()
        assert sha(b)==x['sha256']==pin['sha256']
        assert blob(b)==x['git_blob']==pin['git_blob']
        assert x['url']==pin['url']
    counts['fresh_raw_pin_comparisons']=3
    responses=[read(p) for p in sorted((S/'primary').glob('*.response.json'))]
    for x in responses:
        if 'file' in x:
            b=(S/'primary'/x['file']).read_bytes()
            assert sha(b)==x['sha256'] and len(b)==x['bytes']
    counts['fresh_requests']=len(responses)
    counts['fresh_successes']=sum(x.get('status')==200 for x in responses)
    extract=module('i68_extract',ROOT/'frontier/experiments/i66_dispersive_equation_discovery/extract_primary.py')
    ex=read(S/'primary/extractions.json')
    for x in ex:
        b=extract.extract((S/'primary'/x['source']).read_bytes()).encode()
        assert b==(S/'primary'/x['text']).read_bytes() and sha(b)==x['sha256']
    counts['fresh_primary_text_replays']=len(ex)
    versions=read(S/'current-versions.json')
    for x in versions:
        b=(ROOT/x['abstract_html']).read_bytes();assert sha(b)==x['abstract_sha256']
        version=re.search(r'<meta property="og:url" content="https://arxiv.org/abs/([^\"]+)"',b.decode())[1]
        assert version==x['current_version_at_retrieval']
        text=(ROOT/x['abstract_text']).read_text()
        actual=[line for line in text.splitlines() if 'Submitted on' in line or 'for this version)' in line]
        assert actual==x['version_passage']
        assert version in text
    counts['current_primary_versions']=len(versions)
    diagnostic=module('i68_diagnostics',E/'diagnostics.py').compute()
    assert diagnostic==read(E/'diagnostics.json')
    counts['independent_finite_assertions']=diagnostic['checks']
    observation=read(S/'i67-observation.json')
    check(observation,observation['snapshot'])
    assert observation['observed_verdict'] in (ROOT/observation['snapshot']).read_text()
    # Replay the completed peer verifier, preserving its separate nonzero result.
    peer=module('i68_peer',ROOT/'frontier/experiments/i67_logarithmic_blowup_r2/verify.py').verify()
    assert peer['core_checks_status']=='PASS'
    assert peer['counts']['independent_exact_assertions']==3108
    assert peer['counts']['independent_decimal_assertions']==117
    parent_audit=read(ROOT/'frontier/experiments/i67-parent-reference-drift-audit.json')
    current=(ROOT/parent_audit['reference']).read_bytes()
    assert len(current)==parent_audit['current_bytes'] and sha(current)==parent_audit['current_sha256']
    old=current.replace(b'wallauch-v1-html.txt:30-147,151-201',b'wallauch-v1-html.txt:30-201')
    assert sha(old)==parent_audit['initial_sha256'] and len(old)==parent_audit['initial_bytes']
    # I68 froze an even earlier wrapper, before parent_reading was added.
    own_audit=read(S/'reference-drift.json')
    check({'path':own_audit['snapshot'],'bytes':own_audit['observed_bytes'],'sha256':own_audit['observed_sha256']})
    parsed=json.loads(current);parsed.pop('parent_reading')
    old=(json.dumps(parsed,indent=2)+'\n').encode()
    assert sha(old)==own_audit['expected_sha256'] and len(old)==own_audit['expected_bytes']
    assert [x for x in drift if x['path']==own_audit['path']]==[{k:own_audit[k] for k in ['path','expected_bytes','expected_sha256','observed_bytes','observed_sha256']}]
    return {'evidence_status':'FAIL_REFERENCE_DRIFT' if drift else 'PASS','core_checks_status':'PASS',
            'counts':counts,'immutable_reference_drift':drift,'current_ledger_drift':mutable,
            'original_i66_replay_status':original['evidence_status'],
            'original_i66_live_ledger_drift':original['mutable_ledgers_changed'],
            'preserved_primary_failures':original['preserved_primary_failures'],
            'peer_i67_replay_status':peer['evidence_status'],'peer_i67_core_checks_status':peer['core_checks_status'],
            'wrapper_reconstruction_checks':'PASS for both independently frozen baselines; references are NOT refreshed',
            'contribution_status':'See report: TECHNICAL ONLY. Evidence checks do not certify this judgment or worldwide priority.',
            'scope':'Read-only provenance and finite reproducibility. No author edits, old-seal refresh, ledger writes, staging, commit, publication or agent spawning.'}

if __name__=='__main__':
    result=verify();print(json.dumps(result,indent=2,sort_keys=True))
    sys.exit(0 if result['evidence_status']=='PASS' else 1)
