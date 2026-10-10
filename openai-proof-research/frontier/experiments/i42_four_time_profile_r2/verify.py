"""Read-only I42 seal/dependency verification and explicitly frozen-ledger I41 replay."""
from pathlib import Path
import hashlib, json, runpy, subprocess, sys

R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i42_four_time_profile_r2'
E=R/'frontier/experiments/i42_four_time_profile_r2'
OLD=R/'frontier/sources/i41_rademacher_fair_start_warming'
LEDGERS={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def checkbytes(p,row):
    b=p.read_bytes()
    assert len(b)==row['bytes'] and sha(b)==row['sha256'],str(p)
    return b
def ownfiles():
    paths=[R/'frontier/reviews/i42-four-time-profile-r2.md']+list(S.rglob('*'))+list(E.rglob('*'))
    return sorted(str(p.relative_to(R)) for p in paths if p.is_file() and p!=S/'artifact-seal.json')

def replay_i41():
    """Only exact ledger paths get old bytes; all proof/artifact reads remain live."""
    drift=[]
    for row in read(OLD/'inputs.json'):
        checkbytes(OLD/'frozen'/row['path'],row)
        b=(R/row['path']).read_bytes()
        if len(b)!=row['bytes'] or sha(b)!=row['sha256']:
            assert row['path'] in LEDGERS,('Unapproved nonledger drift',row['path'])
            drift.append({'path':row['path'],'i41_mutable_flag':row['mutable'],'old_sha256':row['sha256'],'live_sha256':sha(b)})
    namespace=runpy.run_path(str(R/'frontier/experiments/i41_rademacher_fair_start_warming/verify.py'))
    old_read=Path.read_bytes
    replacements={R/p:OLD/'frozen'/p for p in LEDGERS}
    def frozen_ledger_read(self):return old_read(replacements.get(self,self))
    try:
        Path.read_bytes=frozen_ledger_read
        result=namespace['verify']()
    finally:
        Path.read_bytes=old_read
    return {'mode':'Unchanged I41 verifier, exact four-ledger read-only frozen byte view. NOT a vanilla live verifier PASS.',
            'substituted_paths':sorted(LEDGERS),'live_ledger_drift':drift,'result':result}

def verify(preseal=False):
    out={'status':'PASS sealed evidence and exact diagnostics; analytic verdicts are in the review','pin':PIN}
    if not preseal:
        seal=read(S/'artifact-seal.json');assert set(ownfiles())==set(seal['files'])
        for p,row in seal['files'].items():checkbytes(R/p,row)
        out['sealed_artifacts']=len(seal['files'])
    else:out['seal_check']='PRESEAL ONLY'
    drift=[]
    for row in read(S/'inputs.json'):
        checkbytes(S/'frozen'/row['path'],row)
        b=(R/row['path']).read_bytes()
        if sha(b)!=row['sha256'] or len(b)!=row['bytes']:
            assert row['mutable'],row['path']
            drift.append({'path':row['path'],'baseline_sha256':row['sha256'],'live_sha256':sha(b)})
    out['frozen_inputs']=len(read(S/'inputs.json'));out['mutable_drift_since_i42_freeze']=drift
    for row in read(S/'read-passages.json'):
        b=(R/row['path']).read_bytes();assert sha(b)==row['sha256'];lines=b.splitlines(keepends=True)
        for span in row['ranges']:
            assert 1<=span['first']<=span['last']<=len(lines)
            assert sha(b''.join(lines[span['first']-1:span['last']]))==span['sha256']
    for row in read(S/'contracts.json'):
        b=(R/row['path']).read_bytes();assert sha(b)==row['file_sha256'];ls=b.splitlines(keepends=True)
        assert ('\\label{'+row['label']+'}').encode() in ls[row['label_line']-1]
        excerpt=b''.join(ls[row['first']-1:row['last']])
        assert excerpt.decode()==row['excerpt'] and sha(excerpt)==row['excerpt_sha256']
        assert row['pin']==PIN
    out['read_records']=len(read(S/'read-passages.json'));out['source_contracts']=len(read(S/'contracts.json'))
    for row in read(S/'primary/responses.json'):
        assert row.get('status')==200 and row['matches_pinned_corpus']
        name=row['url'].rsplit('/',1)[1];checkbytes(S/'primary'/name,row)
    out['fresh_pinned_responses']=len(read(S/'primary/responses.json'))
    # Honor the ignored corpus explicitly; the replay below rehashes every member and Git blob.
    corpus=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
    paths=subprocess.check_output(['rg','--files','--no-ignore',str(corpus)],text=True).splitlines()
    manifest=read(OLD/'frozen/frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json')
    assert {str(Path(p).relative_to(corpus)) for p in paths}=={x['path'] for x in manifest['files']}
    assert len(paths)==9340
    replay=replay_i41();out['i41_frozen_ledger_replay']=replay
    saved=read(S/'i41-frozen-ledger-replay.json')
    assert saved['result']==replay['result']
    # Shared ledgers may evolve; report current hashes instead of refreshing snapshots.
    own=runpy.run_path(str(E/'check.py'))['check']()
    assert own==read(E/'diagnostics.json');out['diagnostics']=own
    out['prior_direct_run']=read(S/'i41-reproduction.json')['verify']['returncode']
    out['scope']='R, representations, entropy criterion, countermodel PASS ORIGINAL WITHOUT REPAIRS in report. Full W unproved/unrefuted. No nomination.'
    return out

if __name__=='__main__':print(json.dumps(verify('--preseal' in sys.argv),indent=2))
