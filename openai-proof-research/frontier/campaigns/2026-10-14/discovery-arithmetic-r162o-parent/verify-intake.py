#!/usr/bin/env python3
"""Read-only artifact/input verification of a no-nominee research packet."""
from pathlib import Path
import hashlib
import json
import subprocess

p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162o-parent'
r=b/'fresh-arithmetic-discovery-r162o';m=r/'packet/private'
sha=lambda d:hashlib.sha256(d).hexdigest()
load=lambda f:json.loads(f.read_bytes())
anchors={'FINAL.md':'36709ec1e5a3433d063c71fb4fd195c79673a7ce74088ed2c52ef2867e084aeb',
    'private/MANIFEST.json':'2370e5d2bf7f1117500f608cb8058e03204fb04a0f7e5f56a115905ee555be00',
    'REPORT.md':'22083a630c48b0c36687920f4a41f7e1eb8caddcf5da2b3a634660a4cfa241f5'}
for rel,h in anchors.items():assert sha((r/rel).read_bytes())==h
run=subprocess.run(['python','-I','-B',str(r/'packet/verify.py'),'--packet',str(r/'packet'),
    '--manifest',str(r/'private/MANIFEST.json'),'--final',str(r/'FINAL.md'),'--report',str(r/'REPORT.md'),
    '--manifest-sha256',anchors['private/MANIFEST.json'],'--final-sha256',anchors['FINAL.md'],
    '--report-sha256',anchors['REPORT.md']],capture_output=True,text=True,check=True)
result=json.loads(run.stdout);assert result['files']==64 and result['bytes']==3236304
assert result['mathematical_gate']=='not evaluated'
td=(p/'sources/preprints-tree.json').read_bytes()
assert sha(td)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
tree=json.loads(td);assert len(tree['tree'])==13223 and not tree['truncated'];lookup={x['path']:x for x in tree['tree']}
auth=load(m/'canonical-authentication.json');assert len(auth)==15
for x in auth:
    d=(p/x['local']).read_bytes();y=lookup[x['path']]
    assert len(d)==x['size']==y['size'] and sha(d)==x['sha256']
    assert x['git_blob']==y['sha']==hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
reads=[json.loads(x) for x in (m/'semantic-reads.jsonl').read_text().splitlines()]
for x in reads:
    d=(m/x['path']).read_bytes();assert len(d)==x['total'] and sha(d)==x['sha256']
    assert 0<=x['start']<=x['end']<=len(d)
text_bytes=0
for x in auth:
    if x['path'].endswith('.pdf'):continue
    rel=(p/x['local']).relative_to(m).as_posix();windows=sorted((z['start'],z['end']) for z in reads if z['path']==rel)
    end=0
    for start,stop in windows:assert start<=end;end=max(end,stop)
    assert end==x['size'];text_bytes+=x['size']
assert text_bytes==595707
history=[json.loads(x) for x in (m/'history-reads.jsonl').read_text().splitlines()]
for x in history:
    d=(p/x['path']).read_bytes();assert sha(d)==x['sha256'] and 0<=x['start']<=x['end']<=len(d)
direct=load(b/'discovery-arithmetic-r162n-parent/private/next-direct-originals.json');assert len(direct)==4
for x in direct:
    d=(p/x['path']).read_bytes();assert len(d)==x['bytes'] and sha(d)==x['sha256']
controls=load(m/'controls-result.json')['results']
assert controls['pristine.txt'][0] is True and controls['altered.txt'][0] is False and controls['absent.txt'][0] is False
snap={f.relative_to(r).as_posix():{'bytes':f.stat().st_size,'mode':f.stat().st_mode,'sha256':sha(f.read_bytes())} for f in r.rglob('*') if f.is_file()}
assert snap==load(o/'private/root-before.json')
v={'status':'MATCH','anchors':anchors,'read_only_verifier':result,'payload_files':64,'payload_bytes':3236304,
    'root_files_and_modes_unchanged':68,'canonical_blobs_against_complete_tree':15,
    'reported_full_canonical_text_bytes':text_bytes,'reported_readlog_hash_interval_records':len(reads),
    'history_whole_hash_and_selected_extent_records':len(history),'completed_direct_originals_unchanged':4,
    'reading_metadata_is_not_semantic_reading':True,'saved_copied_controls_match':3,'controls_rerun':False,
    'parent_semantically_read':['REPORT.md','FINAL.md','packet/STATUS.md','packet/verify.py','packet/private/derivation.md',
        'packet/private/READING-LIMITS.md','packet/private/primary-understanding.md','packet/private/source-understanding.md'],
    'parent_canonical_primary_proof_reread':False,'transitive_primary_reading_incomplete':True,
    'late_primary_discovery_false_admission_recoveries_coarse_omissions_retained':True,
    'artifact_verifier_scope':'Exact packet file membership,size,hash and anchors; parent separately checks no current root mode/byte changes. No sealed-directory/mode claim.',
    'mathematical_gate_assigned':False,'accepted':False,'count_change':0}
(o/'verification.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
