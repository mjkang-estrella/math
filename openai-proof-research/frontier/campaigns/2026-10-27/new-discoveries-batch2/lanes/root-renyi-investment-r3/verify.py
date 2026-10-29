import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
root=Path(__file__).resolve().parent
review=root.parent/'sol-renyi-registry-gap-closure-r3'
def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1024*1024),b''):h.update(c)
    return h.hexdigest()
provenance=json.loads((review/'provenance.json').read_text())
freeze=[]
for name,entry in provenance['files'].items():
    p=review/name
    assert digest(p)==entry['sha256'],name
    assert p.stat().st_size==entry['bytes'],name
    freeze.append({'path':str(p),'sha256':entry['sha256'],'bytes':entry['bytes']})
freeze.append({'path':str(review/'provenance.json'),'sha256':digest(review/'provenance.json'),'bytes':(review/'provenance.json').stat().st_size})
coverage=json.loads((review/'exactcoverage.json').read_text())
commits=set(); previous=coverage['base']; file_counts=[]
for row in coverage['intervals']:
    assert row['base']==previous
    p=Path(row['response']);p=p if p.is_absolute() else review/p
    assert digest(p)==row['sha256']
    data=json.loads(p.read_text())
    assert data['base_commit']['sha']==row['base']
    assert data['merge_base_commit']['sha']==row['base']
    assert len(data['files'])==row['file_count']<300
    assert len(data['commits'])==data['total_commits']==len(row['commits'])
    new={v['sha'] for v in data['commits']}
    assert not (new&commits)
    assert row['end'] in new
    commits.update(new);previous=row['end'];file_counts.append(row['file_count'])
assert previous==coverage['end'] and len(commits)==205
for row in coverage['bodies']:
    p=review/row['source'];blob=p.read_bytes()
    assert hashlib.sha256(blob).hexdigest()==row['read']['sha256']
    assert len(blob)==row['read']['bytes']
    actual=hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest()
    assert actual==row['actual_git_blob']
    if row['blob'] is not None:assert actual==row['blob']
assert len(coverage['missing_patch_required'])==70
assert coverage['all_required_missing_bodies_closed'] and coverage['all_selected_bodies_closed']
before=json.loads((review/'before.json').read_text());after=json.loads((review/'after.json').read_text())
for lane,record in after.items():
    assert record['all_match'] and before[lane]['all_match']
    # Preserve the worker's exhaustive input rehash receipts; root independently
    # rechecks the proof and review manifest, not the >1GB inherited survey cache.
candidate=root.parent/'sol-fresh-source-discovery-r111'/'PROOF.md'
assert digest(candidate)==provenance['candidate_proof_sha256']
report={'utc':datetime.now(timezone.utc).isoformat(),'review_manifest_verified':len(freeze)-1,
 'comparison_intervals':11,'file_counts':file_counts,'distinct_commits':len(commits),
 'actual_body_hashes_verified':len(coverage['bodies']),'required_missing_patch_paths':70,
 'end':previous,'root_decision':'INVEST; bounded novelty hold cleared',
 'credit':0,'counts':[8,38],
 'limits':'Not worldwide priority; 51 historical whole-source hash mismatches retain exact atom recovery; baseline semantic selection bounded. Root verified review hashes and immutable body/compare receipts, not all inherited bulk survey bytes.'}
(root/'ADOPTION.json').write_text(json.dumps(report,indent=2)+'\n')
(root/'review-freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
print(json.dumps(report))
for row in coverage['bodies']:
    if any(s in row['path'] for s in ['WeightedRenyi','ExactEntropyPower','TruncatedExponentialTwoAdic']):
        t=(review/row['source']).read_text(errors='replace')
        selected=[line for line in t.splitlines() if any(k in line for k in ['theorem ','def ','lemma ','Claim','Theorem'])]
        print(row['path'], '\n'.join(selected)[:2200])
