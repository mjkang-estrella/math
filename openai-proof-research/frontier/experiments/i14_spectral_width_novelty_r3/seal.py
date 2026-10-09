"""Verify frozen inputs and pinned corpus, then seal only this review's assigned artifacts."""
import pathlib,json,hashlib,re,datetime,sys
root=pathlib.Path('.')
sr=root/'frontier/sources/i14_spectral_width_novelty_r3'
er=root/'frontier/experiments/i14_spectral_width_novelty_r3'
review=root/'frontier/reviews/i14-spectral-width-novelty-r3.md'
sha=lambda b:hashlib.sha256(b).hexdigest()
inp=json.loads((sr/'input-manifest.json').read_text())
for e in inp:
    original=root/e['path'];frozen=sr/'inputs'/e['path']
    assert sha(original.read_bytes())==e['sha256'],('changed input',e['path'])
    assert sha(frozen.read_bytes())==e['sha256'],('bad freeze',e['path'])
tree=json.loads((sr/'inputs/sources/preprints-tree.json').read_text())
assert tree['truncated'] is False
expected={e['path']:e for e in tree['tree'] if e['type']=='blob' and e['path'].endswith(('.tex','.bib','.md','.txt'))}
corpus=json.loads((sr/'corpus-manifest.json').read_text())
assert set(expected)=={e['path'] for e in corpus['files']}
for e in corpus['files']:
    b=(sr/'corpus'/e['path']).read_bytes()
    assert sha(b)==e['sha256']
    blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert blob==e['git_blob']==expected[e['path']]['sha']
literature=json.loads((sr/'literature/manifest.json').read_text())
for e in literature:
    if e.get('status')=='downloaded':
        assert sha((root/e['local']).read_bytes())==e['sha256']
        if 'extracted_text' in e:
            t=e['extracted_text'];assert sha((root/t['local']).read_bytes())==t['sha256']
text=review.read_text();assert '\0' not in text
links=re.findall(r'\]\(([^)]+)\)',text)
for link in links:
    if not link.startswith('https://'):
        assert (review.parent/link).exists() or (review.parent/link).resolve()==(sr/'artifact-seal.json').resolve(),('broken local link',link)
result={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'python':sys.version,
        'frozen_inputs_verified_unchanged':len(inp),'pinned_files_verified':len(corpus['files']),
        'pinned_manuscript_directories':len({x['path'].split('/')[1] for x in corpus['files']}),
        'tree_entries':len(tree['tree']),'tree_truncated':tree['truncated'],
        'literature_captures_verified':sum(x.get('status')=='downloaded' for x in literature),
        'review_sha256':sha(review.read_bytes()),'review_local_links_verified':sum(not x.startswith('https://') for x in links),
        'verdict':'TECHNICAL ONLY','proof':'PASS retained','count_increment':0,
        'scope':'Only assigned review and source/experiment directories were written.'}
(er/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
seal_path=sr/'artifact-seal.json'
files=[review]+[p for folder in [sr,er] for p in folder.rglob('*') if p.is_file() and p!=seal_path]
rows=[{'path':str(p),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size} for p in sorted(files)]
seal={'sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pin':corpus['pin'],'verdict':'TECHNICAL ONLY','self_excluded':str(seal_path),'artifacts':rows}
seal_path.write_text(json.dumps(seal,indent=2)+'\n')
# Read back and verify the sealed output identities, without modifying any sealed artifact.
for e in json.loads(seal_path.read_text())['artifacts']:
    assert sha((root/e['path']).read_bytes())==e['sha256']
for link in links:
    if not link.startswith('https://'): assert (review.parent/link).exists()
print(json.dumps(result,indent=2))
print('sealed artifacts:',len(rows))
print('seal SHA-256:',sha(seal_path.read_bytes()))
