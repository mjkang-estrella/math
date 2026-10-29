import hashlib,json,shutil,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone

batch=Path(__file__).resolve().parent.parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n in (64,65):
    lane=batch/f'lanes/sol-fresh-source-discovery-r{n}'
    here=batch/f'lanes/root-fresh-source-r{n}-handback'
    here.mkdir(exist_ok=True)
    prov=json.loads((lane/'provenance.json').read_text())
    records=prov['source_hashes'] if n==64 else prov['http']
    hashes=[]
    for r in records:
        key=r.get('path',r.get('file'))
        if key and 'sha256' in r:
            hashes.append({'path':key,'expected':r['sha256'],'actual':sha(lane/key)})
    assert hashes and all(r['actual']==r['expected'] for r in hashes)
    inventory={str(p.relative_to(lane)):sha(p) for p in lane.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
    copy=here/'check-copy'
    copy.mkdir(exist_ok=True)
    shutil.copyfile(lane/'check.py',copy/'check.py')
    args=['transfer'] if n==64 else ['4']
    with (here/'check.log').open('w') as log:
        subprocess.run([sys.executable,'check.py',*args],cwd=copy,stdout=log,stderr=subprocess.STDOUT,check=True)
    output='checks-transfer.json' if n==64 else 'checks-n4.json'
    assert json.loads((copy/output).read_text())==json.loads((lane/output).read_text()) if n==64 else True
    if n==65:
        a=json.loads((copy/output).read_text());b=json.loads((lane/output).read_text())
        assert a['first_row_normalized_counts']==b['first_row_normalized_counts']
        assert 521**2-82*4462==-94443
        assert 97440<99894
    receipt={
      'utc':datetime.now(timezone.utc).isoformat(),'status':'UNRESOLVED handback preserved','credit':0,'counts':[7,37],
      'target':'Han-Pedon Conjecture C' if n==64 else 'Mirzavaziri-Yaqubi Conjecture4.15 aggregate Latin-square ascent unimodality',
      'gap':'Identify consecutive denominators with uniform zero-gap normalization; prove both coefficient-end laws, exact period and all initial indices.' if n==64 else 'Uniform comparison of aggregate all-square coefficients below the symmetry center. Public attainment theorem is insufficient.',
      'root_check':'All 16 finite transfer tests replayed in own copy; JSON identical. No all-order source theorem follows.' if n==64 else 'Order4 exact enumeration replayed; coefficient vector identical. Saved order6 log-concavity deficit and order7 subset-valley arithmetic checked; full order6/7 enumeration not rerun.',
      'full_worker_suite_rerun':False,'source_freshness':'HOLD retained','formal':'No Lean or formal PASS',
      'source_hashes':hashes,'input_inventory':inventory,
      'limits':'No full proof, counterexample, novelty clearance, acceptance or count change. Root preserves diagnostics and stated gaps; no independent all-order result claimed.'}
    (here/'ADOPTION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    assert inventory=={str(p.relative_to(lane)):sha(p) for p in lane.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
    paths=[str(p.relative_to(Path.cwd())) for root in (lane,here) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='pathspec.txt']
    if n==65:
        nxt=batch/'NEXT.md';s=nxt.read_text()
        s=s.replace('Three fresh Sol high/default research lanes r65 finite structures, r66 analysis,\nr64 arithmetic/algebra are active; no children.', 'r64 Han-Pedon and r65 Latin-square unimodality remain unresolved. Their exact\nproof gaps and limited root replays are preserved in root-fresh-source-r64-handback\nand root-fresh-source-r65-handback; no counts changed.\nThree fresh Sol high/default research lanes r68 finite structures, r66 analysis,\nr67 arithmetic/algebra are active; no children.')
        nxt.write_text(s);paths.append(str(nxt.relative_to(Path.cwd())))
    (here/'pathspec.txt').write_text('\n'.join(paths)+'\n')
    print(json.dumps({'lane':n,'source_hashes':len(hashes),'original_files_unchanged':len(inventory),'bounded_replay':'PASS'}))
