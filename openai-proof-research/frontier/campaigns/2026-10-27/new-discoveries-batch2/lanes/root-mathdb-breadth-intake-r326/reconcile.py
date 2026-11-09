from pathlib import Path
import hashlib, json, sys
D=Path(__file__).resolve().parent
B=D.parent
F=D/'frozen/pi-mathdb-primary-qualified-breadth-r320'
C=B/'pi-mathdb-primary-qualified-breadth-r320'
def read(p): return json.loads(p.read_text())
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''): h.update(block)
    return h.hexdigest()
def write(n,o): (D/n).write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
def check_inputs():
    bindings=read(D/'bindings.json')
    for r in bindings:
        assert sha(Path(r['original']))==r['sha256']
        assert sha(D/r['copy'])==r['sha256']
    child=read(F/'manifest.json')['payloads']
    for r in child:
        assert sha(F/r['path'])==r['sha256']
        assert (F/r['path']).stat().st_size==r['bytes']
    delivered={str(p.relative_to(C)) for p in C.rglob('*') if p.is_file() and 'frozen' not in p.relative_to(C).parts}
    assert delivered=={r['path'] for r in child}|{'manifest.json','verification-receipt.json'}
    refs=read(F/'bindings.json')['bindings']
    for r in refs:
        for p in [Path(r['source']),C/r['copy']]:
            assert sha(p)==r['sha256']
            assert p.stat().st_size==r['bytes']
    old=read(D/'frozen/root-mathdb-breadth-intake-r316/coverage-delta.json')
    reserved=read(D/'frozen/root-mathdb-next-breadth-r318/reserved-ids.json')
    disp=read(F/'dispositions.json')['dispositions']
    assert len(old)==133 and len(reserved)==50 and len(set(reserved))==50
    assert set(map(int,disp))==set(reserved)
    assert not set(map(int,old)) & set(reserved)
    return old,disp,{'root_bindings':len(bindings),'child_payloads':len(child),'upstream_bindings_and_copies':len(refs)}
def derive():
    old,disp,counts=check_inputs()
    coverage=dict(old)
    for i,row in disp.items():
        coverage[i]={'record_statement_review':'delegate_reported_complete','report':'pi-mathdb-primary-qualified-breadth-r320/dispositions.json','disposition':row['disposition'],'reported_evidence_level':row.get('evidence_level'),'source_scope_cleared':False,'prior_cleared':False,'accepted_credit':0}
    assert len(coverage)==183
    rows=[json.loads(l) for l in (D/'frozen/pi-mathdb-full-corpus-inventory-r301/tags/review-queue-top.jsonl').read_text().splitlines() if l]
    queue=[];used=set(map(int,coverage))
    for row in rows:
        i=int(row['mathdb_id'])
        if i in used or row.get('status')!='open' or row.get('statement_completeness')!='full':continue
        used.add(i);queue.append(row)
        if len(queue)==50:break
    assert len(queue)==50
    return coverage,queue,counts
def payloads(): return sorted(p for p in D.rglob('*') if p.is_file() and str(p.relative_to(D)) not in {'manifest.json','verification-receipt.json'})
if sys.argv[1]=='build':
    coverage,queue,counts=derive()
    write('coverage-delta.json',coverage)
    write('reserved-ids.json',[r['mathdb_id'] for r in queue])
    write('queue.json',queue)
    write('summary.json',{'known_ids':95675,'delegate_reported_statement_reviews':183,'without_report':95492,'new_reported_ids':50,'next_reserved_not_reviewed':50,'retained_primary_body_htmls':3,'additional_body_read_claim_without_retained_body':346000,'triage_proposals':[347483,338062,327474],'proposals_not_prior_or_source_scope_cleared':True,'accepted_additional':9,'accepted_total':39,'next_outcome':40,'integrity':counts})
    write('manifest.json',[{'path':str(p.relative_to(D)),'sha256':sha(p),'bytes':p.stat().st_size} for p in payloads()])
else:
    coverage,queue,counts=derive()
    assert read(D/'coverage-delta.json')==coverage
    assert read(D/'queue.json')==queue
    assert read(D/'reserved-ids.json')==[r['mathdb_id'] for r in queue]
    rows=read(D/'manifest.json')
    assert {r['path'] for r in rows}=={str(p.relative_to(D)) for p in payloads()}
    for r in rows:
        assert sha(D/r['path'])==r['sha256']
        assert (D/r['path']).stat().st_size==r['bytes']
    counts.update(result='PASS',root_payloads=len(rows),reported_reviews=183,next_disjoint_reservation=50,scope='Integrity and coverage reconciliation; no mathematical/prior clearance')
    write('verification-receipt.json',counts);print(json.dumps(counts))
