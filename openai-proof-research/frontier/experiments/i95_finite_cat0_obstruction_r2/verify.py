"""Offline READ-ONLY I95 evidence verifier. No fetch/write/bytecode/repair/reseal.
--preseal validates before the one final seal exists; never creates a seal.
"""
import sys
sys.dont_write_bytecode=True
import argparse,json,re,subprocess
from evidence import *
from independent import reconstruct,check_certificate
from diagnostics import run as diagnostics

def check(p,h):assert sha(raw(p))==h,'hash mismatch: '+p

def inherited_seal(base,expected):
    p=base+'/seal-v1.json';check(p,expected);d=load(p)
    assert d['pin']==PIN
    assert raw(base+'/seal-v1.sha256').decode().split()[0]==expected
    files=d['files']
    if isinstance(files,dict):files=[{'path':p,**v} for p,v in files.items()]
    expected_names=sorted([x['path'] for x in files]+d['exclusions'])
    actual=[d['owned_report']]
    for directory in d['owned_directories']:
        for item in path(directory).rglob('*'):
            n=item.relative_to(R).as_posix();path(n)
            if item.is_file():actual.append(n)
    assert sorted(actual)==expected_names,'original exact domain: '+base
    for item in files:check(item['path'],item['sha256']);assert len(raw(item['path']))==item['bytes']
    return len(files)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--preseal',action='store_true');args=ap.parse_args()
    before=inventory();before_hashes={p:sha(raw(p)) for p in before}
    if args.preseal:assert not any(path(p).exists() for p in EX)
    else:
        seal=load(EX[0]);check(EX[0],raw(EX[1]).decode().split()[0])
        assert raw(EX[1]).decode()==sha(raw(EX[0]))+'  seal-v1.json\n'
        assert seal['pin']==PIN and seal['owned_report']==REPORT and seal['owned_directories']==[S,E]
        assert seal['exclusions']==EX and seal['mutable_ledgers']==MUTABLE
        assert seal['original_proof']=='ORIGINAL_PASS_WITHOUT_REPAIRS'
        assert seal['Q89']=='CLOSED_AT_FINITE_CONTRACTION_SCOPE'
        fs=seal['files'];assert [d['path'] for d in fs]==sorted({d['path'] for d in fs})
        assert before==sorted([d['path'] for d in fs]+EX),'exact owned domain'
        for d in fs:check(d['path'],d['sha256']);assert len(raw(d['path']))==d['bytes']
    refs=load(S+'/immutable-references.json')
    assert [d['path'] for d in refs]==sorted({d['path'] for d in refs})
    assert not any('i94_' in d['path'] or 'i96_' in d['path'] for d in refs)
    for d in refs:check(d['path'],d['sha256'])
    assert load('sources/upstream.json')['commit']==PIN
    check('frontier/experiments/i91-parent-verification.json','fea7c7af195fb688ff68cf9a11bf053bf84b1f816998fa7d2bd39b9f2fc32f37')
    check('frontier/iterations/i91-finite-cat0-obstruction.md','2b6b3ace4fa6b664dbf0d642d85757ac7ae9a09fcf60b8dd4ec07096be6afce7')
    check('frontier/iterations/i89-geometric-group-discovery.md','29adb44728edee78ef949c390de75cb9c486da8860bcf7817898f132bb4f86be')
    old={}
    for lane,h in [('i89_geometric_group_discovery','4d9c2b12ad1bc77dd8c313164e62cc9c9ed80aab1bce82f8cd60de33225a0583'),('i91_finite_cat0_obstruction','ba5e4a80bae104f88eede8df76e0f0f75b05e84bbe185de108347bbc6caa82e8')]:
        old[lane]=inherited_seal('frontier/sources/'+lane,h)
    inputs=load(S+'/inputs.json');assert [d['path'] for d in inputs]==sorted(MUTABLE+['AGENTS.md'])
    drift=[]
    for d in inputs:
        assert d['mutable']==(d['path'] in MUTABLE);check(d['snapshot'],d['sha256'])
        if sha(raw(d['path']))!=d['sha256']:
            assert d['mutable'],'undeclared input drift';drift.append(d['path'])
    readings=load(S+'/readings.json')
    assert readings==sorted(readings,key=lambda d:(d['path'],d['start'],d['end']))
    for d in readings:
        b=raw(d['path']);check(d['path'],d['source_sha256']);lines=b.decode().splitlines(keepends=True)
        assert 1<=d['start']<=d['end']<=len(lines)
        passage=''.join(lines[d['start']-1:d['end']]);assert sha(passage.encode())==d['passage_sha256']
        assert re.findall(r'\\label\{([^}]+)\}',passage)==d['labels']
    searches=load(S+'/searches.json');records,hits,corpus=complete_domain(searches)
    assert records==load(S+'/body-inventory.json')
    assert '\n'.join(corpus)+'\n'==raw(S+'/corpus-rg-files.txt').decode()
    for q,h in zip(searches,hits):assert len(h)==q['count'] and h==load(q['output'])
    pdfs=load(S+'/selected-pdf-replays.json');assert len(pdfs)==5
    for d in pdfs:
        check(d['pdf'],d['pdf_sha256']);check(d['text'],d['text_sha256'])
        result=subprocess.run(['pdftotext','-layout',str(path(d['pdf'])),'-'],cwd=R,capture_output=True)
        assert result.returncode==0 and result.stdout==raw(d['text']),'PDF re-extraction: '+d['pdf']
    # Bind retained HTTP response evidence to actual bytes and explicit versions.
    responses=load('frontier/sources/i91_finite_cat0_obstruction/primary/responses.json')
    for d in responses:assert d['status']==200 and d['headers'];check(d['local'],d['sha256']);assert len(raw(d['local']))==d['bytes']
    assert b'arXiv:1512.01736v1' in raw('frontier/sources/i91_finite_cat0_obstruction/primary/berg-nikolaev.txt')
    assert b'arXiv:1210.5829v1' in raw('frontier/sources/i89_geometric_group_discovery/primary/ikn.txt')
    certificate=check_certificate(reconstruct());assert json.loads(json.dumps(certificate))==load(E+'/independent-output.json')
    diagnostic=diagnostics();assert diagnostic==load(E+'/diagnostics-output.json')
    historical=load(E+'/original-i91-replay.json')
    assert historical['status']=='PASS_EVIDENCE_ONLY' and historical['Q91']=='AUTHOR_PROOF_REQUIRES_INDEPENDENT_REVIEW'
    assert historical['original_blobs_verified']==10373
    # The saved old verdict is intentionally NOT changed to this review's analytic verdict.
    assert before==inventory(),'owned inventory changed while verifying'
    assert before_hashes=={p:sha(raw(p)) for p in before},'owned bytes changed while verifying'
    for d in refs:check(d['path'],d['sha256'])
    if not args.preseal:
        for d in fs:check(d['path'],d['sha256'])
    print(json.dumps({'status':'PASS_PRESEAL_EVIDENCE_ONLY' if args.preseal else 'PASS_EVIDENCE_ONLY','mode':'OFFLINE_READ_ONLY','pin':PIN,'original_proof':'ORIGINAL_PASS_WITHOUT_REPAIRS_IN_SEPARATE_I95_REPORT','original_prerequisites':'SCOPED_ORIGINAL_PASS_WITHOUT_REPAIRS_R89_H89_E89_NOT_AUDITED','Q89':'CLOSED_AT_FINITE_CONTRACTION_SCOPE','contribution':'SEPARATE_NOT_DECIDED_I96_NOT_BOUND','presentation':'NOT_OUTPUT','size_runtime_bound':'NONE_CLAIMED','finding_count_change':0,'owned_files':len(before),'immutable_references':len(refs),'readings':len(readings),'original_seal_file_counts':old,'manuscripts':749,'original_blobs':len(records),'outside_originals':1033,'corpus_originals':9340,'outside_PDF_hashes':776,'selected_PDF_reextractions':len(pdfs),'search_hits':{q['name']:len(h) for q,h in zip(searches,hits)},'allowed_live_drift':drift,'certificate':{k:certificate[k] for k in ['status','points','variables','midpoints','rows','used_rows','updates','margin','nonzero_outward_roundings']},'diagnostics':diagnostic},indent=2,sort_keys=True))
if __name__=='__main__':
    try:main()
    except Exception as e:
        print(json.dumps({'status':'FAIL_EVIDENCE','error':str(e)},sort_keys=True));raise
