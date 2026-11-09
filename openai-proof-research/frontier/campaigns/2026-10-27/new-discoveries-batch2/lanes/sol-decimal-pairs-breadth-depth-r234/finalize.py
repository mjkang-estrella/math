from pathlib import Path
import hashlib,json,datetime,shutil
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    base=L.parent.parent
    for name in ['upstream.json','CONTENTS.md']:
        p=Path('openai-proof-research/sources')/name
        if p.exists():shutil.copyfile(p,L/'admin'/name)
    rec=[json.loads(s) for s in (L/'retrieval-receipts.jsonl').read_text().splitlines()]
    for r in rec:
        if 'sha256' in r:assert sha(L/r['file'])==r['sha256']
    ledger=json.loads((L/'admin/ledger.json').read_text())
    assert [ledger[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']]==[9,39,40]
    helper=base/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
    provenance={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':str(L),'primary':{'title':'On Polynomial Pairs of Integers','url':'https://cs.uwaterloo.ca/journals/JIS/VOL18/Ezerman/eze3.pdf','version':'JIS18 Article15.3.5','publication_date':'2015-02-14','pages':'2–5: conventions, Proposition1, Table1, Conjecture4; 11–12: Remark13, Proposition14','sha256':sha(L/'sources/eze3.pdf'),'precursor':'https://arxiv.org/pdf/1210.7593v2','precursor_updated':'2014-08-15','precursor_initial':'2012-10-29','source_freeze':'frozen-references.json; source-postread-checks.json'},'retrievals':rec,'source_inventory':{str(p.relative_to(L)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted((L/'sources').iterdir()) if p.is_file()},'freeze_policy':'Direct references and compact report snapshots only. PDFs saved and hashed before body inspection; derived pdftotext saved before reading. No recursive historical trees copied. Administrative files are snapshots only.','guard':{'helper':str(helper),'sha256':sha(helper),'AS_MiB':512,'groupRSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'raised_caps':False},'outcome':{'full_mathematical_candidate':'literal Conjecture4 counterexample','novelty':'unapproved automatic-extension objection; registry heads uncleared','additional_breadth_families':8,'novelty_cleared_survivors':0,'credit_requested':0,'counts_edited':False},'limitations':['No complete current public-registry coverage; denied routes not retried.','No exhaustive historical source-body or script alias screen.','Most current arXiv searches narrow or noisy; absence is not clearance.','No complete classification or Conjecture11 resolution.'],'administrative_catalogue':'upstream and CONTENTS metadata snapshot only; no catalogue theorem was used as a scientific premise'}
    (L/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
    # Last planned artifact write. The manifest intentionally omits itself and the verification receipt.
    files={str(p.relative_to(L)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']}
    (L/'final-manifest.json').write_text(json.dumps({'schema':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'excluded':['final-manifest.json','verification-receipt.json'],'files':files},indent=2)+'\n');print({'manifest_files':len(files),'manifest_sha256':sha(L/'final-manifest.json')})
if __name__=='__main__':main()
