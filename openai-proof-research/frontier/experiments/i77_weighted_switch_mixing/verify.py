"""Offline read-only I77 replay. Does not create, fetch, refresh, or repair artifacts."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from collections import Counter
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i77_weighted_switch_mixing'
E=R/'frontier/experiments/i77_weighted_switch_mixing'
REPORT=R/'frontier/iterations/i77-weighted-switch-mixing.md'
LEDGERS={'README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def check(ok,msg):
    if not ok:raise AssertionError(msg)
def check_bytes(row):
    b=(R/row['path']).read_bytes()
    check(len(b)==row['bytes'] and sha(b)==row['sha256'],'bytes '+row['path'])
    return b
def main():
    seal=read(S/'seal-v1.json')
    check(seal['mutable_ledgers']==sorted(LEDGERS),'exact mutable allowlist')
    exclusions={S/'seal-v1.json',E/'verification.json'}
    actual={str(p.relative_to(R)) for base in [S,E] for p in base.rglob('*') if p.is_file() and p not in exclusions}|{str(REPORT.relative_to(R))}
    check(actual=={x['path'] for x in seal['artifacts']},'seal exact coverage')
    for row in seal['artifacts']:check_bytes(row)
    drift=[];refs=read(S/'references.json')
    for row in refs:
        p=row['path'];b=(R/p).read_bytes();good=len(b)==row['bytes'] and sha(b)==row['sha256']
        check(row['mutable']==(p in LEDGERS),'reference mutability '+p)
        if p in LEDGERS:
            snap=(S/'ledgers'/p).read_bytes();check(sha(snap)==row['sha256'] and len(snap)==row['bytes'],'ledger snapshot '+p)
            if not good:drift.append(p)
        else:check(good,'immutable reference drift '+p)
    check({x['path'] for x in refs if x['mutable']}==LEDGERS,'four ledger references')
    tree=read(R/'sources/preprints-tree.json');blobs={x['path']:x for x in tree['tree'] if x['type']=='blob'}
    domain=read(R/'frontier/sources/i72_graph_probability_discovery/corpus-domain.json');C=R/domain['root'];paths={x['path'] for x in domain['files']}
    listing={str(Path(p).relative_to(C)) for p in subprocess.check_output(['rg','--files','--no-ignore',str(C)],text=True).splitlines()}
    check(listing==paths,'fixed domain exact listing')
    corpus_text={}
    for row in domain['files']:
        b=(C/row['path']).read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        check(len(b)==row['bytes'] and sha(b)==row['sha256'] and blob==row['git_blob']==blobs[row['path']]['sha'],'fixed corpus identity '+row['path'])
        corpus_text[row['path']]=b.decode(errors='replace').splitlines()
    inv=read(R/'frontier/sources/i72_graph_probability_discovery/inventory.json')
    check((len(tree['tree']),len(blobs),len(paths))==(13223,10373,9340),'full tree counts')
    check(len({x['path'].split('/')[1] for x in tree['tree']})==749,'manuscript count')
    check([v for k,v in sorted(blobs.items()) if k not in paths]==inv['other_blobs'] and len(inv['other_blobs'])==1033,'outside blob inventory')
    counts={}
    for name,s in read(S/'searches.json').items():
        rx=re.compile(s['regex']);hits=[]
        for p,lines in corpus_text.items():
            for i,line in enumerate(lines,1):
                if rx.search(line):hits.append((p,i,line))
        check(Counter(hits)==Counter(map(tuple,s['line_multiset'])),'fixed line multiset '+name);counts[name]=len(hits)
    pinned=read(S/'pinned-references.json')
    for row in pinned:
        b=check_bytes(row);up=row['upstream_path'];blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        check(blob==row['git_blob']==blobs[up]['sha'],'pinned blob '+up)
        check(row['raw_url']=='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+up,'pinned raw URL')
    passages=read(S/'passages.json');versions=read(S/'versions.json')
    for row in passages+versions:
        txt=''.join((R/row['path']).read_text().splitlines(keepends=True)[row['start']-1:row['end']])
        check(txt==row['text'] and sha(txt.encode())==row['sha256'],'passage '+row['path'])
        if 'latest_displayed' in row:check('<strong>['+row['latest_displayed']+']</strong>' in txt,'capture version')
    requests=read(S/'primary-requests.json');pdfs=0
    for row in requests:
        check(row.get('status')==200 and 'error' not in row,'primary request '+row['name']);b=check_bytes(row);p=R/row['path']
        if p.suffix=='.pdf':
            check(b.startswith(b'%PDF'),'PDF content')
            run=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True)
            check(run.returncode==0 and run.stdout==p.with_suffix('.txt').read_bytes(),'PDF extraction replay '+p.name);pdfs+=1
    fresh=read(S/'fresh-raw-requests.json')
    for row in fresh:
        check(row['status']==200,'fresh pin HTTP')
        b=(R/row['path']).read_bytes();target=next(x for x in pinned if x['raw_url']==row['url'])
        check(sha(b)==row['sha256'] and b==(R/target['path']).read_bytes(),'fresh pin exact bytes')
    run=subprocess.run([sys.executable,'-B',str(E/'diagnostics.py')],cwd=R,capture_output=True,text=True)
    check(run.returncode==0,'diagnostic failure '+run.stderr)
    check(json.loads(run.stdout)==read(E/'diagnostics-first-run.json'),'exact diagnostic replay')
    check((E/'diagnostics-first-run.stderr').read_bytes()==b'','first run stderr')
    print(json.dumps({'status':'PASS_EVIDENCE_AND_FINITE_DIAGNOSTICS','read_only':True,'sealed_artifacts':len(seal['artifacts']),'immutable_and_mutable_references':len(refs),'mutable_ledger_drift':drift,'corpus_files':len(paths),'outside_tree_blobs':1033,'pinned_references':len(pinned),'passages':len(passages),'version_bindings':len(versions),'primary_responses':len(requests),'pdf_text_replays':pdfs,'fresh_raw_pins':len(fresh),'search_line_multisets':counts,'diagnostics':'Exact rational baseline reproduced','analytic_status':'Technical partials and scoped obstructions; W remains GAP. Not an independent proof review.','contribution_status':'No substantial nomination; no count increment.'},indent=2,sort_keys=True))
if __name__=='__main__':
    try:main()
    except Exception as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},indent=2));sys.exit(1)
