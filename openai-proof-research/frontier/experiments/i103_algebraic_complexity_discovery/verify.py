"""Offline READ-ONLY integrity/finite-check replay. No proof or novelty certification.

Run with python -B. --preseal validates content before the one final seal exists.
Neither mode downloads, writes, extracts, repairs, or creates a seal.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json, hashlib, re, collections, runpy

ROOT=Path(__file__).resolve().parents[3]
S=Path('frontier/sources/i103_algebraic_complexity_discovery')
X=Path('frontier/experiments/i103_algebraic_complexity_discovery')
REPORT=Path('frontier/iterations/i103-algebraic-complexity-discovery.md')
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
ALLOW=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
def raw(p):return (ROOT/p).read_bytes()
def sha(p):return hashlib.sha256(raw(p)).hexdigest()
def data(p):return json.loads(raw(p))
def check(ok,msg):
    if not ok:raise AssertionError(msg)
def inventory():
    ans=[REPORT]
    for base in [S,X]:
        for p in (ROOT/base).rglob('*'):
            check(not p.is_symlink(),f'owned symlink: {p}')
            if p.is_file():ans.append(p.relative_to(ROOT))
    return sorted(str(p) for p in ans)
def main():
    check(sys.argv[1:] in [[],['--preseal']],'only --preseal is supported')
    pre=bool(sys.argv[1:]); files=inventory(); sealpath=str(S/'seal.json')
    if pre:
        check(not (ROOT/sealpath).exists(),'preseal mode requires no seal')
    else:
        seal=data(sealpath)
        check(seal['pin']==PIN,'seal revision')
        check(set(files)==set(seal['files'])|{sealpath},'exact owned inventory')
        for p,h in seal['files'].items():check(sha(p)==h,f'owned hash: {p}')
    refs=data(S/'immutable-references.json')
    check(refs['only_live_drift_allowlist']==ALLOW,'drift allowlist changed')
    drift=[]
    for r in refs['references']:
        check('i101_' not in r['path'] and 'i102_' not in r['path'],'active output bound')
        if r['drift_allowed']:
            check(r['path'] in ALLOW,'extra mutable reference')
            check(sha(r['snapshot'])==r['sha256'],'mutable snapshot hash')
            if sha(r['path'])!=r['sha256']:drift.append(r['path'])
        else:
            check(sha(r['path'])==r['sha256'],f'immutable reference: {r["path"]}')
    for p in (ROOT/S/'snapshots').rglob('*'):
        if p.is_file():
            rel=p.relative_to(ROOT/S/'snapshots')
            if str(rel) not in ALLOW:check(raw(rel)==p.read_bytes(),f'original snapshot: {rel}')
    tree=data(S/'snapshots/sources/preprints-tree.json')['tree']
    blobs={x['path']:x for x in tree if x['type']=='blob'}
    D=data(S/'search-domain.json')
    check(D==data('frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'),'frozen domain differs')
    check(len(tree)==13223 and len(blobs)==10373 and len(D)==10373,'domain counts')
    check(len({x['path'].split('/')[1] for x in tree})==749,'manuscript count')
    check(len({d['path'] for d in D})==len(D) and {d['path'] for d in D}==set(blobs),'exact original positions')
    Q=data(S/'queries.json'); hits=[]; counts=collections.Counter()
    for d in D:
        b=raw(d['local']); orig=raw(d['original_local'])
        check(hashlib.sha256(b).hexdigest()==d['sha256'],f'text: {d["path"]}')
        check(hashlib.sha256(orig).hexdigest()==d['original_sha256'],f'original: {d["path"]}')
        git=hashlib.sha1(b'blob '+str(len(orig)).encode()+b'\0'+orig).hexdigest()
        check(git==d['git_sha']==blobs[d['path']]['sha'],f'Git blob: {d["path"]}')
        for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
            for key,expr in Q.items():
                for m in re.finditer(expr,line):
                    counts[key]+=1
                    hits.append({'query':key,'path':d['path'],'local':d['local'],'line_splitlines':i,'start':m.start(),'end':m.end(),'match':m.group(),'line':line})
    expected=[json.loads(x) for x in raw(S/'lexical-hits.jsonl').decode().splitlines()]
    check(hits==expected,'exact ordered lexical match multiset')
    summary=data(S/'search-summary.json')
    check(dict(counts)==summary['counts'] and sum(counts.values())==1401,'lexical count')
    family=data(S/'family-screen.json')
    selected=[d for d in D if any(k in d['path'].split('/')[1] for k in family['title_expressions'])]
    check(selected==data(S/'selected-inventory.json') and len(selected)==181,'exact selected family positions')
    check(dict(collections.Counter(d['path'].split('/')[1] for d in selected))==family['families'],'family counts')
    reads=[json.loads(x) for x in raw(S/'read-manifest.jsonl').decode().splitlines()]
    bypath={d['path']:d for d in D}
    for r in reads:
        check(r['local']==bypath[r['source']]['local'],'read source location')
        check(sha(r['local'])==r['sha256'],'read source hash')
        ls=raw(r['local']).decode().splitlines();a,z=r['first'],r['last']
        check(1<=a<=z<=len(ls),'read range')
        check(hashlib.sha256(('\n'.join(ls[a-1:z])+'\n').encode()).hexdigest()==r['passage_sha256'],'read passage hash')
    for prefix,sections in {
        'Polynomial-Hitting-Lists':['encoding.tex','expansion.tex','division.tex','generator.tex','rank.tex','introduction.tex'],
        'Uniform-Matrix-Hitting':['construction.tex','order.tex','words.tex','systems.tex','introduction.tex']}.items():
        for section in sections:
            rr=[r for r in reads if prefix in r['source'] and r['source'].endswith('/'+section)]
            check(bool(rr),'missing required proof read')
            n=len(raw(rr[0]['local']).decode().splitlines())
            union=set().union(*(set(range(r['first'],r['last']+1)) for r in rr))
            check(union==set(range(1,n+1)),f'incomplete required proof read: {prefix}/{section}')
    rr=[r for r in reads if 'Matrix-Multiplication-Nine-Fourths' in r['source']]
    check(set(range(1,905))<=set().union(*(set(range(r['first'],r['last']+1)) for r in rr)),'N proof ending coverage')
    contracts=data(S/'source-contracts.json');check(contracts['pin']==PIN,'contract revision')
    for c in contracts['sources']:
        d=bypath[c['path']]
        check(all(c[k]==v for k,v in d.items()),'contract source mapping')
        check(c['pinned_url']=='https://raw.githubusercontent.com/openai/math/'+PIN+'/'+d['path'],'contract URL')
        lines=raw(d['local']).decode().splitlines()
        labels=[{'label':m.group(1),'line_splitlines':i} for i,l in enumerate(lines,1) for m in re.finditer(r'\\label\{([^}]+)\}',l)]
        check(c['labels']==labels,'exact source labels')
        check(c['recorded_reads']==[{'first':r['first'],'last':r['last']} for r in reads if r['source']==d['path']],'contract read ranges')
    ext=data(S/'external-read-manifest.json')
    for r in ext:
        check(sha(r['source'])==r['sha256'],'external text hash')
        ls=raw(r['source']).decode().split('\n');a,z=r['first'],r['last']
        check(1<=a<=z<=len(ls),'external LF range')
        check(hashlib.sha256(('\n'.join(ls[a-1:z])+'\n').encode()).hexdigest()==r['passage_sha256'],'external LF passage')
    for r in data(S/'external-requests.json'):
        if r.get('status')==200:
            p=S/'external'/(r['name']+'.pdf')
            check(sha(p)==r['sha256'] and len(raw(p))==r['bytes'],'external response bytes')
    diagnostics=runpy.run_path(str(ROOT/X/'check_math.py'))['run']()
    check(diagnostics==data(X/'exact-results.json'),'exact diagnostics replay')
    check(diagnostics['status']=='PASS','finite diagnostics failed')
    return {'status':'PRESEAL_PASS' if pre else 'PASS','scope':'Integrity and finite diagnostics only; no universal proof or contribution certification',
        'owned_files':len(files),'original_positions':len(D),'selected_positions':len(selected),'lexical_matches':len(hits),
        'read_passages':len(reads),'external_LF_passages':len(ext),'exact_diagnostics':diagnostics,'allowed_live_ledger_drift':drift}

if __name__=='__main__':
    try:print(json.dumps(main(),indent=2,ensure_ascii=False))
    except Exception as e:
        print(json.dumps({'status':'FAIL','error':type(e).__name__+': '+str(e)}));raise
