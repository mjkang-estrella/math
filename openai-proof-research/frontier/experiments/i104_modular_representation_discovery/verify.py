"""I104 OFFLINE READ-ONLY replay. Usage: python -B verify.py [--preseal].
No downloads, writes, bytecode, repair or seal operation. Preparation is separate.
This validates evidence and finite diagnostics, not universal mathematics.
"""
import sys
if not sys.dont_write_bytecode or sys.flags.optimize:
    raise SystemExit('Require python -B without -O')
import os, json, hashlib, re, subprocess
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parents[3]
S=Path('frontier/sources/i104_modular_representation_discovery')
E=Path('frontier/experiments/i104_modular_representation_discovery')
REPORT=Path('frontier/iterations/i104-modular-representation-discovery.md')
SEAL=S/'seal.json'; SEALHASH=S/'seal.sha256'

def readonly(event,args):
    if event=='open':
        mode=args[1];flags=args[2]
        if (isinstance(mode,str) and any(x in mode for x in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise RuntimeError('Read-only verifier rejected file write')
    if event in {'os.remove','os.rename','os.mkdir','os.rmdir','os.chmod','os.chown','os.link','os.symlink','os.truncate','socket.connect','socket.bind','socket.getaddrinfo'}:
        raise RuntimeError('Read-only/offline verifier rejected '+event)
sys.addaudithook(readonly)

def require(ok,message):
    if not ok:raise AssertionError(message)
def blob(path):return (ROOT/path).read_bytes()
def digest(b):return hashlib.sha256(b).hexdigest()
def js(path):return json.loads(blob(path))
def owned():
    out=[REPORT]
    for directory in [S,E]:
        for p in (ROOT/directory).rglob('*'):
            require(not p.is_symlink(),'Owned symlink '+str(p))
            if p.is_file():out.append(p.relative_to(ROOT))
    return sorted(str(p) for p in out)

def run(preseal=False):
    result={'mode':'preseal' if preseal else 'final','read_only':True,'offline':True,'bytecode_disabled':True}
    current=owned()
    if preseal:
        require(str(SEAL) not in current and str(SEALHASH) not in current,'Preseal refuses an existing seal')
    else:
        raw=blob(SEAL)
        require(blob(SEALHASH).decode().strip()==digest(raw),'Seal digest mismatch')
        seal=json.loads(raw)
        require(current==seal['owned_inventory'],'Exact owned inventory mismatch')
        require(set(seal['files'])==set(current)-{str(SEAL),str(SEALHASH)},'Seal hash scope mismatch')
        for p,h in seal['files'].items():require(digest(blob(p))==h,'Owned hash mismatch '+p)
        result['owned_files']=len(current)
    for row in js(S/'immutable-references.json'):
        require(digest(blob(row['path']))==row['sha256'],'Immutable reference mismatch '+row['path'])
    upstream=js('sources/upstream.json')
    require('fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb' in json.dumps(upstream),'Wrong upstream pin')
    tree=js('sources/preprints-tree.json')
    require(not tree.get('truncated',False),'Truncated complete-tree input')
    require(len(tree['tree'])==13223,'Tree entry count')
    original={x['path']:x for x in tree['tree'] if x['type']=='blob'}
    require(len(original)==10373,'Original blob count')
    q=js(S/'queries.json');domain=js(q['domain'])
    require(Counter(x['path'] for x in domain)==Counter(original.keys()),'Domain path multiset differs from tree')
    require(Counter(x['kind'] for x in domain)=={'corpus':9340,'outside_pdf':776,'outside_bytes':257},'Domain kinds')
    pats={k:re.compile(v,re.I) for k,v in q['queries'].items()};hits={k:[] for k in pats}
    for row in domain:
        b=blob(row['original_local'])
        require(digest(b)==row['original_sha256'],'Original SHA256 '+row['path'])
        git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(git==row['git_sha']==original[row['path']]['sha'],'Original Git blob '+row['path'])
        require(len(b)==original[row['path']]['size'],'Original size '+row['path'])
        rep=b if row['local']==row['original_local'] else blob(row['local'])
        require(digest(rep)==row['sha256'],'Representation SHA256 '+row['path'])
        for ln,line in enumerate(rep.decode('utf-8',errors='replace').splitlines(),1):
            for name,pat in pats.items():
                for m in pat.finditer(line):hits[name].append({'path':row['path'],'line':ln,'span':list(m.span()),'match':m.group(),'text':line})
    result['original_blobs']=len(domain);result['inherited_pdf_texts_hash_checked']=776
    result['searches']={}
    for name,rows in hits.items():
        rows.sort(key=lambda x:(x['path'],x['line'],x['span']))
        encoded=''.join(json.dumps(r,ensure_ascii=False,sort_keys=True)+'\n' for r in rows).encode()
        require(encoded==blob(S/('search-'+name+'.jsonl')),'Complete search multiset mismatch '+name)
        result['searches'][name]={'occurrences':len(rows),'families':len({r['path'].split('/')[1] for r in rows})}
    titles=sorted({r['path'].split('/')[1] for r in domain});ts=js(S/'title-screen.json')
    require(len(titles)==ts['total_titles']==749,'Family count')
    pat=re.compile(ts['pattern'],re.I)
    require([x for x in titles if pat.search(x)]==ts['matches'],'Title-screen mismatch')
    selected=js(S/'selected-inventory.json')
    selected_families={r['path'].split('/')[1] for r in selected}
    require(len(selected_families)==5,'Selected-family scope')
    require(selected==[r for r in domain if r['path'].split('/')[1] in selected_families],'Selected inventory exactness')
    for entry in js(S/'passages.json')['passages']:
        raw=blob(entry['local']);text=raw.decode('utf-8',errors='replace');lines=text.splitlines()
        require(digest(raw)==entry['sha256'],'Passage source hash '+entry['local'])
        require(len(lines)==entry['splitlines_count'] and len(text.split('\n'))==entry['lf_split_count'],'Passage line conventions')
        selected_lines=lines[entry['first']-1:entry['last']]
        require(selected_lines[0]==entry['first_line'] and selected_lines[-1]==entry['last_line'],'Passage endpoints')
        require(digest(('\n'.join(selected_lines)+'\n').encode())==entry['passage_sha256'],'Passage exact bytes')
    result['passages']=len(js(S/'passages.json')['passages'])
    scope=js(S/'extraction-scope.json')
    require(len(scope['pdfs'])==8,'Selective extraction limit')
    require(scope['pdfs']==[str(p.relative_to(ROOT)) for p in sorted((ROOT/S/'external').glob('*.pdf'))],'PDF extraction inventory')
    for p in scope['pdfs']:
        process=subprocess.run(['pdftotext','-layout',str(ROOT/p),'-'],capture_output=True,check=False)
        require(process.returncode==0,'PDF extraction failure '+p+': '+process.stderr.decode(errors='replace'))
        require(process.stdout==blob(p+'.txt'),'Selected PDF text differs '+p)
    result['external_pdfs_reextracted']=len(scope['pdfs'])
    process=subprocess.run([sys.executable,'-B',str(ROOT/E/'diagnostics.py')],capture_output=True,check=False)
    require(process.returncode==0,'Finite diagnostics failed '+process.stderr.decode(errors='replace'))
    diagnostics=json.loads(process.stdout)
    require(diagnostics==js(E/'diagnostics.json'),'Diagnostic replay mismatch')
    initial=js(E/'diagnostics-initial.json')
    require(initial['cycle_reconstructions']==683,'Initial diagnostic record changed')
    require(diagnostics['cycle_reconstructions']==683,'Cycle reconstruction count')
    for row in diagnostics['twisted']:
        if row['group']=='A5' and row['p']==2:
            for s,actual in enumerate(row['generating_orbit_residues']):
                if s==0:continue
                n=2**s;mod=row['modulus'];coef=4 if row['t']==7 else 2
                expected=(pow(15,n,mod)-coef*pow(3,n,mod)-2*pow(5,n,mod)+3)%mod
                require(actual==expected,'Analytic A5 formula disagrees with finite computation')
    result['finite_diagnostics']={'partitions':683,'tuple_cases':len(diagnostics['twisted']),'s_range':[0,10]}
    result['status']='PASS'
    result['boundary']='Evidence integrity and finite replay only; no universal proof or contribution certification.'
    return result
if __name__=='__main__':
    require(sys.argv[1:] in [[],['--preseal']],'Only optional --preseal is supported')
    try:
        print(json.dumps(run(sys.argv[1:]==['--preseal']),indent=2))
    except Exception as exc:
        print(json.dumps({'status':'FAIL','type':type(exc).__name__,'message':str(exc)},indent=2))
        raise SystemExit(1)
