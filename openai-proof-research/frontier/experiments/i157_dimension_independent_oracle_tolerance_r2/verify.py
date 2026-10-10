"""Offline read-only I157 evidence replay; never executes ancestor programs."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import os,json,hashlib,re,collections,math
from fractions import Fraction
R=Path(__file__).resolve().parents[3]
S='frontier/sources/i157_dimension_independent_oracle_tolerance_r2'
E='frontier/experiments/i157_dimension_independent_oracle_tolerance_r2'
REPORT='frontier/reviews/i157-dimension-independent-oracle-tolerance-r2.md'
LEDGERS=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
def guard(event,args):
    if event=='open':
        mode,flags=args[1:3]
        if isinstance(mode,str) and any(x in mode for x in 'wax+'):raise RuntimeError('write denied')
        if isinstance(flags,int) and flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND):raise RuntimeError('write flags denied')
    if event.startswith(('socket.','subprocess.','ctypes.')) or event in {'os.mkdir','os.remove','os.rename','os.rmdir','os.link','os.symlink','os.chmod','os.truncate','os.utime','os.system','os.exec','os.posix_spawn','os.fork','os.forkpty','os.chdir','os.fchdir','os.replace','os.unlink','os.chown','os.lchown','os.fchmod','os.fchown','os.ftruncate','os.setxattr','os.removexattr'}:raise RuntimeError('operation denied: '+event)
sys.addaudithook(guard)
CACHE={}
def read(p):
    if p not in CACHE:CACHE[p]=(R/p).read_bytes()
    return CACHE[p]
def sha(b):return hashlib.sha256(b).hexdigest()
def data(p):return json.loads(read(p))
def files():
    ans={REPORT}
    for base in [S,E]:
        for p in (R/base).rglob('*'):
            assert not p.is_symlink()
            if p.is_file():ans.add(str(p.relative_to(R)))
    return ans
def leaves(obj):
    if isinstance(obj,dict):return [z for v in obj.values() for z in leaves(v)]
    if isinstance(obj,list):return [z for v in obj for z in leaves(v)]
    if not isinstance(obj,str):return [json.dumps(obj,ensure_ascii=False)]
    out=[];pos=start=0;decoder=json.JSONDecoder()
    while pos<len(obj):
        match=re.search(r'[\[{]',obj[pos:])
        if match is None:break
        k=pos+match.start()
        try:value,n=decoder.raw_decode(obj[k:])
        except ValueError:pos=k+1;continue
        if isinstance(value,(dict,list)):
            out.extend(x.strip() for x in obj[start:k].split('\n\n') if x.strip());out.extend(leaves(value));pos=start=k+n
        else:pos=k+1
    out.extend(x.strip() for x in obj[start:].split('\n\n') if x.strip())
    return out
def marked(txt,pattern):
    ms=list(re.finditer(pattern,txt))
    return [(m.group(1),txt[m.end():ms[i+1].start() if i+1<len(ms) else len(txt)].strip()) for i,m in enumerate(ms)]
def context_check():
    c=data(S+'/decoded-occurrences.json');decoder=json.JSONDecoder()
    for root in c['roots']:assert sha(read(root['path']))==root['sha256']
    def ordinary(obj,path='task'):
        if isinstance(obj,dict):return [z for key,v in obj.items() for z in ordinary(v,path+'/'+str(key))]
        if isinstance(obj,list):return [z for i,v in enumerate(obj) for z in ordinary(v,path+'/'+str(i))]
        return ['FIELD '+path+'\n'+(obj if isinstance(obj,str) else json.dumps(obj,ensure_ascii=False))]
    taskstreams=[('152-algorithmic-sampling-reconstruction-discovery','i154_dimension_independent_oracle_tolerance'),('148-polynomial-index-torus-subpackets','i152_algorithmic_sampling_reconstruction_discovery'),('145-arithmetic-automorphic-discovery','i148_polynomial_index_torus_subpackets'),('142-uniform-algebraic-allocation','i145_arithmetic_automorphic_discovery'),('139-diffuse-weighted-positivity','i142_uniform_algebraic_allocation'),('136-birational-positivity-discovery','i139_diffuse_weighted_positivity')]
    for name,base in taskstreams:
        task=data('frontier/iterations/iteration'+name+'-task.json')
        assert read('frontier/sources/'+base+'/direct-context.txt').decode()=='\n\n'.join(ordinary(task))+'\n'
    expected=[]
    def occurrence_walk(root,obj,path):
        if isinstance(obj,dict):
            for key,v in obj.items():occurrence_walk(root,v,path+[{'key':key}])
        elif isinstance(obj,list):
            for i,v in enumerate(obj):occurrence_walk(root,v,path+[{'index':i}])
        elif isinstance(obj,str):
            start=pos=0
            while pos<len(obj):
                match=re.search(r'[\[{]',obj[pos:])
                if match is None:break
                k=pos+match.start()
                try:value,n=decoder.raw_decode(obj[k:])
                except ValueError:pos=k+1;continue
                if not isinstance(value,(dict,list)):pos=k+1;continue
                if k>start:expected.append((root,path+[{'slice':[start,k]}]))
                occurrence_walk(root,value,path+[{'embedded':k,'length':n}]);pos=start=k+n
            if start<len(obj) or not obj:expected.append((root,path+[{'slice':[start,len(obj)]}]))
        else:expected.append((root,path))
    for root in c['roots']:occurrence_walk(root['path'],data(root['path']),[])
    assert expected==[(x['root'],x['path']) for x in c['occurrences']]
    for row in c['occurrences']:
        obj=data(row['root'])
        for step in row['path']:
            if 'key' in step:obj=obj[step['key']]
            elif 'index' in step:obj=obj[step['index']]
            elif 'slice' in step:obj=obj[slice(*step['slice'])]
            else:
                obj,n=decoder.raw_decode(obj[step['embedded']:]);assert n==step['length']
        piece=c['pieces'][row['piece']]
        text=obj if isinstance(obj,str) else json.dumps(obj,ensure_ascii=False)
        assert piece==dict(type=type(obj).__name__,text=text,sha256=sha(text.encode()))
    for row in c['inherited_occurrence_records']:assert sha(read(row['path']))==row['sha256']
    old='frontier/sources/i152_algorithmic_sampling_reconstruction_discovery'
    unique=data(old+'/context-unique.json');cov=data(old+'/context-decoding-coverage.json')
    roots=sorted({re.split(r'/(?:task|\d+)(?:/|$)',x['field'],maxsplit=1)[0] for x in cov})
    allparts=[]
    for root in roots:
        pat=r'(?m)^FIELD ([^\n]+)\n' if root.endswith('/direct-context.txt') else r'(?m)^\[(\d+)\]\n'
        for _,part in marked(read(root).decode(),pat):allparts.extend(leaves(part))
    assert len(unique)==2232 and len(cov)==3570
    assert collections.Counter(allparts)==collections.Counter(unique[x['piece']] for x in cov)
    stream=marked(read(old+'/context-unique.txt').decode(),r'(?m)^\[(\d+)\]\n')
    assert [int(k) for k,v in stream]==list(range(len(unique))) and [v for k,v in stream]==unique
    paragraphs=data(old+'/context-paragraphs.json');pcov=data(old+'/context-paragraph-coverage.json')
    for row in pcov:assert read(row['path']).decode()[row['start_char']:row['end_char']]==paragraphs[row['piece']]
    base='frontier/sources/i136_birational_positivity_discovery'
    oldpieces=dict(marked(read(base+'/context-reading.txt').decode(),r'(?m)^\[(\d+)\]\n'))
    oldcov=data(base+'/context-coverage.json');freeze=data(base+'/input-freeze.json')
    rootmap={x['path']:x['snapshot'] for x in freeze if any(c['field'].startswith(x['path']) for c in oldcov)}
    fields={}
    for row in oldcov:fields.setdefault(row['field'],[]).append(oldpieces[str(row['piece'])])
    for field,parts in fields.items():
        root=max((p for p in rootmap if field==p or field.startswith(p+'/')),key=len)
        raw=read(rootmap[root]).decode();obj=json.loads(raw) if root.endswith('.json') else raw
        tail=field[len(root):].lstrip('/')
        for key in tail.split('/') if tail else []:
            if key.startswith('embedded@'):obj=decoder.raw_decode(obj[int(key.split('@')[1]):])[0]
            elif isinstance(obj,list):obj=obj[int(key)]
            else:obj=obj[key]
        assert all(p in obj for p in parts) if isinstance(obj,str) else parts==[json.dumps(obj,ensure_ascii=False)]
    for root,snapshot in rootmap.items():
        raw=read(snapshot).decode();obj=json.loads(raw) if root.endswith('.json') else raw
        assert not set(leaves(obj))-set(unique)
    for p in ['frontier/experiments/i154-parent-verification.json','frontier/experiments/i152-parent-verification.json']:
        parent=data(p);assert json.loads(parent['stdout'])==parent['result']
    return dict(new_occurrences=len(c['occurrences']),inherited_pieces=len(unique),inherited_occurrences=len(cov),inherited_paragraph_occurrences=len(pcov),older_occurrences=len(oldcov),semantic_read_complete=False)
def main():
    pre=sys.argv[1:]==['--preseal'];assert pre or not sys.argv[1:]
    inv=data(S+'/inventory.json');owned=inv['owned_paths'];assert owned==sorted(set(owned))
    if pre:
        assert not (R/S/'seal.json').exists()
        hashes=json.load(sys.stdin);assert set(hashes)==set(owned)-{E+'/validation.json'}
        assert files()==set(hashes)
    else:
        hashes=data(S+'/seal.json')['sha256'];assert list(hashes)==owned
        assert files()==set(owned)|{S+'/seal.json'}
        assert data(E+'/validation.json')['status']=='PASS'
    for p,h in hashes.items():assert sha(read(p))==h,('owned',p)
    immutable=data(S+'/immutable.json');assert [x['path'] for x in immutable]==sorted({x['path'] for x in immutable})
    for row in immutable:
        assert row['path'] not in LEDGERS and not re.search(r'/(?:i|iteration)(155|156)[-_]',row['path'])
        assert sha(read(row['path']))==row['sha256'],('immutable',row['path'])
    for row in data(S+'/snapshots.json'):assert sha(read(row['snapshot']))==row['sha256']
    context=context_check()
    for row in data(S+'/read-log.json'):
        b=read(row['path']);ls=b.decode().splitlines()
        assert sha(b)==row['sha256'] and len(ls)==row['lines']
        assert row['ending']==ls[row['end']-1]
        assert sha('\n'.join(ls[row['start']-1:row['end']]).encode())==row['passage_sha256']
    flat=data(S+'/flat-check.json');assert flat['preparation_traversals']==1
    domain=data(flat['domain']);tree=data(flat['tree'])['tree'];blobs={x['path']:x for x in tree if x['type']=='blob'}
    assert len(tree)==13223 and len(domain)==len(blobs)==10373 and {x['path'] for x in domain}==set(blobs)
    assert sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree)==749
    lexical=[data(p) for p in flat['lexical_records']];patterns={}
    for item in lexical:
        for key,expr in item['patterns'].items():assert key not in patterns;patterns[key]=re.compile(expr)
    found={k:[] for k in patterns};pdfs=0
    for row in domain:
        b=read(row['local']);o=b if row['local']==row['original_local'] else read(row['original_local'])
        assert sha(b)==row['sha256'] and sha(o)==row['original_sha256']
        assert hashlib.sha1(b'blob '+str(len(o)).encode()+b'\0'+o).hexdigest()==row['git_sha']==blobs[row['path']]['sha']
        pdfs+=row['kind']=='outside_pdf'
        for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
            for key,pat in patterns.items():
                ms=list(pat.finditer(line))
                if ms:found[key].append(dict(path=row['path'],local=row['local'],splitlines_line=i,text=line,spans=[list(m.span()) for m in ms]))
    assert pdfs==776
    for item in lexical:
        for key,result in item['results'].items():assert result==found[key],key
    assert flat['lexical_lines']=={k:len(v) for k,v in found.items()}
    assert flat['lexical_occurrences']=={k:sum(len(x['spans']) for x in v) for k,v in found.items()}
    overlaps=['frontier/sources/'+x+'/overlap-search.json' for x in ['i136_birational_positivity_discovery','i145_arithmetic_automorphic_discovery','i152_algorithmic_sampling_reconstruction_discovery','i154_dimension_independent_oracle_tolerance']]
    for p in overlaps:
        ov=data(p);pat=re.compile(ov['expression']);foundrows=[]
        assert ov['paths']==sorted(set(ov['paths']))
        for row in ov.get('refs',[]):assert sha(read(row['path']))==row['sha256']
        for path in ov['paths']:
            assert not re.search(r'/(?:i|iteration)(155|156)[-_]',path)
            for i,line in enumerate(read(path).decode().splitlines(),1):
                ms=list(pat.finditer(line))
                if ms:foundrows.append(dict(path=path,splitlines_line=i,text=line,spans=[list(m.span()) for m in ms]))
        assert foundrows==ov['results']
    print('Immutable owned, inherited, context, corpus, lexical, primary and passage bytes checked before diagnostics.',file=sys.stderr,flush=True)
    result=dict(status='PASS',mode='preseal' if pre else 'sealed read-only',immutable=len(immutable),owned=len(owned),tree_entries=len(tree),manuscripts=749,original_blob_positions=len(domain),pdf_text_bindings=pdfs,context=context,original_proof_verdict='unresolved',scope='Evidence validity only; semantic obligations remain incomplete. No universal correctness or contribution certification.')
    if not pre:
        scope={};exec(compile(read(E+'/diagnostics.py'),E+'/diagnostics.py','exec'),scope)
        result['new_finite_diagnostics']=scope['run']()
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
