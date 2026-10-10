"""Offline READ-ONLY I112 evidence replay. Run with python -B. Never repairs or seals."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,re,subprocess,runpy

ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i112_inverse_boundary_discovery'
E=ROOT/'frontier/experiments/i112_inverse_boundary_discovery'
def read(p):return (ROOT/p).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def data(p):return json.loads(p.read_text())
def main():
    pre=sys.argv[1:]==['--preseal']
    assert not sys.argv[1:] or pre,'unknown arguments'
    inv=data(S/'inventory.json');expected=set(inv['owned_paths']);sealpath=inv['seal_path']
    actual={str(p.relative_to(ROOT)) for base in (S,E) for p in base.rglob('*') if p.is_file()}
    actual.add('frontier/iterations/i112-inverse-boundary-discovery.md')
    missing_validation=str((E/'validation.json').relative_to(ROOT))
    if pre:
        assert not (ROOT/sealpath).exists(),'preseal forbidden after sealing'
        if missing_validation not in actual:expected.remove(missing_validation)
        assert actual==expected,{'extra':sorted(actual-expected),'missing':sorted(expected-actual)}
    else:
        assert actual==expected|{sealpath},{'extra':sorted(actual-expected-{sealpath}),'missing':sorted(expected-actual)}
        sealed=data(ROOT/sealpath)
        assert set(sealed['sha256'])==expected
        for p,h in sealed['sha256'].items():assert sha(read(p))==h,('owned hash',p)
        assert data(E/'validation.json')['status']=='PASS'
    for row in data(S/'immutable-references.json'):
        assert sha(read(row['path']))==row['sha256'],('immutable',row['path'])
    D=data(S/'search-domain.json');tree=data(S/'snapshots/sources/preprints-tree.json')['tree']
    blobs={x['path']:x for x in tree if x['type']=='blob'}
    assert len(tree)==13223 and len(blobs)==10373
    assert sum(x['type']=='tree' and x['path'].count('/')==1 for x in tree)==749
    assert len(D)==10373 and len({x['path'] for x in D})==10373
    assert {x['path'] for x in D}==set(blobs)
    lexical=data(S/'lexical-search.json');computed={k:[] for k in lexical['patterns']}
    pdfs=0
    for x in D:
        b=read(x['local']);o=b if x['local']==x['original_local'] else read(x['original_local'])
        assert sha(b)==x['sha256'],('representation',x['local'])
        assert sha(o)==x['original_sha256'],('original',x['original_local'])
        git=hashlib.sha1(b'blob '+str(len(o)).encode()+b'\0'+o).hexdigest()
        assert git==x['git_sha']==blobs[x['path']]['sha']
        if x['kind']=='outside_pdf':pdfs+=1
        lines=b.decode('utf-8',errors='replace').splitlines()
        for k,pat in lexical['patterns'].items():
            rr=re.compile(pat)
            for i,line in enumerate(lines,1):
                matches=list(rr.finditer(line))
                if matches:computed[k].append({'path':x['path'],'local':x['local'],'splitlines_line':i,
                   'text':line,'spans':[list(m.span()) for m in matches]})
    assert pdfs==776 and computed==lexical['results'],'lexical multiset mismatch'
    passages=data(S/'read-manifest.json')['passages']
    for p in passages:
        b=read(p['local']);assert sha(b)==p['file_sha256']
        t=b.decode('utf-8');lines=t.splitlines() if p['convention']=='splitlines' else t.split('\n')
        excerpt='\n'.join(lines[p['start']-1:p['end']])
        assert excerpt==p['passage'] and sha(excerpt.encode())==p['passage_sha256']
    replay=data(S/'pdf-replay.json');assert len(replay)==inv['selective_pdf_replay_limit']==2
    for p in replay:
        out=subprocess.run(['pdftotext','-layout',str(ROOT/p['pdf']),'-'],capture_output=True,check=True)
        assert out.stdout==read(p['text']),('pdf replay',p['pdf'])
    checks=runpy.run_path(str(E/'diagnostics.py'))['check']()
    assert checks==data(E/'diagnostic-result.json')
    head=data(S/'literature/upstream-head.json')
    assert head['sha']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    result={'status':'PASS','mode':'preseal' if pre else 'sealed read-only',
      'owned_files':len(actual),'original_blob_positions':len(D),'inherited_pdf_text_bindings':pdfs,
      'read_passages':len(passages),'lexical_matched_lines':{k:len(v) for k,v in computed.items()},
      'selected_pdf_reextractions':len(replay),'finite_diagnostics':checks,
      'scope':'source identity and finite algebra only; not universal proof or contribution certification'}
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
