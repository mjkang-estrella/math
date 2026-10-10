#!/usr/bin/env python3
"""Exact full-domain review search. Default read-only replay; --prepare preseal only."""
import hashlib,json,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
SRC=ROOT/'frontier/sources/i92_anchored_rank_approximation_r2'
MAP=ROOT/'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'
QUERIES=[('continuation',r'matched walks?|exceptional.direction|continuation records?'),('classical',r'Auerbach|local.reflexivity')]
def compute():
    domain=json.loads(MAP.read_bytes());out={name:[] for name,_ in QUERIES}
    pats=[(name,re.compile(pat,re.I)) for name,pat in QUERIES]
    for r in domain:
        for no,line in enumerate((ROOT/r['local']).read_text(encoding='utf-8',errors='replace').splitlines(),1):
            for name,pat in pats:
                if pat.search(line):out[name].append(dict(path=r['path'],local=r['local'],line=no,text=line))
    return out

def main():
    prepare=sys.argv[1:]==['--prepare'];assert not sys.argv[1:] or prepare
    if prepare:assert not (SRC/'seal.json').exists()
    out=compute();summary=[]
    for name,pat in QUERIES:
        data=''.join(json.dumps(r,ensure_ascii=False)+'\n' for r in out[name]).encode()
        row=dict(name=name,pattern=pat,flags='IGNORECASE',records=len(out[name]),manuscripts=len({r['path'].split('/')[1] for r in out[name]}),sha256=hashlib.sha256(data).hexdigest())
        p=SRC/('search-'+name+'.jsonl')
        if prepare:p.write_bytes(data)
        else:assert p.read_bytes()==data,name
        summary.append(row)
    if prepare:(SRC/'queries.json').write_text(json.dumps(summary,indent=2)+'\n')
    else:assert json.loads((SRC/'queries.json').read_bytes())==summary
    print(json.dumps(dict(original_positions=10373,queries=summary,status='PREPARED' if prepare else 'EXACT SEARCH MULTISETS PASS'),indent=2))
if __name__=='__main__':main()
