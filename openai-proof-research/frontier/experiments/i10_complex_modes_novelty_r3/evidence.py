import argparse, datetime, hashlib, json, pathlib, re, urllib.request
ROOT = pathlib.Path(__file__).resolve().parents[3]
OUT = ROOT/'frontier/sources/i10_complex_modes_novelty_r3'
PIN = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def stamp(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b): return hashlib.sha256(b).hexdigest()
def write(name, data): (OUT/name).write_text(json.dumps(data,indent=2)+'\n')
def append(name, row):
    p=OUT/name; data=json.loads(p.read_text()) if p.exists() else []; data.append(row); write(name,data)
def init():
    paths=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json',
    'frontier/iterations/i10-complex-prime-modes.md','frontier/reviews/i10-complex-prime-modes-r2.md',
    'frontier/iterations/i10-complex-modes-proof-integration.md','frontier/iterations/i07-arithmetic.md',
    'frontier/findings/R006-progression-PD-primitive-root-density.md','frontier/findings/R008-parity-PD-independence.md',
    'frontier/reviews/i03-arithmetic-progressions-r4.md','frontier/reviews/i03-arithmetic-novelty-r5.md',
    'frontier/reviews/i05-parity-pd-r2.md','frontier/reviews/i05-parity-novelty-r3.md',
    'frontier/iterations/i05-parity-pd.md','frontier/iterations/i03-arithmetic-progressions.md']
    records=[]
    for p in paths:
        b=(ROOT/p).read_bytes(); records.append(dict(path=p,sha256=sha(b),bytes=len(b)))
    write('input-manifest.json',dict(retrieved_utc=stamp(),files=records))
    tree=json.loads((ROOT/'sources/preprints-tree.json').read_text()); entries=tree['tree']
    families=sorted({x['path'].split('/')[1] for x in entries})
    pattern=r'prime|riemann|elliott|dirichlet|dickman|multiplicative|additive|sieve|factorization|totient|smooth'
    selected=[f for f in families if re.search(pattern,f,re.I)]
    write('inventory-screen.json',dict(truncated=tree['truncated'],entries=len(entries),blobs=sum(x['type']=='blob' for x in entries),directories=len(families),pattern=pattern,selected=selected))
    (OUT/'complete-preprint-inventory.txt').write_text('\n'.join(x['path'] for x in entries)+'\n')
    print(json.dumps(dict(entries=len(entries),families=len(families),selected=selected),indent=2))
def fetch(paths):
    tree={x['path']:x for x in json.loads((ROOT/'sources/preprints-tree.json').read_text())['tree']}
    for p in paths:
        url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{p}'
        b=urllib.request.urlopen(url,timeout=60).read(); blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        assert blob==tree[p]['sha'],p
        dest=OUT/'pinned'/p; dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(b)
        append('retrieval-manifest.json',dict(path=p,url=url,local=str(dest.relative_to(ROOT)),retrieved_utc=stamp(),bytes=len(b),sha256=sha(b),git_blob=blob,tree_match=True))
        print(p,len(b))
def read(path,start,end):
    p=ROOT/path; b=p.read_bytes(); lines=b.decode().splitlines(); end=min(end or len(lines),len(lines))
    append('inspected-ranges.json',dict(path=path,start=start,end=end,sha256=sha(b),read_utc=stamp()))
    for i in range(start-1,end): print(f'{i+1}: {lines[i]}')
if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('mode'); ap.add_argument('args',nargs='*'); a=ap.parse_args()
    if a.mode=='init': init()
    elif a.mode=='fetch': fetch(a.args)
    elif a.mode=='read': read(a.args[0],int(a.args[1]) if len(a.args)>1 else 1,int(a.args[2]) if len(a.args)>2 else None)
