from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def digs(n):
    a=[]
    while n:n,r=divmod(n,10);a.append(r)
    return a
def rev(n):
    r=0
    while n:n,d=divmod(n,10);r=10*r+d
    return r
def check(z):
    a,b,c=(z[k] for k in ['A','B','C'])
    assert a*b==c and rev(a)*rev(b)==rev(c)
    assert [rev(a),rev(b),rev(c)]==[z[k] for k in ['Astar','Bstar','Cstar']]
    x,y=digs(a),digs(b);v=[0]*(len(x)+len(y)-1)
    for i,u in enumerate(x):
        for j,w in enumerate(y):v[i+j]+=u*w
    assert v==z['polynomial_product'] and digs(c)==z['product_digit_polynomial']
    carry=0;ds=digs(c)
    for i,row in enumerate(z['rows_low_to_high']):
        s=v[i] if i<len(v) else 0;d=ds[i] if i<len(ds) else 0
        assert row['i']==i and row['convolution']==s and row['incoming']==carry and row['digit']==d
        assert s+carry-d==10*row['outgoing'];carry=row['outgoing'];assert carry>=0
    assert not carry and len(z['rows_low_to_high'])>=max(len(v),len(ds))
    assert a%10 and b%10 and c%10
    return len(z['rows_low_to_high'])
def main():
    manifest=json.loads((L/'final-manifest.json').read_text())
    expected=set(manifest['files']);actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']}
    assert actual==expected
    for n,r in manifest['files'].items():assert sha(L/n)==r['sha256'] and (L/n).stat().st_size==r['bytes']
    z=json.loads((L/'exact-checks.json').read_text());count=sum(check(t) for t in [z,z['reversed_certificate'],z['seed'],z['two_factor_table1_control']])
    assert [z[k] for k in ['A','B','C']]==[7000000070000007,858088,6006616060066166006616]
    assert z['A']!=rev(z['A']) and z['B']!=rev(z['B']) and z['polynomial_product'][0]==56 and digs(z['C'])[0]==6
    assert z['Astar']==7000000700000007 and z['Bstar']==880858 and z['Cstar']==6166006616600606166006
    originals=[]
    for r in json.loads((L/'frozen-references.json').read_text()):
        assert sha(L/r['copy'])==r['sha256'];ok=sha(Path(r['original']))==r['sha256'];assert ok
        originals.append({'path':r['original'],'unchanged':ok})
    history=[]
    for n in ['history-snapshot.json','earlier-history-snapshot.json','active-lane-snapshot.json']:
        entries=json.loads((L/'sources'/n).read_text());changed=[]
        for e in entries:
            assert hashlib.sha256(e['text'].encode()).hexdigest()==e['sha256']
            p=Path(e['path'])
            if not p.exists() or sha(p)!=e['sha256']:changed.append(e['path'])
        history.append({'snapshot':n,'entries':len(entries),'changed_originals_after_snapshot':changed})
    for line in (L/'retrieval-receipts.jsonl').read_text().splitlines():
        r=json.loads(line)
        if 'sha256' in r:
            assert sha(L/r['file'])==r['sha256']
            if 'text_sha256' in r:assert sha((L/r['file']).with_suffix('.txt'))==r['text_sha256']
    receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':sha(L/'final-manifest.json'),'file_count':len(expected),'exact_carry_rows_checked':count,'originals':originals,'history_checks':history,'claim':'mathematics verified; no novelty or credit acceptance','guard':{'AS_MiB':512,'groupRSS_MiB':512,'CPU_seconds':210,'wall_seconds':230},'separate_verification':True}
    (L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','file_count','exact_carry_rows_checked','history_checks']}))
if __name__=='__main__':main()
