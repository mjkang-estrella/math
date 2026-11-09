import json,re,hashlib,pathlib,sys
IDX='../sol-wide-analytic-probabilistic-scout-r268/science/science--history-index.json'
d=json.load(open(IDX))
terms=['1801.07238','Swanepoel','c.s.c.','centrally symmetric convex position','0704.0275','mapping radi','map-rad','0405017','0407503','Konyagin','9804040','1310.0910','Jerónimo','0707.3052','0001010','Dougherty','9904065','Kolountzakis','0612749','Elkies','0801.1993','Kenyon','Solomyak','0702892','Matheron','covariogram','0410251','Siersma','0708.2663','Socolar','parquet','Hadwiger']
ok=bad=0;hits={t:[] for t in terms}
for r in d['verified_references']:
    p=pathlib.Path(r['path'])
    try: b=p.read_bytes()
    except FileNotFoundError: bad+=1;continue
    if hashlib.sha256(b).hexdigest()!=r['sha256']: bad+=1;continue
    ok+=1;s=b.decode('utf8','replace')
    for t in terms:
        pat=r'\b'+re.escape(t)+r'\b' if t[0].isalpha() and t[-1].isalnum() else re.escape(t)
        for m in re.finditer(pat,s,re.I if t[0].isalpha() else 0):
            hits[t].append(dict(path=str(p),excerpt=s[max(0,m.start()-120):m.end()+120].replace('\n',' ')));break
json.dump(dict(index=IDX,index_sha256=hashlib.sha256(open(IDX,'rb').read()).hexdigest(),verified=ok,failed=bad,hits={t:v for t,v in hits.items() if v}),open('history-coverage.json','w'),indent=1)
print('verified',ok,'failed',bad,{t:len(v) for t,v in hits.items() if v})
