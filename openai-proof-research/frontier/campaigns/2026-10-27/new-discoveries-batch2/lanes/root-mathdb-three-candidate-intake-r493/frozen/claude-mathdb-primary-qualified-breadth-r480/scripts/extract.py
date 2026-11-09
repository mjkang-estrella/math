import json,sys,hashlib,os
L=sys.argv[1];out=sys.argv[2]
C=L+'/pi-mathdb-full-corpus-inventory-r301/corpus'
ids=json.load(open(L+'/root-mathdb-breadth-intake-r479/reserved-ids.json'))['ids'];S=set(ids)
recs={}
keys=None
for k in range(1,21):
    fn='mathdb-normalized-chunk-%04d.jsonl'%k
    with open(os.path.join(C,fn),'rb') as f:
        for ln,raw in enumerate(f,1):
            r=json.loads(raw)
            if keys is None: keys=sorted(r)
            i=r.get('mathdb_id', r.get('id'))
            if i in S:
                if i in recs: recs[i]['dup']=True; continue
                canon=json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':'))
                recs[i]={'chunk':'corpus/'+fn,'line':ln,'raw_line_sha256':hashlib.sha256(raw.rstrip(b'\n')).hexdigest(),
                  'canonical_record_sha256':hashlib.sha256(canon.encode()).hexdigest(),'record':r}
print('keys',keys); print('found',len(recs),'missing',sorted(S-set(recs)))
json.dump({str(i):recs[i] for i in ids if i in recs},open(out,'w'),ensure_ascii=False,indent=1)
