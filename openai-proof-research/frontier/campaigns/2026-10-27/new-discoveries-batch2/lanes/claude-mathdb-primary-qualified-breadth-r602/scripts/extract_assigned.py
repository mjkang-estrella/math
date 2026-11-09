# Locate the 50 r601-reserved records for Claude r602 in the 20 r301 chunks (read in place); emit exact record + hashes.
import hashlib,json,os,sys
B=os.path.realpath(sys.argv[1]); out=sys.argv[2]
I=os.path.join(B,'lanes/root-mathdb-breadth-intake-r601'); P=os.path.join(B,'lanes/pi-mathdb-full-corpus-inventory-r301')
ids=json.load(open(os.path.join(I,'reserved-ids.json'),encoding='utf-8'))['ids']; S=set(ids)
m=json.load(open(os.path.join(P,'manifest.json'),encoding='utf-8'))
chunks=sorted(e['path'] for e in m['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-'))
found={}
for c in chunks:
    with open(os.path.join(P,c),'rb') as f:
        for ln,raw in enumerate(f,1):
            r=json.loads(raw.decode('utf-8'))
            if r.get('mathdb_id') in S:
                if r['mathdb_id'] in found: print('DUP',r['mathdb_id']); sys.exit(1)
                can=json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8')
                st=r.get('statement') or ''
                found[r['mathdb_id']]={'mathdb_id':r['mathdb_id'],'chunk':c,'line':ln,'line_sha256':hashlib.sha256(raw.rstrip(b'\n')).hexdigest(),
                  'canonical_record_sha256':hashlib.sha256(can).hexdigest(),'statement_utf8_sha256':hashlib.sha256(st.encode('utf-8')).hexdigest(),
                  'statement_chars':len(st),'record':r}
miss=[i for i in ids if i not in found]
json.dump([found[i] for i in ids if i in found],open(out,'w',encoding='utf-8'),ensure_ascii=False,indent=1)
print(json.dumps({'found':len(found),'missing':miss,'keys':sorted({k for v in found.values() for k in v['record']})}))
sys.exit(1 if miss else 0)
