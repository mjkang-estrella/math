exec(open(__file__.replace('read.py','bind.py')).read().split('refs={}')[0])
ids=set(j(I/'reserved-ids-r716.json')['ids']);out=[]
for e in j(C/'manifest.json')['files']:
 if not e['path'].startswith('corpus/'):continue
 for n,line in enumerate((C/e['path']).open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:out.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':e['path'],'corpus_line':n,'record':r})
assert len(out)==50
write('literal-records.json',out)
import sys
start=int(sys.argv[1]);end=int(sys.argv[2])
for d in sorted(out,key=lambda d:d['mathdb_id'])[start:end]:print(json.dumps(d,ensure_ascii=False))
