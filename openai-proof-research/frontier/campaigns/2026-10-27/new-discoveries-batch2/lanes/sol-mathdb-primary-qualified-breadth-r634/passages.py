from pathlib import Path
import json,re,hashlib
O=Path(__file__).resolve().parent;S=O.parent/'sol-mathdb-primary-qualified-breadth-r418/primary';t=(S/'ohtsuki.txt').read_text().splitlines();out=[]
for x in json.loads((O/'literal-records.json').read_text()):
 r=x['record']
 if 'Ohtsuki' not in r['source_name']:continue
 label=r['title'].split(' —')[0];a=[i for i,l in enumerate(t) if l.startswith(label+' ') or l.startswith(label+'(')]
 if not a:print('MISSING',r['mathdb_id'],label);continue
 i=a[0];text='\n'.join(t[max(0,i-3):i+15]);out.append({'mathdb_id':r['mathdb_id'],'path':str(S/'ohtsuki.txt'),'line_start':max(0,i-3)+1,'line_end':i+15,'label':label,'text':text})
(O/'selected-passages.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');b=(O/'selected-passages.json').read_bytes();(O/'passage-bindings.json').write_text(json.dumps({'path':'selected-passages.json','sha256':hashlib.sha256(b).hexdigest(),'size':len(b)},indent=2)+'\n')
for a in out:print(a['mathdb_id'],a['line_start'],a['text'])
