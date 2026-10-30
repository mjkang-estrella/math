import pathlib,sys,json,hashlib
L=pathlib.Path(__file__).parent;p=L/'copies/sources'/sys.argv[1];t=p.read_text();parts=t.split('\f');rows=[]
for i in map(int,sys.argv[2:]):
 start=sum(len(x)+1 for x in parts[:i]);rows.append({'page_index':i,'char_start':start,'char_end':start+len(parts[i])});print('PAGE',i,parts[i])
with (L/'extra-body-coverage.jsonl').open('a') as f:f.write(json.dumps({'file':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'ranges':rows})+'\n')
