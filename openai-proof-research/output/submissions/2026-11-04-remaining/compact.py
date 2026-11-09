from pathlib import Path
import json,base64,gzip
out=Path(__file__).resolve().parent
p=out/'submission-manifest.json';d=json.loads(p.read_text());d['papers'][0].update(status='submitted',mathdb_url='https://mathdb.com/abs/2611.00023')
for r in d['papers'][1:]:
 a=Path(r['attachments'][0]);v=json.loads(a.read_text());v['encoding']='gzip+base64';v['files']={k:base64.b64encode(gzip.compress(base64.b64decode(s),mtime=0)).decode() for k,s in v['files'].items()};a.write_text(json.dumps(v))
 s=Path(r['attachments'][1]);s.write_text(s.read_text().replace('import json,base64','import json,base64,gzip').replace('write_bytes(base64.b64decode(data))','write_bytes(gzip.decompress(base64.b64decode(data)))'))
 r['comments']=r['comments'].replace('base64-encoded file contents','gzip-compressed, base64-encoded file contents')
 print(r['id'],round(a.stat().st_size/1048576,2))
p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
