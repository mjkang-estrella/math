from pathlib import Path
import requests,json,hashlib,datetime
R=Path(__file__).resolve().parents[1];p=R/'source-provenance.json';a=json.loads(p.read_text());entries=[e for e in a if e['key']=='327375'];assert len(entries)==2
new=entries[-1];(R/new['path']).rename(R/'sources/327375-correct.pdf');new['path']='sources/327375-correct.pdf'
old=entries[0];q=requests.get(old['url'],timeout=15);b=q.content;assert q.status_code==200 and hashlib.sha256(b).hexdigest()==old['sha256'];(R/'sources/327375-mistyped.pdf').write_bytes(b);old['path']='sources/327375-mistyped.pdf';old['excluded_reason']='Operator mistyped arXiv identifier; unrelated quantum optics paper, not evidence for record 327375';old['usable']=False
old['restored_identical_bytes_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();p.write_text(json.dumps(a,indent=2)+'\n')
