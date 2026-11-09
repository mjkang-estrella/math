from pathlib import Path
import json,hashlib,xml.etree.ElementTree as E,re,datetime
P=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
rows=[]
for line in (P/'freeze-new.jsonl').read_text().splitlines():
    r=json.loads(line);s=Path(r['original']);t=Path(r['copy'])
    assert sha(s)==r['sha256']==sha(t)
    if s.suffix=='.pdf':
        tx=Path(str(t)+'.txt');r.update(text=str(tx),text_sha256=sha(tx));rows.append(r)
(P/'source-map.json').write_text(json.dumps(rows,indent=2)+'\n')
ns={'a':'http://www.w3.org/2005/Atom'};chron=[]
for e in E.parse(P/'frozen/chronology.xml').findall('a:entry',ns):
    chron.append({k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated']})
for r in rows:
    text=Path(r['text']).read_text();r['body_version_banner']=next((x.strip() for x in text.splitlines() if 'arXiv:' in x),None)
(P/'chronology.json').write_text(json.dumps({'metadata':chron,'printed_banners':[{'url':r['url'],'banner':r['body_version_banner']} for r in rows],'limits':'Atom publication/update dates and printed version dates are distinct; no current GitHub registry chronology verified.'},indent=2)+'\n')
admin=json.loads((P/'administrative/ledger.json').read_text());assert (admin['accepted_count'],admin['total_accepted_count'],admin['next_global_outcome_number'])==(9,39,40)
for r in json.loads((P/'freeze.json').read_text()):assert sha(Path(r['original']))==r['sha256']==sha(Path(r['copy']))
files={str(f.relative_to(P)):sha(f) for f in sorted(P.rglob('*')) if f.is_file() and f.name not in ('manifest.json','receipt.json')}
(P/'manifest.json').write_text(json.dumps({'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'excludes':['manifest.json','receipt.json'],'files':files},indent=2)+'\n')
print(json.dumps({'files':len(files),'primary_PDFs':len(rows),'chronology_records':len(chron),'counts_unchanged':True}))
