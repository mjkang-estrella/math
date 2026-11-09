import pathlib,json,hashlib,datetime,xml.etree.ElementTree as E
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(name,d):(L/name).write_text(json.dumps(d,indent=2))
ns={'a':'http://www.w3.org/2005/Atom'}
chron=[]
for name in ['chronology-api.xml','latest1702-api.xml']:
 for e in E.parse(L/'retrieval'/name).findall('a:entry',ns):
  chron.append({'id':e.findtext('a:id','',ns),'title':e.findtext('a:title','',ns),'authors':[a.findtext('a:name','',ns) for a in e.findall('a:author',ns)],'published':e.findtext('a:published','',ns),'updated':e.findtext('a:updated','',ns)})
put('chronology.json',chron)
sources=[]
for p in (L/'retrieval').glob('*.receipt.json'):
 row=json.loads(p.read_text());target=p.with_name(p.name.removesuffix('.receipt.json'))
 if 'sha256' in row:assert sha(target)==row['sha256']
 sources.append(row)
for p in (L/'retrieval').glob('*.freeze.json'):
 row=json.loads(p.read_text());pdf=p.with_suffix('.pdf');txt=p.with_suffix('.txt')
 # filenames end in .freeze.json, so remove both suffixes
 stem=p.name.removesuffix('.freeze.json');pdf=p.with_name(stem+'.pdf');txt=p.with_name(stem+'.txt')
 assert sha(pdf)==row['pdf_sha256'] and sha(txt)==row['text_sha256']
for row in json.loads((L/'freeze.json').read_text()):assert sha(pathlib.Path(row['original']))==sha(pathlib.Path(row['copy']))==row['sha256']
put('source-receipts.json',sources)
put('provenance.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':str(L),'source_receipts':'source-receipts.json','chronology':'chronology.json','frozen_originals':'freeze.json','history_inventory':'history-bindings.json','history_scope':'14268 distinct textual bodies <=4MB in traversed batch and sources; administrative entries are observed snapshots, not immutable scientific inputs','source_after_read_verification':True,'resources':{'AS_bytes':512*1024*1024,'group_RSS_bytes':512*1024*1024,'CPU_seconds':210,'wall_seconds':230,'cap_raises':False},'counts':{'additional':9,'total':39,'next':40,'modified':False},'status':'ordinary proof candidate, independent review and priority HOLD','children':0,'external_mutations':False,'third_fresh_survivor_obtained':False,'breadth_additional_families':8})
rows=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']:rows.append({'path':str(p.relative_to(L)),'sha256':sha(p),'bytes':p.stat().st_size})
put('manifest.json',rows)
print('manifest entries',len(rows))
