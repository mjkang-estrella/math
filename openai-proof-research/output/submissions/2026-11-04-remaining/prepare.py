from pathlib import Path
import json,hashlib,zipfile,tarfile,shutil
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[2]
B=ROOT/'frontier/campaigns/2026-10-27/new-discoveries-batch2'
C=B/'new-twenty-2026-10-31'
rows=[]
entries=[(B,e) for e in json.loads((B/'ledger.json').read_text())['accepted']]
entries += [(C,json.loads((C/(e.get('acceptance') or e['file'])).read_text())) for e in json.loads((C/'ledger.json').read_text())['accepted'][22:]]
for base,e in entries:
 ident=str(e.get('mathdb_id') or 'D'+str(e['number']))
 dest=OUT/ident;dest.mkdir(exist_ok=True)
 row={'id':ident,'title':e['title'],'authors':'Myeongjin Kang','scope':e['scope'],'status':'prepared'}
 for key,src,expected in [('paper',e['paper'],e.get('paper_sha256') or e.get('sha256',{}).get('paper')),('proof_packet',e.get('packet') or e['proof_packet'],e.get('packet_sha256') or e.get('sha256',{}).get('proof_packet'))]:
  src=base/src.split(' (identical')[0]; data=src.read_bytes();h=hashlib.sha256(data).hexdigest();assert h==expected,(ident,key,h,expected)
  out=dest/src.name;shutil.copyfile(src,out);row[key]=str(out);row[key+'_sha256']=h
 archive=Path(row['proof_packet']);files={}
 if zipfile.is_zipfile(archive):
  with zipfile.ZipFile(archive) as z:
   assert z.testzip() is None
   for f in z.infolist():
    if not f.is_dir(): files[f.filename]=z.read(f)
 else:
  with tarfile.open(archive) as z:
   for f in z.getmembers():
    if f.isfile(): files[f.name]=z.extractfile(f).read()
 # Accepted source archives are published as supported JSON attachments, preserving every byte.
 import base64
 package={'original_archive_name':archive.name,'original_archive_sha256':row['proof_packet_sha256'],'files':{name:base64.b64encode(data).decode() for name,data in files.items()},'encoding':'base64'}
 attachment=dest/'proof-sources.json';attachment.write_text(json.dumps(package))
 extract=dest/'extract_sources.py';extract.write_text('''import json,base64\nfrom pathlib import Path\np=Path(__file__).with_name("proof-sources.json")\nout=Path("extracted-proof-sources");out.mkdir(exist_ok=False)\nfor name,data in json.loads(p.read_text())["files"].items():\n q=Path(name)\n assert not q.is_absolute() and ".." not in q.parts\n target=out/q;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(base64.b64decode(data))\nprint(out.resolve())\n''')
 row['attachments']=[str(attachment),str(extract)]
 row['abstract']=e['scope']+'\n\nAI-assisted research preprint. The scoped main statement has a Lean certificate. Internal AI review is not external journal peer review; bounded prior-art searches do not certify worldwide priority. See the paper for exact qualifications and formalization limits.'
 row['comments']='Submitted by Myeongjin Kang. '+('Related MathDB problem '+ident+'. ' if ident.isdigit() else '')+'Proof sources are attached as proof-sources.json (base64-encoded file contents); extract_sources.py reconstructs all archived files. Original archive SHA-256: '+row['proof_packet_sha256']+'.'
 rows.append(row)
 print(ident,round(attachment.stat().st_size/1048576,2),'MB',row['title'])
(OUT/'submission-manifest.json').write_text(json.dumps({'status':'prepared','papers':rows},indent=2,ensure_ascii=False)+'\n')
