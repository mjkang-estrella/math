from pathlib import Path
import json,hashlib,shutil,zipfile
ROOT=Path(__file__).resolve().parents[3]
B=ROOT/'frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31'
OUT=Path(__file__).resolve().parent
rows=[]
for e in json.loads((B/'ledger.json').read_text())['accepted']:
 x=json.loads((B/e['acceptance']).read_text()) if 'acceptance' in e else e
 folder=OUT/str(x['mathdb_id']);folder.mkdir(exist_ok=True)
 files={}
 for k in ['paper','proof_packet']:
  p=B/x[k];h=hashlib.sha256(p.read_bytes()).hexdigest()
  expected=x.get('sha256',{}).get(k) or x.get('artifact_sha256',{}).get(x[k])
  if expected: assert h==expected,(x['mathdb_id'],k)
  dest=folder/p.name;shutil.copyfile(p,dest);files[k]=str(dest)
  files[k+'_sha256']=h
  if k=='proof_packet':
   with zipfile.ZipFile(p) as z: assert z.testzip() is None
 row={'mathdb_id':x['mathdb_id'],'title':x['title'],'authors':'Myeongjin Kang','abstract':x['scope']+'\n\nAI-assisted research preprint. The scoped main statement has a Lean certificate; internal AI review is not external journal peer review. Bounded prior-art searches do not certify worldwide priority. See the paper for qualifications and supplementary results not covered by Lean.', 'comments':'Submitted by Myeongjin Kang. Original AI-assisted research draft and source proof archive; draft preparation and internal campaign-status language in the PDF records its preparation stage. Related MathDB problem '+str(x['mathdb_id'])+'. Scope: '+x['scope'],**files,'status':'prepared','mathdb_url':None}
 rows.append(row)
(OUT/'submission-manifest.json').write_text(json.dumps({'status':'prepared','papers':rows},indent=2,ensure_ascii=False)+'\n')
print('Prepared',len(rows),'papers and proof archives; accepted hashes checked where recorded.')
