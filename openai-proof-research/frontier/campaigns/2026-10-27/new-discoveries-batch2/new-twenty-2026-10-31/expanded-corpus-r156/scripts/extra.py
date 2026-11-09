import urllib.request,pathlib,json,datetime,hashlib
p=pathlib.Path.cwd();jobs=[]
for row in json.loads((p/'reservation.json').read_text())['rows']:
 if 'arxiv' in row['source_url']:jobs.append((str(row['mathdb_id'])+'-abs',row['source_url']))
jobs += [('companion-2023','https://math.wvu.edu/~hlai2/Pdf/Hong-Jian_Lai_Pdf/318_DM_2023.pdf'),('openai-head','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'),('dong-publications','https://math.nie.edu.sg/fmdong/Research/Publications-Dong.htm'),('matroids-new','https://arxiv.org/html/2409.13834')]
log=[]
for key,u in jobs:
 try:
  with urllib.request.urlopen(u,timeout=12) as f:b=f.read();status=f.status
  ext='pdf' if b.startswith(b'%PDF') else 'html';(p/'sources'/f'{key}.{ext}').write_bytes(b)
  r={'key':key,'url':u,'status':status,'sha256':hashlib.sha256(b).hexdigest()}
 except Exception as e:r={'key':key,'url':u,'error':str(e)}
 r['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();log.append(r);print(r,flush=True)
 (p/'outputs/extra-receipts.json').write_text(json.dumps(log,indent=2))
