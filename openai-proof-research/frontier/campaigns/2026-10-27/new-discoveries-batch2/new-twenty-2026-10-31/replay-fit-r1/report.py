from pathlib import Path
import json,re,hashlib,zipfile
L=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
rows=[];pres={}
for cid,endpoint,mod in [('330264','conjecture_false','Endpoint'),('324342','conjecture5_false','ConferenceMDS324342')]:
 files={}
 for p in sorted((L/f'original-{cid}').glob('*.lean')):
  b=p.read_bytes();q=L/f'build-{cid}'/p.name
  files[p.name]={'original_sha256':h(b),'build_sha256':h(q.read_bytes()) if q.exists() else None,'byte_identical':q.exists() and b==q.read_bytes(),'definitions':re.findall(r'(?m)^\s*(?:noncomputable )?def\s+(\w+)',b.decode())}
 s=(L/f'original-{cid}'/f'{mod}.lean').read_text()
 stmt=re.search(r'(?m)^\s*theorem '+endpoint+r'\s*:[\s\S]*?(?=:=)',s)[0]
 pres[cid]={'files':files,'endpoint_statement_text':stmt,'endpoint_statement_sha256':h(stmt.encode()),'moved_or_split_proofs':[],'note':'No replacement packet proposed; original candidate modules remain byte-identical.'}
 for p in sorted((L/'logs').glob(f'{cid}-*.log')):
  s=p.read_text()
  m=re.search(r'GUARD peak_kib=(\d+) elapsed=(\d+) status=(\d+) reason=(\w*)',s)
  if m:rows.append([p.name,*m.groups()])
(L/'statement-preservation.json').write_text(json.dumps(pres,indent=2)+'\n')
(L/'timings.tsv').write_text('log\tpeak_RSS_KiB\twall_seconds\twait_status\tlimit_reason\n'+''.join('\t'.join(x)+'\n' for x in rows))
with zipfile.ZipFile(L/'unchanged-frozen-sources.zip','w',zipfile.ZIP_DEFLATED) as z:
 for cid in ['330264','324342']:
  for p in sorted((L/f'original-{cid}').glob('*.lean')):z.writestr(cid+'/'+p.name,p.read_bytes())
print(json.dumps({'modules_preserved':{k:all(x['byte_identical'] for x in v['files'].values()) for k,v in pres.items()},'timings':rows},indent=2))
