from pathlib import Path
import json,re,hashlib
L=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
rows=[]
for p in sorted((L/'logs').glob('*.log')):
 s=p.read_text();m=re.search(r'GUARD peak_kib=(\d+) elapsed=(\d+) status=(\d+) reason=(\w*)',s)
 if m:rows.append([p.name,*m.groups()])
(L/'timings.tsv').write_text('log\tpeak_RSS_KiB\twall_seconds\twait_status\tlimit_reason\n'+''.join('\t'.join(x)+'\n' for x in rows))
r={}
for cid in ['330264','324342']:
 files={}
 for p in sorted((L/f'original-{cid}').glob('*.lean')):
  q=(L/'fresh-324342'/p.name) if cid=='324342' else p
  b=p.read_bytes();c=q.read_bytes()
  files[p.name]={'old_sha256':h(b),'new_sha256':h(c),'byte_identical':b==c}
  if p.name=='ConferenceMDS324342.lean':
   b0=b[b.index(b'\n\n'):];c0=c[c.index(b'\n\n'):]
   assert b0==c0
   files[p.name]['whole_body_after_imports_sha256_old']=h(b0)
   files[p.name]['whole_body_after_imports_sha256_new']=h(c0)
   files[p.name]['exception']='Only endpoint-module imports changed; ALL definition, statement and proof bytes are identical.'
 endpoint='conjecture_false' if cid=='330264' else 'conjecture5_false'
 mod='Endpoint' if cid=='330264' else 'ConferenceMDS324342'
 s=(L/f'original-{cid}'/f'{mod}.lean').read_text()
 stmt=re.search(r'(?m)^\s*theorem '+endpoint+r'\s*:[\s\S]*?(?=:=)',s)[0]
 r[cid]={'files':files,'endpoint_statement_text':stmt,'endpoint_statement_sha256':h(stmt.encode()),'moved_or_split_proofs':[]}
 if cid=='324342':
  for p in (L/'fresh-324342').glob('*.lean'):
   if p.name not in files:files[p.name]={'new_sha256':h(p.read_bytes()),'new_file':True}
(L/'statement-preservation.json').write_text(json.dumps(r,indent=2)+'\n')
for cid in ['330264','324342']:
 logs=[x for x in rows if x[0].startswith('final324342-' if cid=='324342' else '330264-') and 'buffered' not in x[0]]
 out=['| Log | Wall seconds | Peak RSS KiB | Status | Watchdog reason |','|---|---:|---:|---:|---|']
 out+=['| '+ ' | '.join([x[0],x[2],x[1],x[3],x[4] or 'none recorded'])+' |' for x in logs]
 (L/f'{cid}-timings.md').write_text('\n'.join(out)+'\n')
