from pathlib import Path
import json,sys,hashlib,datetime
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r225')
p=R/sys.argv[1];j=json.loads(p.read_text());b=(R/j['file']).read_bytes();lines=b.splitlines(keepends=True);a,z=j['lines'];excluded=set()
for n,_,_,kind in j['mask']:
 s=lines[n-1].decode().strip()
 if kind.startswith('editorial'):raise Exception('Unresolved editorial marker '+str(n))
 if s and s.isdecimal():continue # Numeric mathematical fragments always restored prospectively.
 excluded.add(n)
print('SEMANTIC',j['file'],a,z,'numeric fragments retained; classified running headers/blank lines omitted')
o=0;spans=[]
for n,l in enumerate(lines,1):
 if a<=n<=z and n not in excluded:
  print(str(n)+': '+l.decode().rstrip('\r\n'));spans.append([o,o+len(l)])
 o+=len(l)
with (R/'semantic-reads.jsonl').open('a') as out:out.write(json.dumps({'file':j['file'],'selected_spans':spans,'parser':'bytes.splitlines(keepends=True)','sha256_file':hashlib.sha256(b).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})+'\n')
