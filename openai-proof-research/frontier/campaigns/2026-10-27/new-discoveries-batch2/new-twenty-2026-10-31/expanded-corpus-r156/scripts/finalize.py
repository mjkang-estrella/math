import pathlib,re,json,hashlib,os
p=pathlib.Path.cwd();f=p/'SUMMARY.md';s=f.read_text()
for a,b in [('All4','All 4'),('all15','all 15'),('all21','all 21'),('all19','all 19'),('all6','all 6'),('all3','all 3'),('tested7','tested 7'),('tested967','tested 967'),('Both20','Both 20'),('through150','through 150'),('order10','order 10'),('order12','order 12'),('order6','order 6'),('order24','order 24'),('orders4','orders 4'),('and5','and 5'),('of18','of 18'),('for11','for 11'),('among46','among 46'),('sizes4','sizes 4'),('side sizes4','side sizes 4'),('had13','had 13'),('and1,717','and 1,717'),('size<=4','size <= 4'),('through order15','through order 15'),('its110','its 110'),('its137','its 137'),('over6GiB','over 6 GiB'),('every50ms','every 50 ms'),('CPU120','CPU 120'),('wall140','wall 140'),('zero or one','zero or one'),('k28','k = 28'),('at k=28','at k = 28'),('gives3,689','gives 3,689'),('exceeding3,347','exceeding 3,347'),(' at r=5',' at r = 5'),('modulo9','modulo 9'),('six-neighbour','six-neighbour'),('first-neighbour','first-neighbour'),('triangle-free cubic order10','triangle-free cubic order 10')]:s=s.replace(a,b)
f.write_text(s)
# Verify durable data again; exclude the still-being-written audit logs from manifest.
r=json.loads((p/'results.json').read_text());v=json.loads((p/'reservation.json').read_text());assert len(r)==20 and set(r)==set(map(str,v['ids']))
for k,x in r.items():
 b=(p/x['raw_file']).read_bytes();assert b.endswith(b'\n') and hashlib.sha256(b).hexdigest()==x['provenance']['raw_sha256']
 assert hashlib.sha256(x['literal_statement'].encode()).hexdigest()==x['statement_sha256']
manifest={str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in p.rglob('*') if f.is_file() and f.name!='manifest.json' and not str(f.relative_to(p)).startswith(('logs/audit','logs/finalize'))}
(p/'outputs/manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
active=[]
for d in pathlib.Path('/proc').iterdir():
 if not d.name.isdigit():continue
 try:
  b=(d/'cmdline').read_bytes().split(b'\0')
  if len(b)>1 and (b[0].endswith(b'python3') or b[0].endswith(b'lean')) and any(str(p).encode() in a for a in b):
   if int(d.name) not in [os.getpid(),os.getppid()]:active.append(int(d.name))
 except OSError:pass
print(json.dumps({'result_entries':len(r),'raw_and_statement_hash_checks':'PASS','manifest_files':len(manifest),'other_lane_python_or_lean_processes':active}))
