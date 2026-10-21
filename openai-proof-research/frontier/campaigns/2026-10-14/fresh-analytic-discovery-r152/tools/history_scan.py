from pathlib import Path
import fnmatch,json,re,hashlib
ROOT=Path.cwd()
OUT=ROOT/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r152'
p=json.loads((OUT/'private/ISOLATION-POLICY.json').read_text())
rx=re.compile(r'Boltzmann|hard[ -]sphere|Lanford|BBGKY|grand[ -]canonical|hypocoerc|Fokker[ -]Planck|Langevin',re.I)
record={'roots':p['roots'],'pruned':[],'read':[],'binary':[],'errors':[],'missing':[],'hits':[],'links':[]}
def excluded(rel):
 s=rel.lower()
 return any(fnmatch.fnmatchcase(s,g) for g in p['exclude']) or any(x in {'.git','node_modules','dependencies','__pycache__'} for x in Path(s).parts)
def walk(d):
 try: entries=sorted(d.iterdir(),key=lambda x:x.name)
 except OSError as e:record['errors'].append([str(d.relative_to(ROOT)),str(e)]);return
 for q in entries:
  rel=q.relative_to(ROOT).as_posix()
  if excluded(rel):record['pruned'].append(rel);continue
  if q.is_symlink():record['links'].append(rel);continue
  if q.is_dir():walk(q);continue
  if not q.is_file():continue
  try:
   b=q.read_bytes()
   if b'\x00' in b:record['binary'].append(rel);continue
   try:s=b.decode('utf-8')
   except UnicodeDecodeError:record['binary'].append(rel);continue
   record['read'].append({'path':rel,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
   matches=[{'line':i,'text':line} for i,line in enumerate(s.splitlines(),1) if rx.search(line)]
   if matches:record['hits'].append({'path':rel,'matches':matches})
  except OSError as e:record['errors'].append([rel,str(e)])
for s in p['roots']:
 d=ROOT/s
 if excluded(s):raise RuntimeError('root excluded')
 if not d.exists():record['missing'].append(s)
 else:walk(d)
(OUT/'private/history-search.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
print({k:len(v) for k,v in record.items()})
for hit in record['hits']:print(hit['path'],len(hit['matches']))
