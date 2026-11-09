import pathlib,json,re,hashlib,os
p=pathlib.Path('../expanded-corpus-r91');r={}
d=json.loads((p/'results.json').read_text());r['results_entries']=d if not isinstance(d,list) else [x for x in d if str(x.get('mathdb_id',x.get('id',''))) in ('372630','372631')]
if isinstance(d,dict):
 r['results_entries']={k:v for k,v in d.items() if k in ('372630','372631')}
r['script_screen']=[]
for f in (p/'scripts').glob('*.py'):
 s=f.read_text();r['script_screen'].append({'path':str(f),'bytes':len(s),'sha256':hashlib.sha256(s.encode()).hexdigest(),'relevant_lines':[l for l in s.splitlines() if re.search('372630|372631|native_decide|ofReduceBool|sorry|admit',l)]})
r['receipts_manifest']=json.loads((p/'receipts-manifest.json').read_text());r['source_receipts']={str(f.relative_to(p)):json.loads(f.read_text()) for f in (p/'sources').glob('*.receipt.json')};r['systemd']={'pid1':pathlib.Path('/proc/1/comm').read_text().strip(),'user_bus_exists':pathlib.Path(f'/run/user/{os.getuid()}/bus').exists(),'note':'User scope verified running; early runs used direct caps, final replay uses MemoryMax=6G scope.'}
r['local_source_forbidden_tokens']={str(f):re.findall(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide|ofReduceBool)\b',f.read_text()) for f in pathlib.Path('replay/packet').glob('*.lean') if f.name in ('Eventown.lean','Audit.lean')}
pathlib.Path('outputs/input-screen.json').write_text(json.dumps(r,indent=2));print('script files',len(r['script_screen']),'systemd',r['systemd']);print('results',str(r['results_entries'])[:2500]);print(r['local_source_forbidden_tokens'])
