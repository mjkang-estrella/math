import pathlib,json,hashlib,zipfile,re,datetime
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();r=json.loads((D/'results.json').read_text());ids=set(json.loads((D/'reservation.json').read_text())['ids']);assert len(r)==20 and set(map(int,r))==ids
for k,e in r.items():
 raw=(D/f'raw/{k}.jsonl').read_bytes();assert raw.endswith(b'\n') and sha(raw)==e['provenance']['raw_sha256'];assert sha(e['statement'].encode())==e['provenance']['statement_utf8_sha256']
 for f in e['source_files']:assert sha((D/f['file']).read_bytes())==f['sha256']
replay=json.loads((D/'outputs/replay.json').read_text());assert replay['success'];assert replay['zip_sha256']==sha((D/'338258-proof-source.zip').read_bytes())
audit=(D/'logs/fresh-audit.log').read_text();assert 'AUDITED_LOCAL_DECLARATIONS|398' in audit and 'error:' not in audit and 'sorryAx' not in audit
with zipfile.ZipFile(D/'338258-proof-source.zip') as z:
 m=json.loads(z.read('MANIFEST.json'));assert len(m)==20
 for n,h in m.items():
  b=z.read(n);assert sha(b)==h
  if n.endswith('.lean') and n!='Audit.lean':assert not re.search(rb'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',b)
# Record true retrieval times/hash receipts for search outputs, without inventing HTTP status.
for p in (D/'sources').glob('search*.json'):
 rec={'kind':'web search tool result, not a direct HTTP download','path':str(p.relative_to(D)),'sha256':sha(p.read_bytes()),'saved_at_utc':datetime.datetime.fromtimestamp(p.stat().st_mtime,datetime.timezone.utc).isoformat()};(D/'sources'/(p.name+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n')
# Complete current registry path screens; distinct from proof-body review.
patterns=['338258','riordan','oddcoordinate','oddkernel','Cheon','344906','sandpile']
scopes=[]
for p in [D/'sources/omega-D5.json',D/'sources/omega-Problems.json',D.parent/'fresh-corpus-r10/sources/registry-preprints.json']:
 o=json.loads(p.read_text());rows=o.get('tree',[]) if isinstance(o,dict) else o;paths=[t.get('path','') for t in rows if isinstance(t,dict)];scopes.append({'file':str(p),'sha256':sha(p.read_bytes()),'truncated':o.get('truncated') if isinstance(o,dict) else None,'path_count':len(paths),'hits':[t for t in paths if any(p.lower() in t.lower() for p in patterns)]})
(D/'outputs/registry-screen.json').write_text(json.dumps(scopes,indent=2)+'\n')
files={str(p.relative_to(D)):{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for p in D.rglob('*') if p.is_file() and p.name!='FILES.json'}
(D/'FILES.json').write_text(json.dumps(files,indent=2)+'\n');print({'results':len(r),'raw_lines_verified':20,'full_lean_replay':True,'audited_local_declarations':398,'files_hashed':len(files)})
