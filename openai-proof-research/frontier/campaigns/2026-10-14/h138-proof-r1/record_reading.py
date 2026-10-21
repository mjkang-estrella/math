from pathlib import Path
import json,hashlib,gzip,tarfile,io
R=Path(__file__).resolve().parent;I=R/'private/incoming';P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');A=P/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r138'
sha=lambda b:hashlib.sha256(b).hexdigest()
sources=[]
full26={'introduction.tex','crossings.tex','angular-program.tex','geometry.tex','transfer.tex','matching.tex','growth.tex','bibliography.tex'}
full25={'introduction.tex','counting.tex','finite-selection.tex','transmission.tex'}
for x in json.loads((I/'source-ledger.json').read_text()):
 n=x['canonical_path'];b=(I/x['local_path']).read_bytes();full=Path(n).name in (full26 if 'September-26' in n else full25)
 sources.append({'canonical_pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','canonical_path':n,'pinned_url':x['url'],'size':len(b),'git_blob_sha1':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),'sha256':sha(b),'copy':'private/incoming/'+x['local_path'],'read_ranges':[[1,len(b.splitlines())]] if full else [],'reading':'full operative section' if full else 'acquired/authenticated, not credited as proof reading'})
(R/'source-reading.json').write_text(json.dumps(sources,indent=2)+'\n')
ranges={'2109.07534v1':[[275,355],[753,1057]],'1601.02066v1':[[317,347],[418,595]],'1108.3244v3':[[95,357]],'2312.16939v4':[[205,290],[347,624],[1002,1038],[1233,1336]]}
prim=[]
for x in json.loads((I/'primary-ledger.json').read_text()):
 raw=(I/x['local_path']).read_bytes();dec=gzip.decompress(raw);extracts=[]
 try:
  with tarfile.open(fileobj=io.BytesIO(dec),mode='r:') as t:
   files={m.name:t.extractfile(m).read() for m in t.getmembers() if m.isfile() and any(Path(m.name).name==Path(e['path']).name for e in x['extracts'])}
 except tarfile.ReadError:files={'main.tex':dec}
 for e in x['extracts']:
  b=(I/e['path']).read_bytes();name=e['path'].split(x['id']+'/',1)[1];matches=[v for k,v in files.items() if Path(k).name==Path(name).name];assert matches and matches[0]==b,(x['id'],name)
  extracts.append({'path':'private/incoming/'+e['path'],'size':len(b),'sha256':sha(b),'raw_archive_extract_match':True,'archive_member_match':'unique requested basename and exact bytes (GK incoming text/ is a local wrapper)' ,'read_ranges':ranges[x['id']] if name.endswith('main.tex') else []})
 prim.append({'version':x['id'],'versioned_original_url':x['url'],'raw_size':len(raw),'raw_sha256':sha(raw),'fresh_network_acquisition':False,'basis':'exact retained incoming raw version and independently checked decompression/extract equality; no latest-version inference','extracts':extracts,'access_failures':[]})
(R/'primary-reading.json').write_text(json.dumps(prim,indent=2)+'\n')
# Direct mandatory originals only; keep metadata and explicit read slices where appropriate.
orig=[]
for n in ['assessment.md','intake.json','replay.json']:
 p=P/'frontier/campaigns/2026-10-14/discovery-analytic-r138-parent'/n;b=p.read_bytes();out=R/'private/intake'/n;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(b);orig.append({'origin':str(p),'copy':str(out.relative_to(R)),'size':len(b),'sha256':sha(b),'read_extent':'full intake/limits, no gate authority','snapshot_timing':'late current selected-original snapshot'})
for n,aa,bb in [('iteration133-fixed-metric-harmonic-growth-task.json',236,375),('iteration136-birational-positivity-discovery-task.json',381,481)]:
 p=P/'frontier/iterations'/n;b=p.read_bytes();obj=json.loads(b);s='\n'.join(obj['brief'].splitlines()[aa-1:bb]);out=R/'private/decoded'/(n+'.selected.txt');out.parent.mkdir(parents=True,exist_ok=True);out.write_text(s+'\n');orig.append({'origin':str(p),'original_size':len(b),'original_sha256':sha(b),'decoded_field':'brief','read_lines_in_decoded_field':[aa,bb],'selected_copy':str(out.relative_to(R)),'selected_sha256':sha((s+'\n').encode()),'whole_task_read':False})
for n,extent in [('frontier/iterations/i130-spectral-harmonic-discovery.md','98–201: selected H and complete H1/H2 operations/conclusion; preceding unrelated screens not full-read'),('frontier/iterations/i133-fixed-metric-harmonic-growth.md','1–342 full'),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r33/report.md','1–29 full'),('AGENTS.md','full'),('sources/upstream.json','full'),('frontier/NEW-TEN-2026-10-14.md','1–95 administrative acceptance rules, mutable journal'),('sources/CONTENTS.md','1–28 catalogue opening only')]:
 p=P/n;b=p.read_bytes();orig.append({'origin':str(p),'size':len(b),'sha256':sha(b),'git_blob_sha1_of_current_bytes':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(),'read_extent':extent,'snapshot_timing':'current observation only'})
(R/'original-reading.json').write_text(json.dumps(orig,indent=2)+'\n')
obs=[]
for x in json.loads((R/'incoming-membership.json').read_text())['members']:
 p=Path(x['origin']);b=p.read_bytes();assert sha(b)==x['sha256'],str(p);obs.append({'origin':str(p),'sha256':sha(b),'matches_intake_selected_bytes':True})
(R/'private/selected-originals-unchanged.json').write_text(json.dumps({'selected_checks':obs,'scope':'selected incoming/current original bytes between intake snapshot and this late observation; no whole-parent, historical, first-read or OS preservation claim'},indent=2)+'\n')
print('Recorded',len(sources),'source bindings,',len(prim),'primary versions with raw/extract checks,',len(orig),'original contexts;',len(obs),'selected originals unchanged')
