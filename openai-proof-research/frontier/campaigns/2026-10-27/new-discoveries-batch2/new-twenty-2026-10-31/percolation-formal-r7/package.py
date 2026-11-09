import pathlib,hashlib,json,zipfile,sys,re
r=pathlib.Path(__file__).resolve().parent;p=r/'packet'
mode=sys.argv[1]
def sha(b):return hashlib.sha256(b).hexdigest()
if mode=='archive':
 files=['guard.sh','replay.sh','module-order.txt','scan.py']+['src/'+m+'.lean' for m in (p/'module-order.txt').read_text().splitlines()]
 for f in ['SUMMARY.md','PROOF.md','STATEMENT-CORRESPONDENCE.md','REPRODUCE.md','NEXT.md']:
  if (r/f).exists():(p/f).write_bytes((r/f).read_bytes());files.append(f)
 (p/'source-manifest.sha256').write_text(''.join(sha((p/f).read_bytes())+'  '+f+'\n' for f in files))
 with zipfile.ZipFile(r/'source-only.zip','w',zipfile.ZIP_DEFLATED) as z:
  for f in files+['source-manifest.sha256']:z.write(p/f,f)
 with zipfile.ZipFile(r/'r6-source.zip') as z:
  same={f:sha((p/f).read_bytes()) for f in files if f.startswith('src/') and f in z.namelist() and (p/f).read_bytes()==z.read(f)}
  changed=[f for f in files if f.startswith('src/') and f in z.namelist() and f not in same]
  assert not changed,changed
  dropped=[f for f in z.namelist() if f.startswith('src/') and f not in files]
 (r/'retained-source-comparison.json').write_text(json.dumps(same,indent=2))
 (r/'dropped-modules.json').write_text(json.dumps({'r6_experiments_omitted':dropped,'historical_list_packet':'Preserved byte-identically in inherited.zip; not rebuilt or dependencies of new mask endpoint.'},indent=2))
 print('source-only.zip',sha((r/'source-only.zip').read_bytes()),'modules',len([f for f in files if f.startswith('src/')]))
elif mode=='extract':
 dest=r/sys.argv[2];assert not dest.exists()
 with zipfile.ZipFile(r/'source-only.zip') as z:
  for f in z.namelist():
   a=pathlib.PurePosixPath(f);assert not a.is_absolute() and '..' not in a.parts
  z.extractall(dest)
 for line in (dest/'source-manifest.sha256').read_text().splitlines():
  h,f=line.split('  ',1);assert sha((dest/f).read_bytes())==h
 print('safe extraction verified',dest)
elif mode=='results':
 dest=r/sys.argv[2];rows=[]
 for m in (dest/'module-order.txt').read_text().splitlines():
  row={'module':m}
  for phase in ['build','check']:
   f=dest/'logs'/f'{phase}-{m}.log';assert f.exists(),f
   t=f.read_text();assert re.search(r'Exit status: 0\s*$',t),f
   ts=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)',t)[1].split(':')
   secs=0
   for x in ts:secs=secs*60+float(x)
   row[phase+'_seconds']=secs
   row[phase+'_peak_rss_kib']=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',t)[1])
  assert (dest/'logs'/f'{m}.ok').exists()
  rows.append(row)
 (r/'module-times.json').write_text(json.dumps(rows,indent=2))
 print('modules',len(rows),'compile',sum(x['build_seconds'] for x in rows),'check',sum(x['check_seconds'] for x in rows))
