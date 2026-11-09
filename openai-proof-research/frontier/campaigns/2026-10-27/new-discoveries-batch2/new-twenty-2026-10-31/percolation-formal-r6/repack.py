import pathlib,hashlib,zipfile,json,shutil
r=pathlib.Path(__file__).resolve().parent;p=r/'packet';f=r/'fresh-extracted'
old=(p/'module-order.txt').read_text().splitlines();core=[m for m in old if not m.startswith('MaskPilot') and m not in ['MaskRUP','MaskCNF','EndpointR6','AuditR6']]
base=[f'MaskPilot{i:04d}' for i in range(0,1000,100)];raw=[f'MaskRaw{i:04d}' for i in range(0,5000,100)]
mods=['MaskRUP']+base+['MaskBuild']+raw+core+['MaskCNF','EndpointR6','AuditR6']
s=(p/'src/AuditR6.lean').read_text();a=s.index('  let localModules');b=s.index('\n  let mut count',a)
s=s[:a]+'  let localModules : Array String := #['+','.join(json.dumps(x) for x in mods)+']'+s[b:]
s=''.join('import '+x+'\n' for x in raw)+s
(p/'src/AuditR6.lean').write_text(s)
(p/'module-order.txt').write_text('\n'.join(mods)+'\n')
for name in ['scan.py']:
 shutil.copyfile(r/name,p/name)
(p/'source-manifest.sha256').write_text(''.join(hashlib.sha256((p/'src'/f'{m}.lean').read_bytes()).hexdigest()+f'  src/{m}.lean\n' for m in mods))
with zipfile.ZipFile(r/'source-only.zip','w',zipfile.ZIP_DEFLATED) as z:
 for n in ['guard.sh','replay.sh','scan.py','module-order.txt','source-manifest.sha256']+[f'src/{m}.lean' for m in mods]:z.write(p/n,n)
with zipfile.ZipFile(r/'source-only.zip') as z:
 for n in z.namelist():assert not pathlib.PurePosixPath(n).is_absolute() and '..' not in pathlib.PurePosixPath(n).parts
 z.extractall(f)
 for n in z.namelist():assert(f/n).read_bytes()==z.read(n)
for q in (f/'src').glob('*.lean'):
 if q.stem not in mods:q.unlink()
print(len(mods))
