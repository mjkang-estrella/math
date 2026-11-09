import pathlib,os,json,hashlib,datetime
root=pathlib.Path('.').resolve();exclude=set();pid=os.getpid()
while pid>0 and pid not in exclude:
 exclude.add(pid)
 try:pid=int(pathlib.Path(f'/proc/{pid}/stat').read_text().split(') ',1)[1].split()[1])
 except (OSError,ValueError,IndexError):break
remaining=[]
for proc in pathlib.Path('/proc').iterdir():
 if not proc.name.isdigit() or int(proc.name) in exclude:continue
 try:
  cwd=(proc/'cwd').resolve();cmd=(proc/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
  if cwd==root or root in cwd.parents:remaining.append({'pid':int(proc.name),'cwd':str(cwd),'command':cmd})
 except OSError:pass
assert not remaining,remaining
r=json.loads(pathlib.Path('review.json').read_text());assert set(r)=={'372630','372631'}
for n in ('scoped-build','scoped-audit','scoped-checker','review-checker','packet-audit'):
 assert json.loads(pathlib.Path('logs/'+n+'.json').read_text())['returncode']==0
assert json.loads(pathlib.Path('logs/false-control.json').read_text())['returncode']!=0
assert 'COUNT|57' in pathlib.Path('logs/scoped-audit.log').read_text()
files={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(root.rglob('*')) if f.is_file() and 'handback' not in f.name}
pathlib.Path('receipts/handback.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'remaining_review_processes':remaining,'artifacts_sha256':files,'candidate_unchanged':True,'recommendation':'zero credit; root adjudication only'},indent=2));print('Verified outputs, successful strict replay/audit/checkers, expected negative failure, and no remaining review processes.')
