from pathlib import Path
import json,hashlib,subprocess,sys,re
r=Path(__file__).resolve().parents[1]
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for attempt in range(40):
 state=json.loads((r/'development-state.json').read_text())
 if state['status']=='PASS_DEVELOPMENT':break
 failed=sorted(p for p in (r/'logs').glob('*-build-*.log.json') if json.loads(p.read_text())['exit']!=0)
 if failed:
  rec=failed[-1];log=rec.with_suffix('');text=log.read_text();m=log.name.split('-build-',1)[1][:-4]
  if re.fullmatch(r'FiniteSupport\d+',m) and 'maximum recursion depth' in text and 'build:'+m not in state['done']:
   p=r/'formal'/(m+'.lean');s=p.read_text();old=int(re.search(r'maxRecDepth (\d+)',s)[1]);assert old<65536
   before=h(p);p.write_text(s.replace(f'maxRecDepth {old}',f'maxRecDepth {old*2}'));after=h(p)
   fixes=json.loads((r/'source-fixes.json').read_text());fixes.append({'module':m,'reason':'Observed strict Lean recursion-depth failure','change':f'Only maxRecDepth {old} → {old*2}; proof and statement unchanged.','before_sha256':before,'after_sha256':after,'failure_receipt':str(rec.relative_to(r))})
   (r/'source-fixes.json').write_text(json.dumps(fixes,indent=2)+'\n')
   mf=r/'source-manifest.json';manifest=json.loads(mf.read_text());manifest['formal/'+m+'.lean']=after;mf.write_text(json.dumps(manifest,indent=2)+'\n')
   state.setdefault('source_migrations',[]).append({'before':state['sources'],'after':h(mf),'module':m,'reason':'Authorized compile-failure option fix'})
   state['sources']=h(mf);(r/'development-state.json').write_text(json.dumps(state,indent=2)+'\n');print('RECORDED OPTION FIX',m,old,old*2,flush=True)
 rc=subprocess.run([sys.executable,'-I',str(r/'replay.py'),'--development','--resume','--steps','2048'],cwd=r).returncode
 if rc==0:break
 failures=sorted(p for p in (r/'logs').glob('*-build-*.log.json') if json.loads(p.read_text())['exit']!=0)
 last=failures[-1].with_suffix('') if failures else None
 if last is None or not re.fullmatch(r'FiniteSupport\d+',last.name.split('-build-',1)[1][:-4]) or 'maximum recursion depth' not in last.read_text():raise SystemExit('Non-option failure; inspect manually, no automatic retry')
else:raise SystemExit('Fix attempt bound reached')
