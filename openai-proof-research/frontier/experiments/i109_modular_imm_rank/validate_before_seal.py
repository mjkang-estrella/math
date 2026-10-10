"""Preparation runner: captures validation and retains failures before the seal."""
import pathlib,subprocess,json,time
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i109_modular_imm_rank'
assert not (S/'seal.json').exists()
events=json.loads((S/'preseal-events.json').read_text()) if (S/'preseal-events.json').exists() else []
start=time.monotonic();r=subprocess.run(['python','-B','frontier/experiments/i109_modular_imm_rank/verify.py','--preseal'],cwd=R,capture_output=True,text=True)
record={'command':['python','-B','frontier/experiments/i109_modular_imm_rank/verify.py','--preseal'],'exit_code':r.returncode,'elapsed_seconds':time.monotonic()-start,'stdout':r.stdout,'stderr':r.stderr}
name='preseal-replay-'+str(len(events)+1)+'.json';(S/name).write_text(json.dumps(record,indent=2)+'\n')
events.append({'record':name,'exit_code':r.returncode,'status':'PASS' if r.returncode==0 else 'FAIL'});(S/'preseal-events.json').write_text(json.dumps(events,indent=2)+'\n')
print(json.dumps({'record':name,'exit_code':r.returncode,'elapsed_seconds':record['elapsed_seconds'],'stdout':r.stdout[:1000],'stderr':r.stderr},indent=2));raise SystemExit(r.returncode)
