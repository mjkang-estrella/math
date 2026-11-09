from work import *
start=datetime.datetime.now(datetime.timezone.utc).isoformat()
r=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True)
dump('check-replay.json',{'start_utc':start,'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'guarded_by':'outer fixed helper_guard.py invocation; child remains in same process group'})
assert r.returncode==0
print('exact checks replay passed')
