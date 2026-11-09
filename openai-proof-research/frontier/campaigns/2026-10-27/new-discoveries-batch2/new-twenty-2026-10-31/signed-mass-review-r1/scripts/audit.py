exec((__import__('pathlib').Path(__file__).parent/'replay.py').read_text().split('res={}')[0])
cmd=[L+'lean','-j1','-DwarningAsError=true','IndependentAudit.lean']
r=subprocess.run(['timeout','140','python',str(D/'scripts/limited.py')]+cmd,cwd=E,env=env,capture_output=True,text=True)
(D/'logs/audit.log').write_text(r.stdout+r.stderr)
print(r.returncode,r.stdout[-1500:],r.stderr)
