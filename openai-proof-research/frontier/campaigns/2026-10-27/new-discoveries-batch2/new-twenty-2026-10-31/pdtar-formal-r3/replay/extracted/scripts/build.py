import pathlib, subprocess, sys, json, time
D=pathlib.Path(__file__).resolve().parents[1]
mods=sys.argv[1:] or json.loads((D/'module-order.json').read_text())
for n in mods:
 tag=str(time.time_ns())+'-build-'+n
 rc=subprocess.run([sys.executable,'-I',str(D/'scripts/limited.py'),tag,sys.executable,'-I',str(D/'scripts/compile.py'),'-o','PDTAR/'+n+'.olean','PDTAR/'+n+'.lean'],cwd=D).returncode
 if rc: print((D/'logs'/(tag+'.log')).read_text());sys.exit(rc)
