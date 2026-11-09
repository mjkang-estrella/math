import subprocess,sys,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
for m in sys.argv[1:]:
 r=subprocess.run([sys.executable,'-I','scripts/limited.py','build-'+m+'-'+str(__import__('time').time_ns()),sys.executable,'-I','scripts/compile.py','-o','PDTAR/'+m+'.olean','PDTAR/'+m+'.lean'],cwd=D)

 if r.returncode: sys.exit(r.returncode)
