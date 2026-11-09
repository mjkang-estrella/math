import subprocess
for exe,args in [('groff',['--version']),('ps2pdf',['-h'])]:
 r=subprocess.run([exe]+args,capture_output=True,text=True);print(exe,r.stdout[:500],r.stderr[:500])
