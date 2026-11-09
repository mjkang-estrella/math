import os,subprocess,sys
p=subprocess.run(sys.argv[1:],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
s=p.stdout
print(s)
with open(f'/proc/{os.getppid()}/fd/1','w') as out:out.write(s)
sys.exit(p.returncode)
