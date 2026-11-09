import subprocess, pathlib,resource,signal
L=pathlib.Path(__file__).resolve().parent
broker=subprocess.Popen(['/bin/bash'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
import shlex,sys
for m in [f'PackedFull{k}' for k in range(8)]+['PackedFull']:
 cmd=' '.join(shlex.quote(x) for x in [sys.executable,str(L/'run.py'),'-o',m+'.olean',m+'.lean'])
 broker.stdin.write('cd '+shlex.quote(str(L/'dev'))+'\n'+cmd+' > '+shlex.quote(str(L/(m+'-attempt01.log')))+' 2>&1\nprintf "%s\\n" "$?"\n');broker.stdin.flush()
 rc=int(broker.stdout.readline().strip());print(m,rc,flush=True)
 if rc:print((L/(m+'-attempt01.log')).read_text());break
broker.stdin.write('exit\n');broker.stdin.flush();broker.wait()
