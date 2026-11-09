import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,subprocess,threading,time,json,hashlib,datetime,urllib.request
lane=pathlib.Path(__file__).resolve().parent
records=[]
def write(name,text):
    child=subprocess.Popen(['python3','-I','-B',str(lane/'write_lane.py'),name],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    start=time.monotonic(); peak=[0]; killed=[]; done=threading.Event()
    def guard():
        while not done.wait(.01):
            try:
                s=pathlib.Path('/proc/'+str(child.pid)+'/status').read_text()
                vals=[int(x.split()[1]) for x in s.splitlines() if x.startswith('VmRSS:')]
                peak[0]=max([peak[0]]+vals)
                if peak[0]>512*1024 or time.monotonic()-start>20: killed.append(True);child.kill();return
            except FileNotFoundError: return
    t=threading.Thread(target=guard);t.start()
    out,err=child.communicate(text);done.set();t.join()
    records.append({'path':name,'pid':child.pid,'exit':child.returncode,'wall_s':time.monotonic()-start,'sampled_RSS_KiB':peak[0],'killed':bool(killed),'reaped':True,'guard_joined':True})
    if child.returncode: raise RuntimeError(err)
def read(f):
    b=pathlib.Path(f).read_bytes();print('FILE',str(f),'SHA256',hashlib.sha256(b).hexdigest(),flush=True)
    print(b.decode(),flush=True)
    return b
