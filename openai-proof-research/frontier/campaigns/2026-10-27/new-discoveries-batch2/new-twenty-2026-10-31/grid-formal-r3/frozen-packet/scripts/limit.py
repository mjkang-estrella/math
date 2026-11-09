import os,sys,subprocess,time,signal,resource,json
start=time.monotonic()
p=subprocess.Popen(sys.argv[1:],start_new_session=True)
peak=0
while p.poll() is None:
 rss=0
 for f in os.scandir("/proc"):
  if f.name.isdigit():
   try:
    if os.getpgid(int(f.name))==p.pid:
     st=open(f.path+"/status").read()
     for line in st.splitlines():
      if line.startswith("VmRSS:"): rss+=int(line.split()[1])
   except (OSError,ProcessLookupError): pass
 peak=max(peak,rss)
 if rss>6*1024*1024 or time.monotonic()-start>140:
  os.killpg(p.pid,signal.SIGKILL);p.wait()
  print("RESOURCE_LIMIT",file=sys.stderr);break
 time.sleep(.2)
print(json.dumps({"wall_s":round(time.monotonic()-start,3),"peak_group_rss_kib":peak,"exit":p.returncode}),file=sys.stderr)
sys.exit(p.returncode if p.returncode>=0 else 128-p.returncode)
