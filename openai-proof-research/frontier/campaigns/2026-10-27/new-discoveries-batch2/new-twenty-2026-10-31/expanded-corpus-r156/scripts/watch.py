import os,subprocess,sys,time,signal,json
p=subprocess.Popen(sys.argv[1:],start_new_session=True)
peak=0; cause=None; start=time.monotonic()
while p.poll() is None:
 rss=0
 for item in os.scandir('/proc'):
  if not item.name.isdigit():continue
  try:
   stat=open(item.path+'/stat').read().split()
   if int(stat[5])==p.pid or int(item.name)==os.getpid():
    rss+=int(open(item.path+'/statm').read().split()[1])*os.sysconf('SC_PAGE_SIZE')
  except (OSError,ValueError,IndexError):pass
 peak=max(peak,rss)
 if rss>6*1024**3 or time.monotonic()-start>137:
  cause='RSS' if rss>6*1024**3 else 'wall';os.killpg(p.pid,signal.SIGKILL);break
 time.sleep(.05)
p.wait()
print(json.dumps({'command':sys.argv[1:],'returncode':p.returncode,'peak_sampled_rss':peak,'seconds':time.monotonic()-start,'killed':cause}),file=sys.stderr)
sys.exit(p.returncode if p.returncode>=0 else 128-p.returncode)
