import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,re,sys
L=pathlib.Path(__file__).resolve().parent
for name,term in json.loads(sys.argv[1]):
 t=(L/'sources'/name).read_text();matches=list(re.finditer(term,t,re.I));print('\nFILE',name,'TOTALCHARS',len(t),'MATCHES',len(matches))
 for m in matches[:4]:print('OFFSET',m.start(),t[max(0,m.start()-350):m.start()+2400])
