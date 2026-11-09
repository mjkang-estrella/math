import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,pathlib,re,html,time,json
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));import review_ops as r
s=r.read(r.LANE/'live/wu-journal.html').decode();s=re.sub(r'<(script|style)\b[^>]*>.*?</\1>','',s,flags=re.S);s=html.unescape(re.sub('<[^>]*>',' ',s));s=re.sub(r'\s+',' ',s)
print(json.dumps(r.write('live/wu-journal-plain.txt',s)))
for term in ['Conjecture 1.22','Lemma 2.5','Lemma 2.6','Lemma 2.7','Lemma 3.7','Lemma 4.3','Lemma 4.6','Corollary 4.7','without vertices','Published','Correction','Cited by']:
 print('\nTERM',term)
 for m in list(re.finditer(re.escape(term),s,re.I))[:5]:print(s[max(0,m.start()-100):m.start()+2300])
r.finish('journal-'+str(time.time_ns()))
