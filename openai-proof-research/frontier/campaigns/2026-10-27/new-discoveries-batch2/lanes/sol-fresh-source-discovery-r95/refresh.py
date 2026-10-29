from pathlib import Path
import urllib.request,json,re,datetime,subprocess
P=Path(__file__).parent; S=P/'sources'; log=[]
def fetch(name,url):
 try:
  with urllib.request.urlopen(url,timeout=35) as r:b=r.read(16000000)
  (S/name).write_bytes(b);log.append({'file':name,'url':url,'bytes':len(b)});return b
 except Exception as e:log.append({'url':url,'error':str(e)});return None
for id in ['2605.05243','2608.06470']:
 fetch(id+'-abs.html','https://arxiv.org/abs/'+id)
 b=fetch(id+'.pdf','https://arxiv.org/pdf/'+id)
 if b:subprocess.run(['pdftotext','-layout',str(S/(id+'.pdf')),str(S/(id+'.pdf.txt'))],check=True)
base=P.parent/'root-edge-irregulator-final-freeze-r1'; results={}
pat=re.compile(r'tokmachev|tarasov|zaporozhets|gini|boundary.*(chord|distance)|(chord|distance).*boundary|santalo|holevo|utkin',re.I)
for repo,key in [('the-omega-institute/trureturing','the-omega-institute'),('openai/math','openai')]:
 h=json.loads((S/(key+'-HEAD.json')).read_text()); head=h['sha'];short='omega' if key!='openai' else key
 matches=[]
 for line in (base/(short+'-tree.txt')).open():
  if pat.search(line):matches.append(line.rstrip().split('\t')[-1])
 results[short]={'head':head,'commit_date':h['commit']['committer']['date'],'baseline_matches':matches,'baseline':str(base/(short+'-tree.txt'))}
 for j,path in enumerate(matches):
  if path.endswith(('.md','.tex')) and (path.startswith(('Problems/','Blueprint/','preprints/'))):fetch(short+'-body-'+str(j)+'.txt','https://raw.githubusercontent.com/'+repo+'/'+head+'/'+path)
 old='d2b0ee6e958cf646530d3476088494e349570b46' if short=='omega' else '7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a'
 if old!=head:
  b=fetch(short+'-compare.json','https://api.github.com/repos/'+repo+'/compare/'+old+'...'+head)
  if b:
   c=json.loads(b);results[short]['comparison']={k:c.get(k) for k in ['total_commits','ahead_by','status']};results[short]['changed_files_returned']=len(c.get('files',[]))
 results[short]['coverage']='Baseline lexical matches and capped HTTP compare only; no full current inventory or semantic clearance.'
(P/'registry.json').write_text(json.dumps(results,indent=2));(P/'refresh-log.json').write_text(json.dumps(log,indent=2));print(json.dumps(results,indent=2));print(json.dumps(log,indent=2))
