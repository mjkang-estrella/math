from research import *
db=sqlite3.connect(HERE/'screen.sqlite');pats=[re.compile(x,re.I) for x in [r'2505[. /_-]04144',r'independent.{0,15}mutual.{0,15}visibility.{0,15}colou?ring',r'01280.y',r'Peterin.{0,100}Samadi',r'Bre.ar.{0,100}Peterin']]
n=hits=0;excluded=[]
with (HERE/'focused-hits.jsonl').open('w') as out:
 for h,path in db.execute('select hash,path from bodies'):
  p=ROOT/path
  if re.search(r'(?:screen-content|supplement-content|required-content|semantic-hits|required-hashes|screen-hashes|supplement-hashes|duplicate-stream)',p.name,re.I):excluded.append(path);continue
  try:s=p.read_text(errors='replace')
  except OSError:continue
  n+=1
  mm=[m for pat in pats for m in pat.finditer(s)]
  if mm:
   hits+=1;out.write(json.dumps({'path':path,'sha256':h,'matches':len(mm),'excerpts':[s[max(0,m.start()-150):m.end()+250] for m in mm[:6]]})+'\n')
save('focused-receipt.json',{'utc':utc(),'distinct_bodies':n,'matching_bodies':hits,'generated_roles_excluded':excluded,'limit':'six excerpts per body; no global match cutoff','scope':'same text/size/binary gaps as initial scan; exact sourceID/title/author supplement'})
print(json.dumps({'bodies':n,'hits':hits,'role_excluded':len(excluded)}))
