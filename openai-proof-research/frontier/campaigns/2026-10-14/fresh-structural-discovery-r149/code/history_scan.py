"""Bounded-family history navigation; prospective component pruning, no size cutoff."""
from pathlib import Path
import os,fnmatch,json,re,hashlib
PROJECT=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
OWN=PROJECT/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r149'
ROUND=['*arithmetic*r113*','*analytic*r143*','*arithmetic*r114*','*analytic*r144*',
 '*structural*r148*','*structural*r147*','*structural*r146*','*structural*r145*',
 '*analytic*r142*','*analytic*r141*','*analytic*r140*','*analytic*r139*',
 '*arithmetic*r112*','*arithmetic*r111*','*arithmetic*r110*','*arithmetic*r109*','*arithmetic*r108*','*arithmetic*r107*',
 '*analytic*r138*','*structural*r144*','*structural*r143*','*analytic*r137*','*analytic*r136*','*analytic*r135*',
 '*h138-*','*t185r144-*','*t177c143-*','*t373e135-*','*k369r134-*','*t088p133-*']
DERIVATIVE=['corpus','source','primary','history-derivative','search','inventory','fixture','control','extract','render','vendor','build','copy','copied','frozen','role','formal','manuscript','release','parent','private','input','upstream','context','fetched','scratch','preprint','catalogue','catalog','intake','prompt','recovery','brief','dispatch','handoff','worker','agent','review','contribution','snapshot','session','transcript','history','task','manifest','authentication','authenticate','family-titles','paths','work','factory','attempt-','node_modules','.git','.venv','__pycache__']
def blocked(name):
 n=name.lower()
 return any(fnmatch.fnmatchcase(n,p) for p in ROUND) or any(x in n for x in DERIVATIVE)
PATTERN=re.compile(r'thin[ -]?(?:spanning[ -]?)?tree|spectrally[ -]thin|source[ -]?174|T174|effective[ -]resistance|Goddyn|Anari.{0,20}Gharan|Asadpour',re.I)
def main():
 counts={'utf8':0,'nonutf8':0,'nul':0,'symlink':0,'pruned':0};hits=[];eligible=[]
 for d,ds,fs in os.walk(PROJECT,topdown=True,followlinks=False):
  base=Path(d)
  keep=[]
  for n in sorted(ds):
   p=base/n
   if p==OWN or p.is_symlink() or blocked(n):counts['pruned']+=1
   else:keep.append(n)
  ds[:]=keep
  for n in sorted(fs):
   p=base/n
   if blocked(n):counts['pruned']+=1;continue
   if p.is_symlink():counts['symlink']+=1;continue
   b=p.read_bytes()
   try:s=b.decode('utf8')
   except UnicodeDecodeError:counts['nonutf8']+=1;continue
   if '\0' in s:counts['nul']+=1;continue
   counts['utf8']+=1
   rel=str(p.relative_to(PROJECT));eligible.append({'path':rel,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
   lines=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if PATTERN.search(l)]
   if lines:hits.append({'path':rel,'matches':lines})
 result={'policy':{'project':str(PROJECT),'round_globs':ROUND,'derivative_substrings':DERIVATIVE,'symlinks':False,'size_cutoff':None,'hidden_ignored_json':True,'pattern':PATTERN.pattern},'counts':counts,'hits':hits}
 (OWN/'private/history-search-refined.json').write_text(json.dumps(result,indent=2))
 (OWN/'private/history-eligible-refined.json').write_text(json.dumps(eligible,indent=2))
 print(json.dumps({'counts':counts,'hit_files':len(hits),'hits':[{'path':x['path'],'matches':x['matches'][:4]} for x in hits]},indent=2))
if __name__=='__main__':main()
