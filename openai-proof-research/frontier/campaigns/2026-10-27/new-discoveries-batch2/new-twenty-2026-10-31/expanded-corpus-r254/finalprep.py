import pathlib,json,re,html
L=pathlib.Path(__file__).resolve().parent; jobs=[]
pats=re.compile(r'semiacyclic|bordeaux|soliton|gilbreath|stirling.permutation|two.stack|wilf|zero.divisor|tree.like|touching.string|borg|spectral.ratio|strong.convex|quasisymmetric|treeable',re.I)
for p in L.glob('*complete-*.body'):
 try:d=json.loads(p.read_text())
 except:continue
 print(p.name,'truncated',d.get('truncated'),'entries',len(d.get('tree',[])))
 for e in d.get('tree',[]):
  if e['type']=='blob' and pats.search(e['path']):
   print(e['path'])
   if 'preprints' in p.name and e['path'].endswith('.tex'):
    h=json.loads((L/'openai-head.body').read_text())['sha'];jobs.append(('openai-manuscript-'+str(len(jobs)),'https://raw.githubusercontent.com/openai/math/'+h+'/preprints/'+e['path']))
(L/'matched-jobs.json').write_text(json.dumps(jobs))
for p in sorted(L.glob('*-abs.body')):
 s=p.read_text(); print(p.name)
 for field in ['jref','doi','comments']:
  m=re.search(r'<td class="tablecell '+field+r'">([\s\S]*?)</td>',s)
  if m:print(field,html.unescape(re.sub('<[^>]+>',' ',m[1])).strip())
# bounded history notes without numeric substring false hits
C=L.parent;keywords=re.compile(r'Bordeaux|semiacyclic|Stirling permutation|non.overlapping soliton|permutation binomial|balanced path projection|compressed zero.divisor|331498|331779',re.I)
out=[]
for p in C.rglob('*.md'):
 if L in p.parents or not p.is_file():continue
 t=p.read_text(errors='replace')
 if keywords.search(t):out.append({'path':str(p),'text':t})
for p in C.glob('*/results.json'):
 if p.parent==L:continue
 try:d=json.loads(p.read_text())
 except:continue
 if isinstance(d,dict):
  for k,v in d.items():
   if keywords.search(str(v.get('title','')) if isinstance(v,dict) else ''):out.append({'path':str(p),'id':k,'entry':v})
(L/'relevant-history.json').write_text(json.dumps(out,indent=2));print('history matched',[(v['path'],v.get('id')) for v in out])
