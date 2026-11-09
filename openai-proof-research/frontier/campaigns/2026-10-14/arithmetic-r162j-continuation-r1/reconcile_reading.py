from pathlib import Path
import json,re,hashlib,difflib
R=Path('frontier/campaigns/2026-10-14/arithmetic-r162j-continuation-r1');P=R/'packet/private'
def sha(b):return hashlib.sha256(b).hexdigest()
def merge(xs):
 out=[]
 for a,b in sorted(xs):
  if b<=a:continue
  if out and a<=out[-1][1]:out[-1][1]=max(b,out[-1][1])
  else:out.append([a,b])
 return out
def gaps(xs,n):
 out=[];last=0
 for a,b in merge(xs):
  if a>last:out.append([last,a])
  last=max(last,b)
 if last<n:out.append([last,n])
 return out
D=[json.loads(x) for x in (P/'displays.jsonl').read_text().splitlines()]
A=json.loads((P/'canonical-authentication.json').read_text());coverage=[];graph=[]
for e in A:
 p=R/e['local'];b=p.read_bytes();assert len(b)==e['size'] and sha(b)==e['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['sha']
 pdf=p.suffix.lower()=='.pdf';xs=merge([(d['start'],d['end']) for d in D if d['path']==e['path']])
 coverage.append({'path':e['path'],'size':len(b),'sha256':sha(b),'own_display_extents':xs,'own_semantic_status':'authentication only; not rendered' if pdf else 'complete; semantic acknowledgments and recovered seams in READING-NOTES.md','uncovered':None if pdf else gaps(xs,len(b))})
 if p.suffix=='.tex':
  text=re.sub(r'(?<!\\)%[^\n]*','',b.decode())
  root=p
  while root.name!='build' and root!=P:root=root.parent
  for m in re.finditer(r'\\(input|include|bibliography|addbibresource|includegraphics)(?:\[[^\]]*\])?\{([^}]+)\}',text):
   cmd,val=m.groups();targets=[]
   for v in val.split(','):
    exts=[''] if Path(v).suffix else (['.bib'] if cmd in ['bibliography','addbibresource'] else ['.pdf','.png','.jpg'] if cmd=='includegraphics' else ['.tex'])
    for base in [root,p.parent]:
     for ext in exts:
      q=(base/(v+ext)).resolve()
      if q.is_relative_to((P/'canonical').resolve()) and q.is_file():targets.append(str(q.relative_to((P/'canonical').resolve())))
   graph.append({'from':e['path'],'directive':cmd,'argument':val,'resolved':sorted(set(targets))})
assert len(A)==35 and sum(e['size'] for e in A if not e['path'].endswith('.pdf'))==1019669
assert all(not e['uncovered'] for e in coverage if e['uncovered'] is not None)
(P/'canonical-own-reading.json').write_text(json.dumps({'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','non_pdf_bytes':1019669,'files':coverage,'note':'Extent reconciliation is not semantic reading; complete own reading acknowledged in durable notes. PDFs authentication only. Diagram TeX read, no visual rendering.'},indent=2)+'\n')
(P/'include-graph.json').write_text(json.dumps(graph,indent=2)+'\n')
Ds=[json.loads(x) for x in (P/'primary-displays.jsonl').read_text().splitlines()]
primary=[]
for d in sorted((P/'primary').iterdir()):
 if not d.is_dir():continue
 auth=json.loads((d/'authentication.json').read_text())
 for e in auth['files']:
  f=d/'files'/e['file'];b=f.read_bytes();assert len(b)==e['size'] and sha(b)==e['sha256']
  xs=merge([(x['start'],x['end']) for x in Ds if x.get('id')==d.name and x.get('file')==e['file']])
  primary.append({'id':d.name,'file':e['file'],'url':auth['url'],'size':len(b),'sha256':sha(b),'direct_extents':xs,'unread_extents':gaps(xs,len(b)),'coverage_method':'direct own source read; acknowledgments in PRIMARY-NOTES.md' if xs else 'retrieved/authenticated only'})
p1=P/'primary/2601.14411v1/files/260115_kakeyadetailedproofv3.tex';p2=P/'primary/2601.14411v2/files/261001_kakeyadetailedproofv4.tex'
l1=p1.read_bytes().splitlines(keepends=True);l2=p2.read_bytes().splitlines(keepends=True)
o1=[0];o2=[0]
for x in l1:o1.append(o1[-1]+len(x))
for x in l2:o2.append(o2[-1]+len(x))
equals=[]
for tag,i,j,k,l in difflib.SequenceMatcher(None,l1,l2,autojunk=False).get_opcodes():
 if tag=='equal':equals.append({'v1':[o1[i],o1[j]],'v2':[o2[k],o2[l]]})
passages=(P/'primary/gwz-v2-new-passages.txt').read_text()
new=[[int(a),int(b)] for a,b in re.findall(r'GWZ v2 bytes \[(\d+),(\d+)\)',passages)]
assert not gaps([(x['start'],x['end']) for x in Ds if x.get('kind')=='revision-passage-display'],len(passages.encode()))
allv2=merge([x['v2'] for x in equals]+new);assert not gaps(allv2,o2[-1])
(P/'primary/gwz-v2-coverage-transfer.json').write_text(json.dumps({'equal_own_v1_to_v2':equals,'own_read_new_passages':new,'merged_v2_coverage':allv2,'meaning':'Own completed v1 mathematical reading transferred only across exact equal text; every changed nonempty v2 passage separately read with context. No predecessor credit.'},indent=2)+'\n')
for e in primary:
 if e['id']=='2601.14411v2' and e['file'].endswith('.tex'):e['coverage_method']='all changed passages read directly; exact unchanged passages transferred from own complete v1 read';e['unread_extents']=[];e['covered_extents_with_transfer']=allv2
(P/'primary-own-reading.json').write_text(json.dumps(primary,indent=2)+'\n')
print(json.dumps({'canonical_blobs':len(A),'canonical_non_pdf_bytes':1019669,'canonical_unread_mathematics':0,'include_edges':len(graph),'unresolved_include_edges':[e for e in graph if not e['resolved']],'GWZ_v2_coverage':allv2,'primary_file_records':len(primary)}))
