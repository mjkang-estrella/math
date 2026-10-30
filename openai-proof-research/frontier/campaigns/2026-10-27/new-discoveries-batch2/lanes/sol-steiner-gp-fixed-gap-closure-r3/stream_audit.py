from work import *
out=[];selected=[]
pattern=re.compile(r'general.position|steiner|false.twin|\bclon(?:e|ing)|n.ary transit|lexicographic|graph.convex|weighted.{0,40}substitu',re.I)
for p in sorted((R/'diffs').glob('*.diff')):
 recs=[];block=[]
 def consume(lines):
  if not lines:return
  m=re.match(r'diff --git a/(.*?) b/(.*?)$',lines[0].rstrip());assert m
  a,b=m.groups();text=''.join(lines);hits=[s[:500] for s in lines if pattern.search(s)]
  rec={'old_path':a,'new_path':b,'removed':'deleted file mode' in text,'renamed':'rename from ' in text,'added':'new file mode' in text,'bytes':len(text.encode()),'sha256':hashlib.sha256(text.encode()).hexdigest()}
  recs.append(rec)
  if hits or (re.search(r'/Graph/|CONVEX|FIEDLER',b,re.I) and not b.endswith('.json')):
   q=L/'selected-diffs'/p.stem/(str(len(recs))+'.txt');q.parent.mkdir(parents=True,exist_ok=True);q.write_text(text)
   selected.append(dict(rec,commit=p.stem,body=str(q.relative_to(L)),hits=hits[:12]));print(p.stem,b,len(hits),flush=True)
 with p.open() as f:
  for line in f:
   if line.startswith('diff --git '):consume(block);block=[]
   block.append(line)
  consume(block)
 out.append({'commit':p.stem,'file':str(p.relative_to(L)),'files':recs})
(L/'diff-coverage.json').write_text(json.dumps(out,indent=2));(L/'semantic-selection.json').write_text(json.dumps(selected,indent=2));print('diffs',len(out),'selected',len(selected))
