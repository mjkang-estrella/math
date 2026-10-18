#!/usr/bin/env python3
"""Bounded, read-only history search. Matches are evidence pointers, not clearance."""
import argparse, hashlib, json, os, re
from pathlib import Path
P=argparse.ArgumentParser(); P.add_argument('--root',type=Path,required=True); P.add_argument('--output',type=Path,required=True); P.add_argument('--replay-index',type=Path); a=P.parse_args()
root=a.root.resolve(); own=Path(__file__).resolve().parent
replay=json.loads(a.replay_index.read_text()) if a.replay_index else None
allowed={x['path'] for x in replay['artifacts']} if replay else None
if replay:
 for x in replay['artifacts']:
  p=root/x['path']
  if not p.is_file() or p.is_symlink() or hashlib.sha256(p.read_bytes()).hexdigest()!=x['sha256']:raise SystemExit('history input drift: '+x['path'])
 for path,digest in replay['source_inputs'].items():
  if hashlib.sha256((root/path).read_bytes()).hexdigest()!=digest:raise SystemExit('catalogue input drift: '+path)
sha=lambda b:hashlib.sha256(b).hexdigest()
cat=(root/'sources/CONTENTS.md').read_text(); fam={}
heads=list(re.finditer(r'^\*\*(\d{3})\.\s+(.*?)\*\*',cat,re.M))
for i,h in enumerate(heads):
 block=cat[h.end():heads[i+1].start() if i+1<len(heads) else len(cat)]
 papers=[{'title':m[0],'directory':m[1]} for m in re.findall(r'\[([^\]]+)\]\(preprints/([^/]+)/[^)]+\)',block)]
 fam[h[1]]={'name':h[2].rstrip('.'),'papers':papers,'authored_matches':[],'reference_matches':[]}
slugs={p['directory']:f for f,v in fam.items() for p in v['papers']}
syn={'129':['sakoda','sipser','one-way liveness','2dfa','2nfa','two-way deterministic state'], '324':['c0 absorption','absorption of c0','nonlinear banach','s88'], '188':['triangle removal','triangle-removal','terminal leave','terminal-leave'], '150':['triangular billiard','triangular-billiard','irrational triangle','irrational-triangle','full liouville','full-liouville'], '094':['terminal embedding','terminal dimension','dimension reduction in lp','subpolynomial dimension reduction','johnson lindenstrauss','almost extension'], '099':['edit distance','edit-distance'], '176':['kahn kalai','expectation threshold','rooted transfer'], '255':['polycyclic','quasi isometric recognition','quasi-isometric recognition']}
# Exact title phrases supplement explicit family labels and source-directory identities.
norm=lambda s:re.sub(r'[^a-z0-9]+',' ',s.lower()).strip()
phrases={f:[norm(v['name'])]+[norm(p['title']) for p in v['papers']] for f,v in fam.items()}
from collections import defaultdict
ngram_families=defaultdict(set)
for f,ps in phrases.items():
 for phrase in ps:
  ws=phrase.split()
  for n in (3,4):
   for k in range(len(ws)-n+1):
    g=' '.join(ws[k:k+n])
    if sum(len(w)>3 for w in ws[k:k+n])>=2:ngram_families[g].add(f)
unique_ngrams={g:next(iter(fs)) for g,fs in ngram_families.items() if len(fs)==1}
slug_re=re.compile('|'.join(re.escape(s) for s in sorted(slugs,key=len,reverse=True)))
prune={'private','inputs','input','context','snapshots','snapshot','sources','source','primary','literature','raw','work','output','thirdparty','third-party','upstream','pinned','preprints','build','__pycache__','.git','.lake','node_modules','vendor','lean','mathlib','logs','pdf','pages','figures','checks','tests','experiments','mutations','semantic-controls'}
skipname=re.compile(r'(?:brief|dispatch|prompt|task|catalogue|catalog|tree|titles|snapshot|input-copy|context-copy|history-hits|search-hits|search-results)',re.I)
roots=['frontier','frontier/sources','proposals','findings','reviews','notes']; artifacts=[]; excluded=[]
for domain in roots:
 start=root/domain
 if not start.exists():continue
 for d,ds,fs in os.walk(start,followlinks=False):
  dp=Path(d)
  ds[:]=sorted(x for x in ds if x not in prune and not x.startswith('.') and not (dp/x).is_symlink() and (dp/x).resolve()!=own and not (x=='frontier' and dp!=root))
  for name in sorted(fs):
   p=dp/name; rel=p.relative_to(root).as_posix()
   if allowed is not None and rel not in allowed:continue
   if p.is_symlink() or not p.is_file() or p.stat().st_size>2_000_000:continue
   meta=p.suffix=='.json' and re.search(r'(receipt|manifest|provenance)',name,re.I)
   authored=domain!='frontier/sources' and p.suffix in {'.md','.txt'} and not skipname.search(name)
   if not(meta or authored):continue
   b=p.read_bytes()
   try:t=b.decode('utf8')
   except UnicodeError:continue
   lines=t.splitlines(); found={}
   # Directory identity is exact and works in receipts/manifests too.
   for j,line in enumerate(lines,1):
    ids=set()
    for slug in slug_re.findall(line):
     if slug in slugs:ids.add((slugs[slug],'directory'))
    if authored:
     for m in re.finditer(r'\bfamil(?:y|ies)\s*[:#-]?\s*(\d{3})\b',line,re.I):
      if m[1] in fam:ids.add((m[1],'family-label'))
     nl=norm(line)
     ws=nl.split(); grams=defaultdict(set)
     for n in (3,4):
      for k in range(len(ws)-n+1):
       g=' '.join(ws[k:k+n])
       if g in unique_ngrams:grams[unique_ngrams[g]].add(g)
     for f,gs in grams.items():
      if len(gs)>=2:ids.add((f,'title-ngram'))
     if re.search(r'famil(?:y|ies)|Banach',line,re.I):
      for f in re.findall(r'(?<![0-9])([0-3][0-9]{2})(?![0-9])',line):
       if f in fam:ids.add((f,'context-family-number'))
     for f,terms in syn.items():
      if any(norm(x) in nl for x in terms):ids.add((f,'context-synonym'))
    for f,why in sorted(ids):
     found.setdefault(f,[]).append({'line':j,'kind':why,'excerpt':line[:420]})
   artifacts.append({'path':rel,'sha256':sha(b),'bytes':len(b),'class':'authored-note' if authored else 'metadata-reference','families':sorted(found)})
   for f,hits in found.items():fam[f]['authored_matches' if authored else 'reference_matches'].append({'path':rel,'hits':hits})
if allowed is not None and {x['path'] for x in artifacts}!=allowed:raise SystemExit('replay domain differs')
tree=json.loads((root/'sources/preprints-tree.json').read_text()); entries=tree['tree']; dirs=sorted({e['path'].split('/')[1] for e in entries if e['path'].startswith('preprints/') and len(e['path'].split('/'))>=3})
result={'schema':1,'scope':'Read-only bounded repository history; matches require report reading, absence is not novelty clearance.','source_inputs':{p:sha((root/p).read_bytes()) for p in ['sources/CONTENTS.md','sources/preprints-tree.json','sources/upstream.json']},'scan_roots':roots,'excluded_directory_names':sorted(prune),'excluded_filename_pattern':skipname.pattern,'max_file_bytes':2000000,'synonyms':syn,'artifacts':sorted(artifacts,key=lambda x:x['path']),'families':fam,'uncatalogued_preprint_directories':sorted(set(dirs)-set(slugs))}
a.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'artifacts':len(artifacts),'families':len(fam),'mapped_directories':len(slugs),'unmapped_directories':len(result['uncatalogued_preprint_directories']),'authored_matched_families':sum(bool(x['authored_matches']) for x in fam.values())}))
