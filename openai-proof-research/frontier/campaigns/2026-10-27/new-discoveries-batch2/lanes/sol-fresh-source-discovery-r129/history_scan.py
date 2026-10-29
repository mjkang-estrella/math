import os,re,json,hashlib,pathlib,collections
base=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
lane=pathlib.Path(__file__).parent
patterns={
 'radon':r'2507[.]01353|Unimodality for Radon partitions|Youden.{0,20}demon|Ter.Saakov|Radon.{0,80}(log.concav|unimodal)|Chan.{0,80}Kalai',
 'tu':r'2609[.]39917|Approximate Counting for Totally Unimodular|Mohammadi.{0,10}Yekta|Leake.{0,100}(unimodular|Barvinok)|Question 1[.]7',
}
rx={k:re.compile(v,re.I) for k,v in patterns.items()}
exts={'.md','.txt','.tex','.json','.jsonl','.html','.lean','.rst'}
# Role exclusions, not whole lanes. Original r111-r113 scientific files retained.
prune={'.git','.lake','node_modules','__pycache__','legacy-replay','fresh-replay','replay-fresh','outer-extracted-replay','rebuild-extraction','strict-replay','verification-final','verification-fresh','extracted-source','extracted-component','extracted','cache','caches','search-cache','registry-cache'}
seen={};counts=collections.Counter(); omitted=collections.Counter();matches=[]
with (lane/'history/omitted.jsonl').open('w') as omit:
 for root,dirs,files in os.walk(base):
  dirs[:]=[d for d in dirs if d not in prune and pathlib.Path(root,d)!=lane]
  for f in files:
   p=pathlib.Path(root,f); rel=str(p.relative_to(base))
   if p.suffix.lower() not in exts: omitted[p.suffix or '<none>']+=1;continue
   if p.stat().st_size>2097152:
    omit.write(json.dumps({'path':rel,'reason':'file >2MiB; explicit semantic gap','bytes':p.stat().st_size})+'\n');counts['oversized_json_omitted']+=1;continue
   # Generated inventories and echoed historical search output are not original research.
   if re.search(r'(?:tree|manifest|history.scan|historical.scan|history.hits|historical.hits|search.results|http|commit.paths|declarations|axiom.report)',f,re.I):
    counts['generated_name_omissions']+=1;continue
   h=hashlib.sha256()
   try:
    with p.open('rb') as inp:
     for b in iter(lambda:inp.read(65536),b''):h.update(b)
    digest=h.hexdigest();counts['files']+=1
    if digest in seen:seen[digest]['aliases'].append(rel);counts['duplicate_files']+=1;continue
    record={'sha256':digest,'representative':rel,'aliases':[]};seen[digest]=record
    counts['unique_files']+=1
    with p.open(errors='replace') as inp:
     for num,line in enumerate(inp,1):
      for key,r in rx.items():
       if r.search(line):
        hit={'target':key,'path':rel,'sha256':digest,'line':num,'excerpt':line[:1800].rstrip(),'line_truncated':len(line)>1800}
        matches.append(hit)
   except (OSError,UnicodeError) as e:omit.write(json.dumps({'path':rel,'error':str(e)})+'\n');counts['errors']+=1
with (lane/'history/matches.jsonl').open('w') as out:
 for hit in matches:out.write(json.dumps(hit)+'\n')
with (lane/'history/aliases.jsonl').open('w') as out:
 for rec in seen.values():
  if rec['aliases'] or any(m['sha256']==rec['sha256'] for m in matches):out.write(json.dumps(rec)+'\n')
summary={'counts':dict(counts),'patterns':patterns,'date_filter':None,'global_hit_cutoff':None,'per_matching_line_excerpt_characters':1800,'oversize_omitted':counts['oversized_json_omitted'],'omitted_extensions':dict(omitted),'pruned_role_directories':sorted(prune),'semantic_gap':'Lexical screen only; generated-name, oversized JSON and role exclusions can omit relevant text. Raw PDFs not independently extracted by scan. No novelty clearance.'}
(lane/'history/receipt.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary));print('hits',len(matches))
