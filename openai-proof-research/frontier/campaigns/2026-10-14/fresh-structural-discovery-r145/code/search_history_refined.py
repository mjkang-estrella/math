"""Bounded authored-history search. Prune components before descent/selection."""
from pathlib import Path
import os,re,json,hashlib,datetime
PROJECT=Path(__file__).resolve().parents[5]
ROOT=Path(__file__).resolve().parents[1]
role=re.compile(r'(arithmetic.*r(?:110|109|108|107)|analytic.*r(?:139|138|137|136|135)|structural.*r(?:145|144|143)|h138-|t185r144-|t177c143-|t373e135-|k369r134-|t088p133-)',re.I)
derivative=re.compile(r'(corpus|source|primary|history|search|inventory|fixture|control|extract|render|vendor|build|cop(?:y|ies|ied)|frozen|role|formal|manuscript|release|parent|intake|brief|task|dispatch|prompt|snapshot|ledger|cache|packet|payload|outside|envelope|archive|fetched|catalog|input|private|work|venv|site-packages|literature|upstream|pinned|context|review|proof-r|contribution-r|authenticat|manifest|provenance|sawin-2018|node_modules|\.git)',re.I)
needle=re.compile(r'union[\s_\-–‐]*closed|Frankl|Gilmer|Sawin|Chase.{0,15}Lovett|inverse.{0,15}(union|multiplicit)|Sinkhorn|bistochastic|doubly[\s-]*stochastic|2609\.08291',re.I)
records=[]; stats={'directories_pruned':0,'files_pruned':0,'text_read':0,'binary_or_encoding_skips':0,'symlinks_skipped':0}; selected=[]
for base in ['frontier','iterations','experiments','proposals','scouts','notes','findings']:
 top=PROJECT/base
 if not top.is_dir():continue
 for parent,dirs,files in os.walk(top,followlinks=False):
  kept=[]
  for d in dirs:
   p=Path(parent)/d
   if p.is_symlink():stats['symlinks_skipped']+=1
   elif role.search(d) or derivative.search(d):stats['directories_pruned']+=1
   else:kept.append(d)
  dirs[:]=kept
  for f in files:
   p=Path(parent)/f
   if p.is_symlink():stats['symlinks_skipped']+=1;continue
   if role.search(f) or derivative.search(f):stats['files_pruned']+=1;continue
   data=p.read_bytes()
   if b'\0' in data:stats['binary_or_encoding_skips']+=1;continue
   try:s=data.decode('utf-8')
   except UnicodeDecodeError:stats['binary_or_encoding_skips']+=1;continue
   stats['text_read']+=1; selected.append(str(p.relative_to(PROJECT)))
   hits=[{'line':i,'text':line} for i,line in enumerate(s.splitlines(),1) if needle.search(line)]
   if hits:records.append({'path':str(p.relative_to(PROJECT)),'size':len(data),'sha256':hashlib.sha256(data).hexdigest(),'hits':hits})
out=ROOT/'private/history-search-refined.json'
out.write_text(json.dumps({'time':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'UTF8 authored candidates, hidden/ignored/JSON/no size cutoff; coarse exclusions not exhaustive','stats':stats,'selected_paths':selected,'hits':records},indent=2)+'\n')
print(json.dumps(stats));print('hit files',len(records))
for h in records: print(h['path'], 'lines',','.join(str(x['line']) for x in h['hits']))
