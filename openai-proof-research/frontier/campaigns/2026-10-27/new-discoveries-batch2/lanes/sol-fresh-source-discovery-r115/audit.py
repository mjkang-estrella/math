import os,re,hashlib,json,time
from pathlib import Path
root=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
lane=Path(__file__).resolve().parent
exact=re.compile(r'(?<![0-9])(?:2209[.]00986|2511[.]08320|1103[.]2298)(?:v[0-9]+)?(?![0-9])')
assert exact.search('arXiv:2209.00986v2') and not exact.search('12209.009860')
semantic=re.compile(r'common.transversal|Aivazidis|Loukaki|sum of element orders|T[ăa]rn[ăa]uceanu|Giuga|arithmetic derivative',re.I)
generated=re.compile(r'(?:inventory-content|required-content|supplement-content|screen-content|semantic-hits?|duplicate-corpus|screen-hits?|screen-hit-excerpts|(?:inventory|required|supplement|screen)-hashes)',re.I)
counts={'files':0,'bytes':0,'hit_files':0,'excluded':0,'errors':0,'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'regex_selftests':'PASS'}
with (lane/'audit-manifest.jsonl').open('w') as mf,(lane/'audit-matches.jsonl').open('w') as hf,(lane/'audit-exclusions.jsonl').open('w') as ef:
 for base,dirs,files in os.walk(root):
  dirs[:]=[d for d in dirs if d not in {'.git','.lake','node_modules','__pycache__'} and Path(base,d)!=lane]
  for name in files:
   p=Path(base,name);rel=str(p.relative_to(root))
   if generated.search(name):
    ef.write(json.dumps({'path':rel,'reason':'generated corpus echo or its generated match/hash index; not read as mathematics','bytes':p.stat().st_size})+'\n');counts['excluded']+=1;continue
   if p.suffix.lower() not in {'.md','.txt','.tex','.py','.lean','.json','.jsonl','.html','.bib','.csv','.tsv'}:continue
   h=hashlib.sha256();n=0;hits=0
   try:
    with p.open('rb') as f:
     # Fixed bounded chunks; overlap handles token splits. No corpus buffer.
     tail=b'';offset=0
     while True:
      b=f.read(65536)
      if not b:break
      h.update(b);n+=len(b);s=(tail+b).decode('utf-8','replace')
      if hits<4:
       for m in semantic.finditer(s):
        hf.write(json.dumps({'path':rel,'chunk_byte_offset':offset,'excerpt':s[max(0,m.start()-160):m.end()+260],'exact_source_id':bool(exact.search(s))})+'\n');hits+=1
        if hits>=4:break
      tail=b[-512:];offset+=len(b)
    mf.write(json.dumps({'path':rel,'sha256':h.hexdigest(),'bytes':n,'bounded_hits':hits})+'\n');counts['files']+=1;counts['bytes']+=n;counts['hit_files']+=bool(hits)
   except OSError as e:
    ef.write(json.dumps({'path':rel,'error':str(e)})+'\n');counts['errors']+=1
counts['completed_utc']=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())
(lane/'audit-receipt.json').write_text(json.dumps(counts,indent=2)+'\n')
print(json.dumps(counts))
