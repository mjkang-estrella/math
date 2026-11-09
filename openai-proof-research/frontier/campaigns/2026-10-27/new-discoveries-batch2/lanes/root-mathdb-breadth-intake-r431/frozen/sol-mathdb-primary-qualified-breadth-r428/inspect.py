from pathlib import Path
import json,re
R=Path(__file__).resolve().parent;out=[]
for o in json.loads((R/'records.json').read_text()):
 n=o['source_url'].rsplit('/',1)[1];p=R/f'sources/{n}.txt';pg=int(re.search(r'page (\d+)',o['source_name'])[1])
 if not p.exists():print(o['mathdb_id'],'MISSING');continue
 pages=p.read_text().split('\f');txt=pages[pg-1] if pg<=len(pages) else ''
 out.append({'mathdb_id':o['mathdb_id'],'file':f'sources/{n}.txt','physical_page':pg,'excerpt':txt})
 print('\n###',o['mathdb_id'],o['title'],'PAGE',pg,'\n'+txt)
(R/'source-excerpts.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
