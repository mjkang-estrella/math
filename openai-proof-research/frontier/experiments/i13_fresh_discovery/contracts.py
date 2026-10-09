import hashlib,json,pathlib,re
ROOT=pathlib.Path(__file__).resolve().parents[3];OUT=ROOT/'frontier/sources/i13_fresh_discovery'
manifest=json.loads((OUT/'pinned-manifest.json').read_text());rows=[]
for x in manifest:
 p=ROOT/x['local_path']
 if p.suffix!='.tex':continue
 s=p.read_text()
 for m in re.finditer(r'\\begin\{(theorem|proposition|lemma|corollary)\}(?:\[[^\]]*\])?[\s\S]*?\\end\{\1\}',s):
  labels=re.findall(r'\\label\{([^}]+)\}',m[0]);line=s.count('\n',0,m.start())+1
  rows.append({'path':x['upstream_path'],'git_blob':x['git_blob'],'sha256':x['sha256'],'start_line':line,'labels':labels,'statement':m[0]})
(OUT/'theorem-contracts.json').write_text(json.dumps(rows,indent=2)+'\n')
brief=json.loads((OUT/'inputs/frontier/iterations/iteration13-fresh-discovery-task.json').read_text())['brief']
(OUT/'full-brief.txt').write_text('Act as the research sub-agent for this task.\n\n'+brief+'\n')
print('Recorded',len(rows),'exact statement blocks.')
for key in ['Sidorenkos','Common-Integer','Rokhlins','Pointwise-Multiple','distinct-integer-slopes']:
 print('\n'+key)
 for x in manifest:
  if key in x['upstream_path'] and ('introduction.tex' in x['upstream_path'] or x['upstream_path'].endswith('/kernel.tex')):print(x['upstream_path'],x['git_blob'])
