from pathlib import Path
import json,re,hashlib,html
D=Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());rows={}
keywords={349645:['coupled','Barr','Biedl'],349656:['SlowNim','slow nim','Chikin','Gurvich','Vyalyi'],349708:['derangement','Razafimahatratra','Spiga'],349881:['Fujino','extremal rational'],350049:['Rousseau','Sheehan','large books'],350069:['carousel','inducibility','Lidicky'],350318:['Wiener','eccentricity'],350439:['matroid lift','Walsh','Bernstein'],350518:['robust connectivity','Masarik','Bradshaw'],350520:['grid genus','Salinas','Millichap'],350624:['fractional transversal','Bujtas','Tuza','Rote'],350638:['inversion'],350662:['graphical function','Schnetz','Borinsky'],351078:['tree packing'],351124:['fiberedness','Laba','Londner'],351193:['metric dimension','Sedlar','Skrekovski'],351194:['edge metric','zero forcing','Sedlar'],351288:['CRG','edit distance','Riasanovsky'],351460:['prism','Spacapan'],351463:['Calabi']}
poolfiles=[p for p in (D/'sources').glob('pool-*') if not p.name.endswith('.receipt.json') and p.name!='pool-head.json']
for i,o in x.items():
 pats=[i,o['source_url'].rsplit('/',1)[-1]]+keywords[int(i)];hits=[]
 for p in poolfiles:
  for n,l in enumerate(p.read_text(errors='replace').splitlines(),1):
   matched=[a for a in pats if a.lower() in l.lower()]
   if matched:hits.append({'file':p.name,'line':n,'terms':matched,'text':l[:400]})
 rows[i]={'terms':pats,'pool_hits':hits,'scope':'content screen of projects and candidates; tree path screen; keyword hits are not statement equivalence'}
heads={k:json.loads((D/f'sources/{k}-head.json').read_text())['sha'] for k in ['pool','omega','openai']}
omega={}
for name in ['D5','Problems']:
 obj=json.loads((D/f'sources/omega-{name}.json').read_text());omega[name]={'truncated':obj.get('truncated'),'entries':len(obj['tree']),'hits':{i:[t['path'] for t in obj['tree'] if any(a.lower() in t['path'].lower() for a in r['terms'])] for i,r in rows.items()}}
search=json.loads((D/'outputs/github-queries.json').read_text())
for j,r in enumerate(search,1):
 obj=json.loads((D/f'sources/github-search-{j}.json').read_text());r['total_count']=obj.get('total_count');r['first_repositories']=[t['full_name'] for t in obj.get('items',[])][:5]
report={'utc':'2026-11-05','heads':heads,'pool_tree_truncated':json.loads((D/'sources/pool-tree.json').read_text()).get('truncated'),'targets':rows,'omega_path_screen':omega,'github_queries':search,'github_limitation':'All eight query responses have identical body hashes, total_count 65458 and generic lean repositories, despite distinct q URLs. Search results are uninformative; no GitHub novelty clearance claimed. Eight-query ceiling respected; no further API search attempted.','openai_scope':'HEAD unchanged from root pinned complete preprint listing; reused cache reference fresh-corpus-r10/sources/registry-preprints.json; not proof-body clearance.'}
(D/'outputs/registry-screen.json').write_text(json.dumps(report,indent=2,ensure_ascii=False))
print('Pool hits', {i:len(r['pool_hits']) for i,r in rows.items()});print('Omega hits',{name:{i:hs for i,hs in r['hits'].items() if hs} for name,r in omega.items()})
