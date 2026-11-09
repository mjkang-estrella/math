import json,re,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
kws={'343536':['equitable','gridgraph','grid_graph','synchrony','orbitpartition','neuberger','sieben'],
 '339076':['motzkin','scrimshaw'],'369840':['vincular','hankel','deb'],'339049':['edelman','greene','potka','linusson'],
 '352683':['piercing','chessboard','plank'],'341256':['resistor','punctured','conductance','electrical'],
 '341292':['laver'],'343979':['ulam','hinman'],'373759':['superregular','super_regular','mdsprob','mdscode','mds_'],
 '366032':['kazhdan','lusztig','tubbenhauer'],'364816':['mstratio','emst','spanningtree'],'344785':['commonsubseq','lcs','frog'],
 '344963':['unitcommit','ramping','minstop'],'338974':['cambrian','weylposet','pilaud'],'339832':['deltaconj','schroder','haglund'],
 '340156':['binomialedge','hibi','matsuda'],'339553':['szabo','seed','mutation'],'344161':['kitchloo','symmetrybreak','linkhomolog'],
 '338731':['densesubgraph','logisticregression','linkpredict'],'338263':['momentmatch','modelorder','sylvester']}
out={'heads':{k:json.loads((D/'sources'/f'{k}-head.json').read_text())['sha'] for k in ['omega','openai']}}
for f in ['omega-D5-tree.json','omega-Problems-tree.json','openai-preprints-tree.json']:
    d=json.loads((D/'sources'/f).read_text()); paths=[o['path'] for o in d['tree']]
    res={}
    for i,ks in kws.items():
        h=sorted({p for p in paths for k in ks if k in re.sub(r'[^a-z_]','',p.lower())})
        res[i]=h[:12]+([f'... {len(h)} total'] if len(h)>12 else [])
    out[f]={'entries':len(paths),'truncated':d.get('truncated'),'hits':res}
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=1)+'\n')
for f in ['omega-D5-tree.json','omega-Problems-tree.json','openai-preprints-tree.json']:
    print(f,out[f]['entries'],out[f]['truncated'],{i:len(h) for i,h in out[f]['hits'].items() if h})
