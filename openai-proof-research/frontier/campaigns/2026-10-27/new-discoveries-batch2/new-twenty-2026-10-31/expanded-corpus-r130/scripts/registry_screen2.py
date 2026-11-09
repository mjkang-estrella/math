import json,sys,re,pathlib
D=pathlib.Path(sys.argv[1]); kws=['binarypartition','binary_partition','colored','coloured','ulas','zmija','borwein','partialtheta','hardhexagon','hexagon','disk','disktree','crystal','grothendieck','divisible','janson','simplygenerated','landau','rademacher','2314','inversionseq','delta','orientation','alonyuster','matroid','hopf','indicator','holonom','pilegame','metricgraph','resonance','churchhouse','valuation','Dstar','digraphD']
out={}
for f in ['omega-D5-tree.json','omega-Problems-tree.json','omega-tree.json','openai-tree.json','openai-preprints-tree.json']:
    d=json.loads((D/'sources'/f).read_text()); paths=[o['path'] for o in d.get('tree',[])]
    hits={}
    for k in kws:
        h=[p for p in paths if k.lower() in re.sub(r'[^a-z0-9]','',p.lower())]
        if h: hits[k]=h[:8]
    out[f]=dict(entries=len(paths),truncated=d.get('truncated'),hits=hits)
print(json.dumps(out,indent=1))
