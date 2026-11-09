import sys,re,os,glob,json
d=sys.argv[1]; tree=sys.argv[2]
files=[os.path.join(d,'LeanPool_projects.yml')]+sorted(glob.glob(os.path.join(d,'candidates_*')))
text={os.path.basename(f):open(f,encoding='utf-8',errors='replace').read() for f in files}
paths='\n'.join(t['path'] for t in json.load(open(tree))['tree'])
text['TREE_PATHS']=paths
KW={
'349834':['2102.10397','petersen','349834','diameter of generalized'],
'367578':['2503.14780','367578','symmetric tensor','symmetric-tensor','x-matroid','unique maximal'],
'382445':['2511.22492','382445','steiner','oellermann'],
'338345':['1802.01217','338345','plex','ryser'],
'339233':['1805.04888','339233','339234','local antimagic','antimagic'],
'339445':['1806.01835','339445','tropical','upper triangular','bicyclic'],
'339995':['1808.01074','339995','consum'],
'340115':['1808.05213','340115','transversal','brualdi','latin'],
'340262':['1809.00142','340262','dichromatic','digirth','neumann-lara','neumann lara'],
'340616':['1810.01161','340616','deleted join','z_2-index','kneser'],
'340618':['1810.01225','340618','kleitman','samotij','projective cube'],
'341388':['1812.06288','341388','chen-chv','chvátal','chvatal','metric line','lines in'],
'335383':['1702.07589','335383','schnyder','unicellular','triangulation'],
'336139':['1705.08150','336139','permanent','1-2-3','weighting'],
'336449':['1706.07213','336449','inversion sequence','3-crossing','noncrossing','crossings'],
'336565':['1707.02003','336565','336566','3-design','t-design','weight enumerator'],
'336741':['1708.00094','336741','unique-maximum','unique maximum','fum','facial'],
'337060':['1709.04750','337060','circulant','edge-transitive','arc-transitive'],
}
res={}
for mid,ks in KW.items():
    hits=[]
    for f,t in text.items():
        tl=t.lower()
        for k in ks:
            for m in re.finditer(re.escape(k),tl):
                s=max(0,m.start()-80);e=min(len(t),m.end()+80)
                hits.append((f,k,t[s:e].replace('\n',' ')))
    seen=set(); u=[]
    for h in hits:
        key=(h[0],h[2][:70])
        if key in seen: continue
        seen.add(key); u.append(h)
    res[mid]=u
    print(f'== {mid}: {len(u)} hits')
    for h in u[:25]: print('   ',h[0],'|',h[1],'|',h[2])
