import sys,re,os,glob,json
d=sys.argv[1]; tree=sys.argv[2]
files=sorted(glob.glob(os.path.join(d,'*')))
text={os.path.basename(f):open(f,encoding='utf-8',errors='replace').read() for f in files}
text['TREE_PATHS']='\n'.join(t['path'] for t in json.load(open(tree))['tree'])
KW={
'334808':['1612.02843','334808','strong resolving','resolving graph','mutually maximally'],
'334872':['1612.05447','334872','reed-solomon','reed solomon','normal rational','mds'],
'334925':['1612.07652','334925','dimatroid','fair representation','matroid intersection'],
'339813':['1807.04741','339813','queens','kotesovec','kotěšovec'],
'329577':['1501.00573','329577','guo','zeilberger'],
'329610':['1501.02009','329610','mahler'],
'329760':['1501.06872','329760','partial sum','alspach','sequenceable','sequencing'],
'330216':['1503.09175','330216','kneser'],
'330252':['1504.01949','330252','feedback vertex','induced forest'],
'330285':['1504.03662','330285','orthogonal representation'],
'330593':['1505.06984','330593','kikuta','ruckle','caching'],
'330655':['1506.01887','330655','hadwiger-nelson','hadwiger nelson','unit distance','exoo'],
'330666':['1506.02517','330666','perfect code','golomb'],
'330713':['1506.04640','330713','hitchin','fuchsian'],
'331313':['1509.01185','331313','disconnected minor','average degree','wang-wu','csoka'],
'331481':['1510.00258','331481','loomis','uniform cover'],
'331535':['1510.02075','331535','cycle double cover','cycle cover'],
'331543':['1510.02521','331543','latin square'],
'331819':['1511.05384','331819','hypotraceable','path cover','vertex cover','traceable'],
'331893':['1511.07866','331893','warmth','neighborhood complex','hom complex'],
}
for mid,ks in KW.items():
    hits=[]
    for f,t in text.items():
        tl=t.lower()
        for k in ks:
            for m in re.finditer(re.escape(k),tl):
                hits.append((f,k,t[max(0,m.start()-70):m.end()+70].replace('\n',' ')))
    seen=set();u=[]
    for h in hits:
        key=(h[0],h[2][:60])
        if key not in seen: seen.add(key);u.append(h)
    print(f'== {mid}: {len(u)} hits')
    for h in u[:12]: print('   ',h[0],'|',h[1],'|',h[2])
