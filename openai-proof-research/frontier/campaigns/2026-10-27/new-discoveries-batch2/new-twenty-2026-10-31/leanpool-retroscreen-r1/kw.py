import sys,re,os,glob
d=sys.argv[1]
files=[os.path.join(d,'LeanPool_projects.yml')]+sorted(glob.glob(os.path.join(d,'candidates_*')))
text={f:open(f,encoding='utf-8',errors='replace').read() for f in files}
KW={
'388087':['clutter','kiraly','király','nonideal'],
'333569':['intricacy','markov law'],
'347712':['maximum-agreement','maximum agreement','latin square strateg'],
'355140':['maker-breaker','maker breaker','staller'],
'364095':['triangle-distinguish','distinguishes all triangles','edge coloring of k5','k_5'],
'355956':['paley','generalized paley','yip','maximal clique'],
'365710':['irregularity','sigma_t','σ_t'],
'366371':['majorization','ordinal space'],
'364205':['rigid','hamming cube','diameter-5'],
'380362':['moufang','quarter-table','loop of order 16'],
'381805':['edge-magic','edge magic','super edge'],
'378395':['marginal cone','non-collapsing','facet'],
'334599':['supervenience','ternary frame'],
'331705':['cassinian','starlike','wedge'],
'372205':['xor-magic','xor magic'],
'368807':['subtour','asymmetric traveling','atsp','tsp polytope'],
'381433':['non-q','adverse','cyclic latin'],
'349441':['kirchhoff','hubs-biased','hub'],
'356756':['progression-free','elsholtz','klahn','lipnik','four-term','4-ap','ap-free'],
'350979':['monophonic','circulant'],
'342414':['convex domination','edge-pattern'],
'359279':['hook tableau','minors','reconstruction conjecture','k+4'],
'365943':['nut graph','nut-graph'],
'365301':['nearest-colour','nearest-color','contact-order','contact order'],
'353203':['power domination','power-domination','tar reconfiguration','token addition'],
'338258':['riordan','odd-kernel','io-decomposable'],
'352827':['kneser','schrijver','stable kneser'],
'338887':['rotor','chip-firing','chipfiring','chan-levine','levine'],
'342364':['binary partition','ulas','zmija','żmija','coloured partition','colored partition'],
'343536':['equitable partition','neuberger','sieben','swift'],
'345545':['stack-sort','stack sort','stacksort','defant','propp'],
'355217':['outer-connected','middle graph','middle-graph'],
'366974':['positive matching','c_3 □','cartesian product of cycles'],
'346167':['rainbow vertex','vertex-disconnection','nordhaus','gaddum','li-weng','li–weng'],
'324342':['conference matrix','mds','etzion','vardy','yaakobi'],
'330264':['geodesic growth','coxeter','ciobanu','kolpakov'],
'354228':['local antimagic','antimagic','full tree'],
'332037':['smyth','composition','injection conjecture','down-set'],
'369421':['word-representab','representation number','toroidal','kitaev','pyatkin','alshammari'],
'365453':['lau-shiu','lau','shiu','join o_2','3p_2'],
'352253':['yy-delta','y-delta','delta-wye','jeffries','yeats','delta minimal'],
}
for mid,ks in KW.items():
    hits=[]
    for f,t in text.items():
        tl=t.lower()
        for k in ks:
            for m in re.finditer(re.escape(k),tl):
                s=max(0,m.start()-70);e=min(len(t),m.end()+70)
                hits.append((os.path.basename(f),k,t[s:e].replace('\n',' ')))
    print(f'== {mid}: {len(hits)} hits')
    seen=set()
    for h in hits:
        key=(h[0],h[2][:60])
        if key in seen: continue
        seen.add(key)
        if len(seen)>6: print('   ...');break
        print('  ',h[0],'[',h[1],']',h[2])
