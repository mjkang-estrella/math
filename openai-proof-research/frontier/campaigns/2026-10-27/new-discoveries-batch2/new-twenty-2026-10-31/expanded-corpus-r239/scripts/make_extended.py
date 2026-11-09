import pathlib
D=pathlib.Path(__file__).resolve().parents[1]
s=(D/'scripts/latin.py').read_text();s=s.replace('rows=[]','rows=[]\npatterns={"a":["10"]*3,"b":["10","11"],"c":["10","101"],"d":["10","1010"],"f":["1110"],"g":["10101"],"h":["101010"]}\ncases=[(family,k) for k in range(1,7) for family in patterns]')
s=s.replace('for n in [9,10,11,12,14,16]:','for family,k in cases:\n words=patterns[family]+["00"]*(k+(family in "bcfg")); n=sum(map(len,words))\n if n<9:continue\n marks=[];perm=[];offset=0\n for word in words:\n  marks.extend(offset+i for i,c in enumerate(word) if c=="1");perm.extend(offset+(i+1)%len(word) for i in range(len(word)));offset+=len(word)\n order=marks+[i for i in range(n) if i not in marks];inv={v:i for i,v in enumerate(order)};second=[inv[perm[v]] for v in order]')
s=s.replace('range(100):','range(150):').replace('time.monotonic()-start>100','time.monotonic()-start>105')
a=s.index('  while True:');b=s.index('  p[1]=s[:]',a);s=s[:a]+'  s=second[:]\n'+s[b:]
s=s.replace("{'n':n,'generated'","{'family':family,'k':k,'n':n,'generated'")
s=s.replace('latin-search.json','latin-reduced-search.json').replace('latin-obstruction-diagnostic.json','latin-reduced-obstruction-diagnostic.json')
(D/'scripts/latin_reduced.py').write_text(s)
s=(D/'scripts/cyclic.py').read_text().replace('import pathlib,json,time,random,sys','import pathlib,json,time,random,sys,itertools')
s=s.replace('for k in [3,4,5]:','for k in [3]:').replace('for sample in range(2000):','for sample,extra in enumerate(itertools.combinations(range(n-k,N),k)):').replace('rng.sample(range(n-k,N),k)','extra').replace('cyclic-search.json','cyclic-exhaustive-prefix.json').replace('cyclic-witness.json','cyclic-exhaustive-witness.json').replace('random A coverage, not exhaustive A enumeration.','Lexicographic A prefix; see samples_attempted for exact prefix endpoint (last iteration may be untested at wall cutoff).')
(D/'scripts/cyclic_prefix.py').write_text(s)
