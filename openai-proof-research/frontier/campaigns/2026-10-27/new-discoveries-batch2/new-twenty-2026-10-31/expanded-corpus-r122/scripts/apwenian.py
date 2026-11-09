import itertools,collections,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];hist=collections.Counter();survivors=[];total=0
words={k:[''.join(w) for w in itertools.product('01',repeat=k)] for k in range(1,7)}
for a in range(2,7):
 for b in range(1,7):
  if a==b:continue
  for one in words[a]:
   if one[0]!='1':continue
   for zero in words[b]:
    total+=1;s='1'
    while len(s)<1025:s=''.join(one if x=='1' else zero for x in s)[:1025]
    c=list(map(int,s));fail0=next((n for n in range(512) if (c[n]-c[2*n+1]-c[2*n+2])%2),None)
    # d=1-2*c is signed with initial -1, globally negating preserves the criterion.
    d=[1-2*x for x in c];fail1=next((n for n in range(512) if (d[n]+d[n+1]-d[2*n+1]-d[2*n+2])%4!=2),None)
    hist[('01',fail0)]+=1;hist[('signed',fail1)]+=1
    if fail0 is None or fail1 is None:survivors.append({'one':one,'zero':zero,'01_pass':fail0 is None,'signed_pass':fail1 is None})
print('unequal-length morphisms',total,'criterion tests each 512','survivors',len(survivors))
out={'scope':'1 image begins 1, length2..6; 0 image length1..6; unequal lengths; both alphabets; first512 necessary criterion equations','morphisms':total,'survivors':survivors,'first_failure_histogram':[[str(k),v] for k,v in hist.items()]};(D/'outputs/apwenian.json').write_text(json.dumps(out,indent=2));print(survivors[:10])
