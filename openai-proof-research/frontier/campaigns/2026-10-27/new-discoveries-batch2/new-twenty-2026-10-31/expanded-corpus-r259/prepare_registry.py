import pathlib,re,json
L=pathlib.Path(__file__).resolve().parent; B=L.parent
head=re.findall(r'"oid":"([0-9a-f]{40})"',(L/'omega-head.html').read_text())[0]
paths=['D5/S0/Certificates/ChapotonConjectureFiveFourRefutation.lean','D5/S0/Certificates/ChapotonPropositionFiveTwoRefutation.lean','D5/S1/Words/Episturmian/BoundedPowers.lean','D5/S1/Words/Episturmian/DiophantineExponentCriterion.lean','D5/S1/Words/Episturmian/MorphicDecomposition.lean']
jobs=[('omega-'+p.rsplit('/',1)[-1],'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/'+p) for p in paths]
s=(L/'fetch_targets.py').read_text();start=s.index('jobs=');end=s.index('\ndef get',start)
(L/'fetch_registry.py').write_text(s[:start]+'jobs='+repr(jobs)+s[end:])
print('HEAD',head)
for p in ['omega','openai','pool']:
 text=(L/(p+'-head.html')).read_text(); print(p,re.findall(r'"oid":"([0-9a-f]{40})"',text)[:1])
