import json,re,pathlib,hashlib,datetime
ids=json.load(open('reservation.json'))['ids'];o={}
for p in pathlib.Path('sources').glob('omega-*.json'):
 j=json.load(open(p));paths=[x['path'] for x in j.get('tree',[])];hits=[s for s in paths if any(str(i) in s for i in ids) or re.search('positive.match|cartesian|shareshian|pseudoperiod|steady.word|dihedral|harmonious|cnat',s,re.I)]
 o[p.name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'truncated':j.get('truncated'),'paths':len(paths),'hits':hits}
p=pathlib.Path('../fresh-corpus-r10/sources/registry-preprints.json');j=json.load(open(p));o['openai_cached_listing']={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'note':'HEAD unchanged; path screen only','matching_text':[line for line in p.read_text().splitlines() if re.search('shareshian|elementary|matching|dihedral|cartesian',line,re.I)]}
json.dump(o,open('outputs/registry-screen.json','w'),indent=2);print(json.dumps(o,indent=2))
# Stop old historical exclusion routes, not mere mentions.
p=pathlib.Path('../expanded-corpus-r81/results.json');j=json.load(open(p)); hits={k:v for k,v in j.items() if k in map(str,ids)};json.dump(hits,open('outputs/historical-matching-results.json','w'),indent=2);print('history IDs',list(hits))
# Word diagnostics independently validate all recorded witnesses.
a=json.load(open('outputs/pseudo.json'));print('pseudo',len(a),'found',sum(x['found'] for x in a));
for r in a:
 if not r['found']:continue
 s=r['word'];a1,b=r['a'],r['b'];assert all(s[i] in (s[i+a1],s[i+b]) for i in range(len(s)-b))
 for p1 in range(1,(len(s)-1)//3+1):
  assert all(s[i:i+2*p1+1]!=s[i+p1:i+3*p1+1] for i in range(len(s)-3*p1))
print('pseudo witnesses independently checked')
