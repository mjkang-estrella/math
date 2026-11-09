import pathlib,json,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1]; B=D.parent.parent
out={}
for p in [B/'ledger.json',B/'prior-campaign-context.json',D.parent/'ledger.json']:
 b=p.read_bytes();o=json.loads(b);out[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'keys':list(o),'data':o}
(D/'outputs/inherited-context.json').write_text(json.dumps(out,indent=2)+'\n')
print('Read full JSON data for',[(str(p),len(v['data'].get('accepted',[])),len(v['data'].get('excluded',[]))) for p,v in out.items()])
R=D.parent/'chanlevine-parent-final-r1/registries';screen=[]
pat=re.compile('palindrom|modular.*(index|color)|modk|traceab|breadthcritical|irregular|chromaticcut|voronoi|connectedmatching|mondrian|reedwood|2regular|majority|reconstruct|pseudocircle|debruijn|avoidable|kantekwon|steiner|contactnumber|outbranching|flowcount|linearhadwiger|equitable',re.I)
for name in ['omega-D5.body','omega-Problems.body','openai-tree.body']:
 p=R/name;b=p.read_bytes();o=json.loads(b);paths=[x['path'] for x in o.get('tree',[])];matches=[x for x in paths if pat.search(re.sub('[^a-zA-Z0-9]','',x))];screen.append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'truncated':o.get('truncated'),'tree_entries':len(paths),'matches':matches})
(D/'outputs/registry-screen.json').write_text(json.dumps(screen,indent=2)+'\n')
for x in screen:print(x['path'],x['truncated'],x['tree_entries'],len(x['matches']));print('\n'.join(x['matches'][:25]))
# Filter accidental numeric matches from first broad screen. No novelty claim from absence.
text=(D/'history-matches.txt').read_text();ids=json.loads((D/'reservation.json').read_text())['ids'];good=[]
for l in text.splitlines():
 if any(re.search(r'(?<!\d)'+str(i)+r'(?!\d)',l) for i in ids) and len(l)<10000:good.append(l)
(D/'outputs/history-filtered.txt').write_text('\n'.join(good)+'\n')
print('Historical bounded matches',len(good))
