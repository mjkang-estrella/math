import pathlib,json,hashlib,re
D=pathlib.Path(__file__).resolve().parents[1];R=D.parent
pat=re.compile('|'.join(str(i) for i in json.loads((D/'reservation.json').read_text())['ids'])+'|signed.cardinality|face.transitive Klein|perfectly divisible|glued.poset|Saxl hypergraph',re.I)
paths=[R/'ledger.json',R.parent/'ledger.json',R.parent/'prior-campaign-context.json']
paths+=list(R.glob('expanded-corpus-r*/SUMMARY.md'))+list(R.glob('expanded-corpus-r*/CANDIDATE.md'))
out=[]
for p in paths:
 if p.is_file() and D not in p.parents:
  for n,l in enumerate(p.read_text().splitlines(),1):
   if pat.search(l):out.append({'path':str(p),'line':n,'text':l})
(D/'outputs/history-full.json').write_text(json.dumps(out,indent=2));print('matches',len(out))
