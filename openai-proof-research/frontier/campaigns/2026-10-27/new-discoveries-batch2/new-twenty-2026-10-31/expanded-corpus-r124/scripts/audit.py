import pathlib,json,hashlib,re,datetime
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
# Preserve read-only campaign state summaries; these are historical counts, not current credit.
a=[]
for p in [B/'ledger.json',B/'prior-campaign-context.json',D.parent/'ledger.json']:
 o=json.loads(p.read_text());a.append(dict(path=str(p),sha256=sha(p.read_bytes()),root_keys=list(o),accepted=o.get('accepted'),excluded=o.get('excluded'),note='Read-only historical input; does not change campaign counts.'))
(D/'outputs/campaign-inputs.json').write_text(json.dumps(a,indent=2))
x=json.loads((D/'extracted.json').read_text());v=json.loads((D/'outputs/versions.json').read_text());patterns={'1901.06771':'Conjecture 3.24','1901.10886':'Theorem 12.1','1903.10613':'Conjecture 1.3','1904.01146':'Conjecture 7.3','1904.04071':'Conjecture 4.','2007.14115':'Conjecture 7.2','2008.08110':'Conjecture 7.4','2008.12871':'select N','2008.13475':'Conjecture 5.8','2009.01024':'Möbius','2009.07918':'Conjecture 4.3','2010.08023':'Conjecture 1.3','2011.08874':'As stated','2011.09568':'Conjecture 2.5','2011.12822':'Conjecture 1.','2012.00341':'Conjecture 6.1','2012.06160':'Conjecture 3.4','2107.05110':'Conjecture I.2'}
out={}
for a,vs in v.items():
 out[a]=[]
 for z in vs:
  p=D/'sources'/f'{z}.txt';s=p.read_text();lines=s.splitlines();needle=patterns[a];hits=[i for i,l in enumerate(lines) if needle in l];ix=set()
  for i in hits:ix.update(range(max(0,i-3),min(len(lines),i+15)))
  passage='\n'.join(f'{i+1}: {lines[i]}' for i in sorted(ix));(D/'outputs'/f'{z}-target.txt').write_text(passage)
  out[a].append(dict(version=z,pdf_sha256=sha(p.with_suffix('.pdf').read_bytes()),text_sha256=sha(p.read_bytes()),locator=needle,hits_1based=[i+1 for i in hits],passage=passage))
(D/'outputs/version-review.json').write_text(json.dumps(out,indent=2,ensure_ascii=False))
# Fixed-string initial history screening can match digits inside hashes; retain only exact IDs/titles.
pat=re.compile(r'(?<!\d)(?:'+'|'.join(x)+r')(?!\d)');titles=[o['title'].lower() for o in x.values()]
lines=[l for l in (D/'history-matches.txt').read_text().splitlines() if pat.search(l) or any(t in l.lower() for t in titles)]
(D/'outputs/history-exact.txt').write_text('\n'.join(lines)+'\n')
manifest=[]
for p in sorted((D/'sources').glob('*')):
 if p.is_file():manifest.append(dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes())))
(D/'outputs/source-manifest.json').write_text(json.dumps(manifest,indent=2))
print('All versions',sum(map(len,v.values())),'exact historical matches',len(lines))
for a,rows in out.items():print(a,[(r['version'],r['hits_1based']) for r in rows])
