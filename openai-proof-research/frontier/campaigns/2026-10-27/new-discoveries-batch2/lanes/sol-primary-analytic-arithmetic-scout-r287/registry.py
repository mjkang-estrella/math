exec(open(__file__.replace('registry.py','work.py')).read().split("if __name__")[0])
R=Path('openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing')
terms=re.compile(r'Cs[oó]rd[aá]s|Forg[aá]cs|1505.00355|complex.zero.decreas|CZDS|Pochhammer|2312.07754|Karlovych|Shargorodsky|2308.04072|2312.09482|2303.00699|2307.06787|2304.10570|1511.08080|1408.0142|1407.2380|1512.02975|0010143|Onsager|Krull.monoid',re.I)
files=list((R/'Problems').glob('*.md'))+list((R/'D5').rglob('*.lean'))
for lane in L.parent.iterdir():
 if lane==L:continue
 for name in ['SUMMARY.md','SCOUTING.md','discovery.md']:
  if (lane/name).is_file():files.append(lane/name)
hits=[];refs=[]
for p in files:
 if p.stat().st_size>1500000:continue
 d=p.read_bytes();digest=h(d);refs.append(dict(path=str(p.resolve()),sha256=digest))
 # Reuse existing immutable registry references; freeze matching scientific bodies before displaying.
 ms=list(terms.finditer(d.decode(errors='replace')))
 if ms:
  q=freeze(p);s=q.read_text(errors='replace');hits.append(dict(path=str(p.resolve()),sha256=digest,excerpts=[s[max(0,m.start()-150):m.end()+600] for m in ms[:5]]))
 assert h(p.read_bytes())==digest
(L/'registry-references.json').write_text(json.dumps(refs,indent=2));(L/'registry-hits.json').write_text(json.dumps(hits,indent=2))
print('scanned',len(refs),'hits',len(hits))
for x in hits:print(x['path'],x['excerpts'][:2])
for name,url in [('registry-current.html','https://github.com/the-omega-institute/trureturing'),('openai-current.html','https://github.com/openai/math')]:fetch(name,url)
for name in ['czds-search.html','q-search.html','registry-current.html','openai-current.html']:
 p=L/'primary'/name
 if not p.exists():continue
 s=freeze(p).read_text();print(name,'HEAD',re.findall(r'"currentOid":"([a-f0-9]+)"',s)[:2])
 for b in s.split('<li class="arxiv-result">')[1:]:
  a=re.search(r'arxiv.org/abs/([^"<]+)',b);t=re.search(r'<p class="title is-5 mathjax">(.*?)</p>',b,re.S)
  if a and t:print(a.group(1),re.sub('<[^>]+>','',t.group(1)).strip())
