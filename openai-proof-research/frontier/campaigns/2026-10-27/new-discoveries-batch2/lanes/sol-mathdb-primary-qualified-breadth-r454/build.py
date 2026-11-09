import pathlib,json,hashlib,datetime,re
L=pathlib.Path(__file__).resolve().parent;B=L.parent;I=B/'root-mathdb-breadth-intake-r453'
def j(p):return json.loads(p.read_text())
def dump(n,x):(L/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def h(b):return hashlib.sha256(b).hexdigest()
R=j(L/'assigned-records.json');a={int(t[0]):t[1:] for t in (s.split('\t') for s in (L/'assessment.tsv').read_text().splitlines())};assert len(a)==50
P=j(L/'source-provenance.json')
# Restore late HTML provenance lost by overlapping initial HTML/PDF metadata writers.
# No refetch: UTC is retained-file modification time; the successful route is in fetch.log.
known={r.get('path') for r in P}
for p in sorted((L/'sources').glob('*.html')):
 if 'sources/'+p.name not in known:
  P.append(dict(url='https://ems.press/journals/owr/articles/'+p.stem,path='sources/'+p.name,status=200,utc=datetime.datetime.fromtimestamp(p.stat().st_mtime,datetime.timezone.utc).isoformat(),utc_basis='retained file mtime; route success in fetch.log; original response metadata overwritten by concurrent writer',version='published publisher page at retained-file UTC',sha256=h(p.read_bytes()),bytes=p.stat().st_size))
for p in sorted((L/'sources').glob('*.txt')):
 P.append(dict(path='sources/'+p.name,sha256=h(p.read_bytes()),bytes=p.stat().st_size,derived_from='sources/'+p.stem+'.pdf',method='pdftotext -layout; extraction is not layout/proof-dependency verification'))
dump('source-provenance.json',P)
D=[]
for x in R:
 r=x['record'];i=r['mathdb_id'];s,obs,prior=a[i];name=r['source_url'].split('/')[-1];assert (L/'sources'/(name+'.pdf')).exists()
 D.append(dict(mathdb_id=i,title=r['title'],literal_statement=r['statement'],statement_utf8_sha256=h(r['statement'].encode()),canonical_record_sha256=x['canonical_record_sha256'],original_chunk=x['original_chunk'],original_line=x['original_line'],disposition=s,scope_and_quantifiers=r['statement'],full_scope_mechanism_or_obstacle=obs,source_internal_check=prior,source_level=dict(level='PRIMARY_REPORT_PASSAGES',url=r['source_url'],version=r['source_name'],retained_pdf='sources/'+name+'.pdf',retained_text='sources/'+name+'.txt',report_context='primary-sections.json',limitation='Relevant passages and neighboring context read; full report bodies and proof dependencies not exhaustively audited.'),closest_successor_check=dict(level='HOLD_NOT_COMPLETED',checked='Primary report contemporaneous references and source-internal results only.',gap='No independent closest-successor full-body audit; no claim of current unsolved status or literature novelty. Must complete before investment.'),proof_level='NO_NEW_FULL_SCOPE_PROOF',registry_level='HOLD_429_ZERO_MATHDB_REQUESTS',bounded_check=dict(status='NOT_RUN',reason='No candidate warranted finite computation after source/definition gate; no bounded evidence counted as full-scope proof.'),certificate=dict(status='NONE',size_bytes=0,formal_dependencies='None implemented; no Lean run.',decisive_calculation_executed='None',decisive_calculation_planned='None authorized for investment after this triage.'),strongest_objection=obs,novelty_gaps=['Report passage checks do not audit referenced proofs.','Closest-successor full bodies not independently audited.','Live registry is unavailable by instruction; metadata open status is not evidence.'],credit=0))
dump('dispositions.json',D);dump('proposals.json',[])
print('dispositions',len(D),'primary reports',len(list((L/'sources').glob('*.pdf'))))
print('coverage entries',len(j(I/'coverage-delta.json')),'first',str(next(iter(j(I/'coverage-delta.json').values())))[:750])
