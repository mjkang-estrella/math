from pathlib import Path
import hashlib,json,datetime,re
P=Path(__file__).resolve().parent
hashof=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
(P/'sourcebytes.sha256').write_text(''.join(hashof(f)+'  '+str(f.relative_to(P))+'\n' for f in sorted((P/'sources').glob('*')) if f.is_file()))
logs=[]
for name in ['http.json','http-more.json','http-closest.json','http-final.json','http-final-delta.json']:
 if (P/name).exists():logs.extend(json.loads((P/name).read_text()))
# Explicitly screen final actual-body delta, preserve the broader baseline screen as separate evidence.
term=re.compile(r'super.?dominat|super.?domatic|Kov.cs|2305.05632|2505.24072|1705.00928|avoider|Vizing|forcing.?sizes',re.I)
delta=[]
for f in sorted((P/'sources').glob('omega-final-body-*')):
 s=f.read_text(errors='replace');delta.append(dict(file=str(f.relative_to(P)),sha256=hashof(f),hits=[l[:1000] for l in s.splitlines() if term.search(l)]))
(P/'final-delta-screen.json').write_text(json.dumps(delta,indent=2))
prov=dict(lane='sol-fresh-source-discovery-r99',finalized_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='UNRESOLVED',credit=0,counts=dict(additional=8,total=38),full_result=False,proof_file=False,source_claims=[dict(authors='Klein, Rodríguez-Velázquez, Yi',label='Journal Conjecture2, p93; arXiv v2 Conjecture25',scope='All finite simple G,H: gamma_sp(G square H)>=gamma_sp(G) gamma_sp(H)',file='sources/super-vor.pdf'),dict(authors='Kovács, Nagy; repeated by Kovács',label='2305.05632v3 Conjecture1.11 / 2505.24072v1 Conjecture1.1',scope='Every fixed k>=1, 0<=t<=2^k: binary affine forcing-cardinality density tends to1',file='sources/finite-original.html')],source_acquisition=logs,source_hash_file='sourcebytes.sha256',all_date_duplicate_audit='duplicate-audit.json',context='context-read.json',bounded_checks='check-results.json',math_gap='Need uniform p(G)p(H) correction to separate private-witness row/column budgets; no full proof or actual graph counterexample',strongest_objection='Eight disjoint tokens satisfy all separate budgets and half-order bound but violate desired correction; this is only a relaxation obstruction',novelty_holds=['No full new mathematical result','Older intermediate registry chain inherited, not independently re-body-cleared for these fresh claims','Graph enumeration successor journal comparison unavailable; v3 primary body read','Finite geometry journal/classical full comparison incomplete'],registries=dict(omega_initial='49444ed17a62b3b1e64dd3a79cbeeb6ecfe6867d',omega_final='9aef67a59dec08d1ff04a18a3d23560525ab023d',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',new_deltas=[dict(commits=3,files=191,base='28414a3d55d5b97458b138701407d5678e167a8e'),dict(commits=1,files=23,base='49444ed17a62b3b1e64dd3a79cbeeb6ecfe6867d')]),constraints=dict(solo=True,writes_only_lane=True,git_operations=False,external_mutations=False,mmpp_investment=False,lean=False,paper=False,guard=dict(address_space_mib=512,group_rss_mib=512,cpu_seconds=210,wall_seconds=230,sampling_ms=40,blas_threads=1)),failures=['bs4 unavailable','networkx unavailable','g++ unavailable','Journal repository HTTP500; distinct arXiv primary successor obtained'])
(P/'provenance.json').write_text(json.dumps(prov,indent=2))
(P/'manifest.sha256').write_text(''.join(hashof(f)+'  '+str(f.relative_to(P))+'\n' for f in sorted(P.rglob('*')) if f.is_file() and f.name!='manifest.sha256'))
print('Finalized',len(list((P/'sources').glob('*'))),'source files; final delta hits',sum(bool(x['hits']) for x in delta))
