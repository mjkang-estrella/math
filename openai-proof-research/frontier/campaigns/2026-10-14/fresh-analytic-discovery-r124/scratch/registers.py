import pathlib,json,hashlib,re,shutil
root=pathlib.Path.cwd(); own=root/'frontier/campaigns/2026-10-14/fresh-analytic-discovery-r124'; pkt=own/'packet'; pub=pkt/'public'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
a=json.loads((pub/'canonical.json').read_text()); tree=json.loads((root/'sources/preprints-tree.json').read_text()); entries={x['path']:x for x in tree['tree']}
keep={
'The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026':['tests.tex','scales.tex'],
'The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026':['04-routing.tex','05-scales.tex'],
'Uniform-Permanence-in-Weakly-Reversible-Mass-Action-Systems-October-5-2026':['trapping.tex','permanence.tex'],
'A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026':['foundations.tex','local_bounds.tex','range.tex','iteration.tex'],
'A-continuum-temperature-singularity-for-a-radial-pair-potential-September-24-2026':['model.tex','kac.tex'],
'Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026':['03-scales.tex'],
'Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026':['02-pricing.tex','05-limit.tex']}
ret=[];rem=[]
for x in a:
 p=pkt/x['local']; x['tree_entry']=entries[x['path']]
 if any(k in x['path'] and p.name in v for k,v in keep.items()):
  x['labels_present_not_read_claim']=re.findall(r'\\label\{([^}]+)\}',p.read_text()); ret.append(x)
 else:
  x['status']='removed unused acquisition; not semantic proof evidence'; rem.append(x);p.unlink()
for d in sorted((pkt/'private/canonical').rglob('*'),key=lambda p:len(p.parts),reverse=True):
 if d.is_dir() and not any(d.iterdir()):d.rmdir()
dump(pub/'canonical.json',ret);dump(pub/'removed-acquisitions.json',rem)
hist=[('frontier/iterations/i36-harmonic-analysis-discovery.md','opening source/all-ratio/primary comparison, not full later proof'),('frontier/iterations/i37-supergeometric-avoidance.md','opening through line155; later portions not read'),('frontier/iterations/i141-intermittent-rate-permanence.md','opening and full section2.2; combined later output truncated'),('frontier/iterations/i144-critical-siphon-window-repulsion.md','full section5 plus6 and closing evidence; earlier routes only partial'),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r16/original-scope.md','complete'),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r16/screening-before-freeze.md','complete'),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r33/228-conditioned-comparison.md','complete'),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r33/228-checkpoint.md','complete'),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r121/packet/public/continuum.md','complete; late after feasibility'),('frontier/campaigns/2026-10-14/two-temperature-contribution-r1/review.md','complete; late after feasibility'),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r32/263-working-proof.md','opening sections1-4 and ending6; middle4/5 truncated'),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r119/packet/public/report.md','complete'),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r115/packet/public/operation-comparison.md','149-related actual excerpts only'),('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r115/packet/public/research-report.md','149-related actual excerpts only')]
hr=[]
for i,(name,extent) in enumerate(hist,1):
 p=root/name;q=pkt/'private/history'/f'{i:02d}-{p.name}';shutil.copyfile(p,q);hr.append({'origin':name,'local':str(q.relative_to(pkt)),'sha256':sha(q),'bytes':q.stat().st_size,'extent':extent})
dump(pub/'history-register.json',hr)
cr=[]
for p in (pkt/'private/context').rglob('*'):
 if p.is_file():cr.append({'local':str(p.relative_to(pkt)),'sha256':sha(p),'bytes':p.stat().st_size})
dump(pub/'context-register.json',cr)
ident=[]
for lane,names in {
'fresh-analytic-discovery-r122':['HANDOFF.md','packet/public/report.md','packet/public/nls-geometry.md','packet/public/geometry-and-systems.md','packet/public/ancestry-screens.md','packet/public/reading-limits.md'],
'fresh-analytic-discovery-r123':['HANDOFF.md','packet/public/report.md','packet/public/kohn-sham.md','packet/public/operators.md','packet/public/geometric-screens.md','packet/public/reading-limits.md'],
'fresh-structural-discovery-r117':['packet/public/report.md','packet/public/structural-screens.md','packet/public/online-fairness.md','packet/public/automata.md','packet/public/reading.md'],
'fresh-structural-discovery-r123':['REPORT.md','packet/public/report.md','packet/public/elliptic-feasibility.md','packet/public/stability.md','packet/public/other-screens.md','packet/public/reading-limits.md'],
'fresh-arithmetic-discovery-r80':['packet/public/research.md','packet/public/reading-limits.md'],
'fresh-arithmetic-discovery-r87':['REPORT.md','packet/public/report.md','packet/public/division-limits.md','packet/public/cancellation.md','packet/public/geometric-screens.md','packet/public/modular-and-initial-screens.md','packet/public/reading-limits.md'],
'discovery-analytic-r122-parent':['intake.json'],'discovery-analytic-r123-parent':['intake.json'],'discovery-structural-r123-parent':['intake.json'],'discovery-arithmetic-r87-parent':['intake.json'],
't152ac116-contribution-r1':['review.md','reading-limits.md']}.items():
 for name in names:
  p=root/'frontier/campaigns/2026-10-14'/lane/name;ident.append({'origin':str(p.relative_to(root)),'sha256':sha(p),'bytes':p.stat().st_size,'extent':'complete displayed/read body; linked proofs not implied'})
dump(pub/'recent-context-identities.json',ident)
rr=[]
for name in ['relocation-history.txt','geometric-history.txt','history-files.txt','history-files-broad.txt']:
 p=own/'scratch'/name
 if p.exists():rr.append({'former_location':'scratch/'+name,'bytes':p.stat().st_size,'sha256':sha(p),'lines':sum(1 for _ in p.open('rb')),'reason':'own exploratory raw output removed; final bounded hit records retained; not full-text reconstruction'});p.unlink()
dump(pub/'removed-search-receipts.json',rr)
print(json.dumps({'retained':len(ret),'removed':len(rem),'history':len(hr),'context':len(cr),'recent':len(ident),'removed_raw':rr},indent=2))
