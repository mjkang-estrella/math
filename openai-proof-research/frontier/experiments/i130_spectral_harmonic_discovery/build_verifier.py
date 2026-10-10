"""Preparation only: construct a single flat verifier; never call an inherited verifier."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i130_spectral_harmonic_discovery';E=ROOT/'frontier/experiments/i130_spectral_harmonic_discovery'
assert not (S/'seal.json').exists()
x=(ROOT/'frontier/experiments/i127_diagonal_pinned_distance/verify.py').read_text()
x=x.replace('Offline read-only I127 replay, derived from the flat I124 verifier;', 'Offline read-only I130 replay, expanded flat from I127;')
x=x.replace("PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'", "PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'\nW=ROOT/'frontier/sources/i130_spectral_harmonic_discovery';WE=ROOT/'frontier/experiments/i130_spectral_harmonic_discovery'")
old=" pre=sys.argv[1:]==['--preseal'];assert not sys.argv[1:] or pre\n"
new=''' own_pre=sys.argv[1:]==['--preseal'];assert not sys.argv[1:] or own_pre
 wi=data(W/'inventory.json');wp=wi['owned_paths'];assert wp==sorted(set(wp))
 wa=files([W,WE])|{'frontier/iterations/i130-spectral-harmonic-discovery.md'}
 ws=wi['seal_path'];wv=rel(WE/'validation.json');wanted=set(wp)
 assert wi['allowed_live_ledger_drift']==LEDGERS and wi['selective_pdf_replay_limit']==0
 if own_pre:
  assert not (ROOT/ws).exists(),'preseal forbidden after final seal'
  if wv not in wa:wanted.remove(wv)
  assert wa==wanted,dict(extra=sorted(wa-wanted),missing=sorted(wanted-wa))
 else:
  assert wa==wanted|{ws},dict(extra=sorted(wa-wanted-{ws}),missing=sorted(wanted-wa))
  wseal=data(ROOT/ws);assert list(wseal['sha256'])==wp
  for p,h in wseal['sha256'].items():assert sha(read(p))==h,('I130 immutable',p)
  wval=data(WE/'validation.json');assert wval['status']=='PASS' and wval['exit_code']==0
 wrefs=data(W/'immutable-references.json')
 assert [r['path'] for r in wrefs]==sorted({r['path'] for r in wrefs})
 for r in wrefs:assert sha(read(r['path']))==r['sha256'],('I130 direct immutable',r['path'])
 assert sha((V/'seal.json').read_bytes())=='d917b10cbe80dfc969c6a3dce949ab6ee5968baa91ef76da01e6f9b3bb4c3cad'
 # I127 itself is an inherited immutable bundle, always sealed, never executed.
 pre=False
'''
assert old in x;x=x.replace(old,new)
x=x.replace("[data(V/'lexical-search.json')];patterns={}","[data(V/'lexical-search.json'),data(W/'lexical-search.json')];patterns={}")
x=x.replace("+[V/'read-manifest.json']:","+[V/'read-manifest.json',W/'read-manifest.json']:")
x=x.replace("for old in [S,V]:", "for old in [S,V,W]:")
x=x.replace("for x in data(V/'html-bindings.json'):", "for x in data(V/'html-bindings.json')+data(W/'html-bindings.json'):")
start=x.index(" print('Entire immutable/corpus/lexical/passage preflight:")
x=x[:start]+''' # Full I130 decoded input, exact originals and all recursively required fields.
 fr=data(W/'input-freeze.json');t=data(ROOT/fr['task130']);t127=data(ROOT/fr['task127'])
 assert sha(read(fr['task127']))=='49dafeac25ffa649bdf42ad11bbcac47f508aa1dd023958cbf3e78d7a7953f77'
 assert t['brief']==(W/'i130-decoded-brief.txt').read_text()
 assert t127['brief']==(W/'i127-decoded-brief.txt').read_text()
 assert {k:v for k,v in t.items() if k!='brief'}==data(W/'i130-other-fields.json')
 assert {k:v for k,v in t127.items() if k!='brief'}==data(W/'i127-other-fields.json')
 check_parts(t['brief'],fr['markers'],fr['parts'],W)
 assert (W/'supplied-original-i127-report.txt').read_text().strip()==read('frontier/iterations/i127-diagonal-pinned-distance.md').decode().strip()
 par=data(W/'supplied-finalized-i127-parent-response.txt')
 assert par==data(W/'snapshots/frontier/experiments/i127-parent-verification.json')==data(ROOT/'frontier/experiments/i127-parent-verification.json')
 assert par['seal_sha256']=='d917b10cbe80dfc969c6a3dce949ab6ee5968baa91ef76da01e6f9b3bb4c3cad'
 for z in par['parent_review']['complete_files']:assert sha(read(z['path']))==z['sha256']
 for z in par['parent_review']['source_reads']:
  bb=read(z['path']);assert sha(bb)==z['sha256'];ll=bb.decode().splitlines()
  for r in z['ranges']:assert sha('\\n'.join(ll[r['start']-1:r['end']]).encode())==r['sha256']
 for z in data(W/'recursive-freeze.json')['records']:
  bb=read(z['path']);assert sha(bb)==z['sha256'];assert list(json.loads(bb))==z['all_fields']
 for z in data(W/'selected-domain.json'):assert z==bypath[z['path']]
 wo=data(W/'overlap-search.json');rx=re.compile(wo['expression']);wr=[]
 for p in wo['paths']:
  for i,l in enumerate(read(p).decode().splitlines(),1):
   mm=list(rx.finditer(l))
   if mm:wr.append(dict(path=p,splitlines_line=i,text=l,spans=[list(m.span()) for m in mm]))
 assert wr==wo['results']
 versions_seen={}
 for n,v in [('huang',1),('lwx',1),('cai-lai',2),('logunov',2),('xu',1),('brustad',1)]:
  versions=[int(z) for z in re.findall(r'<strong>\\[v(\\d+)\\]</strong>',(W/'literature'/(n+'-current.html')).read_text())]
  assert versions and max(versions)==v,('I130 primary version',n,versions)
  versions_seen[n]=v
 print('Entire immutable/corpus/lexical/passage preflight: PASS; diagnostics begin now',file=sys.stderr,flush=True)
 # Only I130 finite instances; no inherited verifier or diagnostic invoked.
 own=runpy.run_path(str(WE/'diagnostics.py'))['check']();assert own==data(WE/'diagnostic-result.json')
 drift=[p for p in LEDGERS if sha(read(p))!=sha((W/'snapshots'/p).read_bytes())]
 print(json.dumps(dict(status='PASS',mode='preseal' if own_pre else 'sealed read-only',owned_files=len(wa),inherited_sealed_artifacts=inherited_count+len(expected),immutable_direct_references=len(wrefs),tree_entries=len(tree),manuscripts=749,original_blob_positions=len(domain),inherited_pdf_text_bindings=pdfs,read_passages=passages,lexical_matched_lines={k:len(v) for k,v in computed.items()},overlap_matched_lines=len(wr),selected_pdf_reextractions=0,primary_versions=versions_seen,immutable_preflight_before_diagnostics=True,recursive_verifiers_invoked=0,inherited_diagnostic_runs='none; checked only as immutable records',new_finite_diagnostics=own['status'],allowed_live_ledger_drift_observed=drift,scope='Evidence reproduction and finite instances only; no universal analysis, fixed-metric infinite-degree theorem, substantiality, human-review or priority certification'),indent=2))
if __name__=='__main__':main()
'''
(E/'verify.py').write_text(x)
print('Flat verifier written; no inherited verifier executed.')
