exec(compile((__import__('pathlib').Path(__file__).parent/'research.py').read_text().split("if sys.argv[1]=='extract':")[0],__file__,'exec'))
r=json.loads((L/'results.json').read_text());x=r['371534'];x['outcome']='excluded_public_routine_refutation';x['ordinary_route_or_gap']='Public arXiv:2610.17135v1 Corollary D disproves ordinary and augmented Chow real-rootedness. Interlacing in the literal real-rooted sense implies real-rootedness of both polynomials; choose a counterexample lattice and any atom to refute the universal conjunction. This is a routine public bridge, zero credit.';x['reviewed_source_files'].append('sources/3448b2724c3572ed.bin');x['gates']=dict(scope='full conjunction refuted via public non-real-rooted Chow polynomial',source='primary Conjecture8.5 and comparator TheoremA,TheoremC,CorollaryD/proof read; full comparator construction proofs not audited',prior_art='positive public comparator, v1 submitted2026-10-12',subsumption='routine implication interlacing => real-rootedness',novelty='FAIL: complete routine public bridge',significance='no new eligible result');
for id,x in r.items():x['history']='history-source-family-matches.json; exact completed allowlist reconciliation only'
js('results.json',r)
add='''\n## 371534: public real-rootedness obstruction, zero credit\n\nThe completed r318 result for neighboring 371532 identified Bérczi–Coron–Eur–Li, arXiv:2610.17135v1. Fresh GET of its actual body and version page confirms v1 submitted October 12, 2026, and Corollary D states that both ordinary and augmented Chow real-rootedness conjectures are false. Its proof derives non-log-concavity from Theorems A and B, then applies Newton inequalities. Theorem A states that a strict failure of log-concavity in multichain counts propagates to Chow and augmented Chow polynomials of sufficiently large direct sums. Theorem C gives additional explicit simple rank-seven examples for its underlined Chow notation. No identification of underlined versus non-underlined notation is needed for this deduction: Corollary D refutes both types.\n\nThe literal interlacing relation is a relation between real-rooted polynomials. Let M be a public non-real-rooted ordinary Chow counterexample, simplify M if necessary (the polynomial and geometric lattice depend on its flats), and take the corresponding geometric lattice L. It has positive rank and an atom a. If the all-lattice interlacing conjecture were true, H_[a,1] would interlace H_L, forcing H_L real-rooted, a contradiction. The augmented assertion is not needed to refute their conjunction. Thus the reserved universal claim has a complete routine earlier-theorem obstruction, with zero novelty credit. This does not manufacture a new explicit finite certificate or solve a narrower nonstandard relation on non-real roots.\n\nRead depth: actual comparator Theorem A, Theorem C, Corollary D and its short proof; NOT the full construction/discriminant proofs or all figures. The exact public theorem is sufficient to block duplicate research credit; this is not a new fully audited proof package. No Pi plan.\n\nHistory reconciliation additionally found the same-source r303/363750 vanishing conjecture and r308/371744 iterated bridge-sum conjecture. Their generator-word and scheduling gaps agree with the limits above and supply no clearance for this reservation.\n'''
put('ORDINARY-ATTEMPTS.md',(L/'ORDINARY-ATTEMPTS.md').read_text()+add)
put('BRIEF.md',(L/'SUMMARY.md').read_text())
inv=json.loads((L/'read-inventory.json').read_text());rr=json.loads((L/'http-receipts.json').read_text())
for v in rr:
 if v.get('file') in ['sources/3448b2724c3572ed.bin','sources/7cb1868a567a9e78.bin']:inv.append(dict(**v,assigned_ids=[371534],read_depth='selected comparator theorem statements and CorollaryD proof; version history',entire_paper_read=False))
js('read-inventory.json',inv)
# Clean false-copy history and preserve compact exact source-family reconciliation only.
h=json.loads((L/'history-source-family-matches.json').read_text());compact=[]
for v in h:
 e=v['entry'];compact.append(dict(path=v['path'],mathdb_id=e.get('mathdb_id'),title=e.get('title'),source_url=e.get('source_url'),outcome=e.get('disposition'),conclusion=e.get('ordinary_attempt_and_gap',e.get('ordinary_attempt_or_explicit_reduction',e.get('ordinary_attempt_and_gap_or_explicit_exclusion')))))
js('history-source-family-matches.json',compact)
# Reservation check once more at final artifact stage.
b=(L/'reservation.json').read_bytes();assert sha(b)=='ab63294346f390bf78bcc2d397633033015ee2d02309951704733213755fef91';assert set(map(int,r))==set(json.loads(b)['ids']) and len(r)==20
receipt()
# manifest only resolves/globs this assigned lane; no symlinks or outside paths.
exclude={'artifact-manifest.json','manifest-verification.json'};entries=[]
for p in sorted(L.rglob('*')):
 assert not p.is_symlink()
 if p.is_file() and p.name not in exclude:
  assert p.resolve().is_relative_to(L);b=p.read_bytes();entries.append(dict(path=str(p.relative_to(L)),bytes=len(b),sha256=sha(b)))
js('artifact-manifest.json',entries)
for e in entries:
 b=(L/e['path']).read_bytes();assert len(b)==e['bytes'] and sha(b)==e['sha256']
js('manifest-verification.json',dict(manifest_sha256=sha((L/'artifact-manifest.json').read_bytes()),verified_artifacts=len(entries),exact_results=20,reservation_sha256=sha((L/'reservation.json').read_bytes()),excluded=sorted(exclude),exit=0,live_jobs=0,credit=0,campaign='52/60',limit='manifest does not self-hash; verifier receipt excluded to avoid circularity'))
print('Verified',len(entries),'artifacts, exact20; no candidate; credit0;52/60')
