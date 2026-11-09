import pathlib,hashlib,json,stat
O=pathlib.Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r125');P=O/'packet'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'public/FROZEN-SCOPE.md')=='ec09396badbea0351a0eb2f8bdb7b780e1d74ffdace92bb04114cccdc5be4a22'
files={};dirs={'.':stat.S_IMODE(P.stat().st_mode)}
for p in sorted(P.rglob('*')):
 r=p.relative_to(P).as_posix();s=p.lstat()
 assert not p.is_symlink()
 if p.is_dir():dirs[r]=stat.S_IMODE(s.st_mode)
 elif r!='MANIFEST.json':files[r]={'sha256':H(p),'bytes':s.st_size,'mode':stat.S_IMODE(s.st_mode)}
m={'version':1,'files':files,'directories':dirs};(P/'MANIFEST.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n');mh=H(P/'MANIFEST.json')
(O/'REPORT.md').write_text('''# r125 local handoff: T238B125

A complete author proof at the unchanged full frozen scope is available in [packet/public/proof.md](packet/public/proof.md). It establishes, relative to the stipulated source238 conditional moment input, an upper bound C_delta(d²+d log(1/epsilon)) for full-deck mixing with every deterministic independent swap-probability array in [delta,1-delta]. All dimensions, errors and later times are included. The homogeneous-bias quadratic lower bound is credited to r113.

See [public report](packet/public/report.md), [operation comparison](packet/public/comparison.md), [exact scope](packet/public/FROZEN-SCOPE.md) and [reading limits](packet/public/reading-limits.md). The selected-record disintegration and shrinking-segment analytic transfer are written in full. Their contribution is NOT self-certified; a reviewer may find the stronger existing contracts pay the whole deduction routinely. Independent proof/contribution reviews have not occurred. No gate, acceptance or count is assigned. Publication remains STOPPED; parent integrates.

Private evidence/metadata remain under original rights and must not be publicly integrated. Only this owned directory was written; no nested agents, git mutations, shared edits, browser UI, contacts, uploads, downstream formal/manuscript/release work occurred.

Frozen scope SHA256: ec09396badbea0351a0eb2f8bdb7b780e1d74ffdace92bb04114cccdc5be4a22.
Manifest SHA256: '''+mh+'''.

The detached FINAL and this outside report SHA256 must be supplied to the own read-only verifier. Copied-control receipts and their detached hashes are outside packet and supplied separately. Finite/integrity checks authenticate only their stated finite identities or bytes; they are not mathematical gates. The complete canonical tree is checked at its fixed hash, all39 FULL acquisition records are retained,19 source bodies and five successful primary pairs remain, and the failed Jonasson version is recorded. Late readings are disclosed, not backdated.
''')
f={'version':1,'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','manifest_sha256':mh,'manifest_mode':stat.S_IMODE((P/'MANIFEST.json').stat().st_mode),'report_sha256':H(O/'REPORT.md'),'payload_anchors':{k:H(P/k) for k in ['public/report.md','public/FROZEN-SCOPE.md','public/proof.md','public/verify.py','public/controls.py','public/prefreeze.md']},'mathematical_gate':False,'contribution_gate':False}
(O/'FINAL.json').write_text(json.dumps(f,indent=2,sort_keys=True)+'\n')
print(json.dumps({'finalhash':H(O/'FINAL.json'),'reporthash':H(O/'REPORT.md'),'manifest':mh,'files':len(files),'dirs':len(dirs)},sort_keys=True))
