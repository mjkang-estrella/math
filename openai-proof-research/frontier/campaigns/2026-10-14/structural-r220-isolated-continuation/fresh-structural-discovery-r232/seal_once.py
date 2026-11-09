from pathlib import Path
import hashlib,json,shutil,os,subprocess,datetime
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r232')
S=R/'selected'
assert not (S/'MANIFEST.json').exists() and not (S/'FINAL.md').exists() and not (R/'DETACHED-ANCHORS.json').exists(), 'This research selection may be sealed only once.'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(R/'FROZEN-STATEMENT.md')=='9e57e9fcd07c3653bc8568c05f4e1ba57cf4ae56bd58f7b38a087b08ee7e1e68'
assert sha(S/'author/FROZEN-STATEMENT.md')==sha(R/'FROZEN-STATEMENT.md')
assert sha(S/'author/AUTHOR-PROOF.md')==sha(R/'AUTHOR-PROOF.md')
shutil.copyfile(R/'tiny-control-results.json',S/'private/evidence/tiny-control-results.json')
selection=json.loads((R/'selection-preseal-private.json').read_text())
p=S/'private/evidence/tiny-control-results.json'
selection.append({'path':p.relative_to(S).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p),'mode':'0400','rights':'original artifact-control record; private/local'})
selection.sort(key=lambda x:x['path'])
dirs={'.':'0500'}
for e in selection:
 p=S/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'];p.chmod(0o400)
 for d in Path(e['path']).parents:
  dirs[d.as_posix()]='0500'
manifest={'schema':'r232-owned-exact-selection-v1','root':'selected','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','selection':'This exact own selection only; no inherited manifest or mathematical grade','files':selection,'directories':dict(sorted(dirs.items())),'detached':['FINAL.md','MANIFEST.json','../REPORT.md'],'rights':'All private input bodies and named metadata remain local under original rights. Original author prose/code is separate under author/ and code/; nothing is published.'}
(S/'MANIFEST.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
msha=sha(S/'MANIFEST.json');psha=sha(S/'author/AUTHOR-PROOF.md');ssha=sha(S/'author/FROZEN-STATEMENT.md')
final=f'''# r232 selected author-proof packet

Outcome: one full author-proof nominee, r232-Q, at the unchanged frozen statement. No self-assigned correctness, contribution, acceptance or count. Parent alone integrates and reviews.

The normalized theorem bounds every prescribed point-on-side squared-distance deficit by 22(Bδ)^(p/(p+3n)), with B=5·4096^(n/p)/((3−n/p)v^(1/p)), under all hypotheses in author/FROZEN-STATEMENT.md. It includes every minimizing side and degenerate triangles. The author proof and compatible smooth family are in author/.

Frozen statement SHA256: {ssha}
Author proof SHA256: {psha}
MANIFEST SHA256: {msha}

All source operations are paid; the proposed addition is the explicit quantitative radial-defect/endpoint-stability/transport-averaging argument. Formal support is absent: the accessed Lean declaration ends with sorry. Reading and original-history limitations, accidental exposures, version limits and late control rereads are preserved in author/READING-SCOPE.md and private/evidence/. No intended mathematical bridge is left unproved in the author submission; independent adversarial correctness and contribution reviews have not occurred.

This exact packet is sealed once. The detached FINAL, MANIFEST and outside REPORT hashes are in ../DETACHED-ANCHORS.json. Artifact checks concern bytes, modes and exact selection only.
'''
(S/'FINAL.md').write_text(final);fsha=sha(S/'FINAL.md')
report=f'''# Structural discovery r232 — author-proof handoff

One full author-proof nominee is submitted at its unchanged frozen scope: [r232-Q](selected/author/FROZEN-STATEMENT.md), with [complete author proof](selected/author/AUTHOR-PROOF.md). Authorized provenance is Codex / GPT-6 Astra / xhigh / default service tier. Campaign19/20 and latestR041 are the supplied campaign context; no result is counted here.

The theorem assumes integer n≥3, n/3<p<∞, exact reference measure H_d^n, completeness, full support, unreduced RCD(0,n), a uniform local lower ball-volume bound v r^n, and a continuous global sectional defect 0≤ρ≤1 in Gigli's original global test classes. With δ=||ρ||_Lp(B_3(o)), it bounds the squared-distance point-on-side deficit of every chosen minimizing side of every triangle in B_1(o) of perimeter≤1 by 22(Bδ)^(p/(p+3n)), where B=5·4096^(n/p)/((3−n/p)v^(1/p)). The exact statement includes degenerate triangles and zero defect.

The strongest integrated construction was carried out: source characterization gives coarse CBB(−1); its full heat-index, trace, frame and countable-trial operations retain the variable defect; radial contraction gives an explicit Lp bound; upper-semicontinuous representatives and the full companion control every path; explicit hyperbolic endpoint stability and compressed endpoint-ball transports give the rate. A localized smooth metric perturbation on S²×S² verifies nonvacuity, negative sectional curvature, Ricci≥0, exact measure and uniform noncollapse. These established source/classical steps are not separately nominated. The proposed quantitative combination awaits the parent's contribution assessment.

There is no intentionally unproved conditional bridge in the author proof. Independent correctness and contribution reviews remain outstanding, and no correctness, contribution, acceptance or count is assigned. No sharpness, Gromov–Hausdorff approximation, arbitrary measurable-defect, weighted-measure, collapsed-limit, or noncomplete extension is claimed. The [compatibility calculation](selected/author/COMPATIBILITY.md), [prefreeze calculations](selected/author/PREFREEZE.md), and [reading scope](selected/author/READING-SCOPE.md) preserve the actual scope and limits.

All22 canonical blobs were authenticated against the complete pinned tree; all operative source sections, nested figure, macros, comparisons and both bibliographies were read. Actual primary proof sections were read in12 exact accessed PDFs. Some cited intermediates remain unread; extraction limits and accidental editorial/next-section exposures are explicit. GRS v2 returned404 before v1 succeeded; the online AKP version is not claimed to match an earlier date. Two prospectively guarded, precise original-history searches returned no admitted sections, which establishes no exhaustive absence or priority. No excluded peer or closed body was read or reused. The exact Lean endpoint and linked declaration were inspected; its final theorem has sorry, so no proved formal support is claimed.

The selection contains {len(selection)} files plus detached FINAL and MANIFEST, totaling {sum(e['bytes'] for e in selection)} selected bytes before those two seal files. Original author prose/code is separate from protected private bodies and metadata. The packet files are read-only mode0400 and its directories mode0500; the containing exclusive root remains private. [The verifier](selected/code/verify_packet.py) requires all three explicit detached anchors and checks hashes, modes and exact selection. Tiny copied controls accepted the intact fixture and rejected altered content, mode and an extra file. The actual packet verification record is [SEAL-VERIFICATION.json](SEAL-VERIFICATION.json). These are artifact checks, not mathematical gates.

Frozen statement SHA256: `{ssha}`

Author proof SHA256: `{psha}`

FINAL SHA256: `{fsha}`

MANIFEST SHA256: `{msha}`

This REPORT is outside selected/; its detached SHA256 is recorded in [DETACHED-ANCHORS.json](DETACHED-ANCHORS.json). No inherited manifest was attached to a reduced selection. No nested agents, git/staging/commits, shared writes, public actions, browser UI, downstream formalization, manuscript or release work occurred. Parent alone handles integration and reviews.
'''
(R/'REPORT.md').write_text(report);rsha=sha(R/'REPORT.md')
for p in [S/'MANIFEST.json',S/'FINAL.md',R/'REPORT.md']:p.chmod(0o400)
for d in sorted(dirs,key=lambda x:len(Path(x).parts),reverse=True):(S/d).chmod(0o500)
R.chmod(0o700)
cmd=['python',str(R/'verify_packet.py'),'--root',str(S),'--final-sha256',fsha,'--manifest-sha256',msha,'--report',str(R/'REPORT.md'),'--report-sha256',rsha]
x=subprocess.run(cmd,capture_output=True,text=True)
assert x.returncode==0,(x.stdout,x.stderr)
verification={'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'read_only':True,'explicit_anchor_command':cmd,'result':json.loads(x.stdout),'controls':'tiny-control-results.json; independent synthetic copied controls only','math_gate':False,'seal_runs':1}
(R/'SEAL-VERIFICATION.json').write_text(json.dumps(verification,indent=2)+'\n');(R/'SEAL-VERIFICATION.json').chmod(0o400)
anchors={'FINAL':{'path':'selected/FINAL.md','sha256':fsha},'MANIFEST':{'path':'selected/MANIFEST.json','sha256':msha},'REPORT':{'path':'REPORT.md','sha256':rsha},'statement_sha256':ssha,'author_proof_sha256':psha,'seal_runs':1,'verification_record_sha256':sha(R/'SEAL-VERIFICATION.json')}
(R/'DETACHED-ANCHORS.json').write_text(json.dumps(anchors,indent=2)+'\n');(R/'DETACHED-ANCHORS.json').chmod(0o400)
for name in ['FROZEN-STATEMENT.md','AUTHOR-PROOF.md','COMPATIBILITY.md','PREFREEZE.md','READING-SCOPE.md']:(R/name).chmod(0o400)
print(json.dumps({'anchors':anchors,'verification':verification['result']},indent=2))
