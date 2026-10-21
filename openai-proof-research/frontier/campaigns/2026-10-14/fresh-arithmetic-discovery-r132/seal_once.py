"""Create this own selection's three envelopes once. No old manifest is inherited."""
from pathlib import Path
import sys,json,hashlib,subprocess
sys.dont_write_bytecode=True
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r132')
sys.path.insert(0,str(R))
from verify import inventory,ENVELOPES
E=R/'envelopes'
if E.exists():raise SystemExit('Refusing to reseal: envelope directory already exists')
E.mkdir()
m=inventory(R)
(E/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
MH=hashlib.sha256((E/'MANIFEST.json').read_bytes()).hexdigest()
(E/'FINAL.md').write_text('''# Arithmetic discovery r132 — PREFREEZE / no nominee

Authorized Codex / GPT-6 Astra / high / default service tier. Campaign19/20/latestR041 supplied. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and its operative proofs stipulated true. Parent alone integrates, reviews and counts. No frozen theorem, full author-proof nominee, self-assigned grade or count; no downstream work.

ONE family developed: Source037 ordinary-double-point normalized-volume gap. Both canonical manuscripts and every actual all-dimension include were authenticated and read in full. Complete-tree metadata has13223 entries and the stipulated SHA256. All bounds retain normality, complex algebraicity, boundary-zero klt, dimensional and analytic-isomorphism hypotheses.

Strongest integrated work:

- A below-endpoint regime makes isolated Gorenstein reduction, canonical interiority, reduced two-filtration quotient and singular klt slice compatible. The source inequality d(C)<=p_n/2+d(Y)/h eliminates h>=3 near the endpoint.
- Counting the entire killed triangular adapted-basis region strengthens the slice test by L_n(c,x)=((cx-1)_+)^n/[c(c-1)^(n-1)], where c=w(v)/ell>=1. This is a paid refinement of source/classical shell counting.
- In dimension four, canonical rescaling K=961/400 with the SAME Fourier profiles gives exact positive margins. The complete source structural proof replays for V>3844/25 and reaches a hypersurface; the actual Liu proof bounds a non-ODP hypersurface by4096/27. This is a source-proof parameter composition, not a submitted substantial finding or an old-target retry.
- Xu–Zhuang boundedness/discreteness and Xu constructibility already pay existence of an unspecified second gap after the stipulated equality theorem.

The precise unpaid operation is an effective near-equality comparison of the restricted slice valuation with the minimizing Reeb valuation on the moving canonical section, strong enough for the integer Nm-r. Equality gives o(1/r); no such quantitative replacement was obtained below equality. Bounded families do not themselves bound denominators of arbitrary primitive rational approximants. No exhaustion or impossibility claim.

Durable details: notes/integrated-filtration-calculation.md, notes/fourfold-profile-calculation.md, notes/primary-comparison.md, notes/reduction-boundary.md. READING.md gives actual primary/transitive extents and failures. The old screen-037 scope is expressly excluded and uncleared; no priority/full-scope clearance is claimed.

Isolation limits are material: four administrative false admissions occurred in two scans; guards were strengthened afterward. A component-start screen predicate also received a late compound-alias correction. Coarse omissions and opaque aliases remain. No active-peer premise was used, and no perfect-isolation certificate is claimed. Some combined displays were truncated and recovered; incoming-original identities were taken late. Source/primary/history bodies remain private under their original rights.

Artifact-only checks compare selected source and primary bytes, late incoming snapshots, exact rational calculations and six small copied integrity controls. These are not mathematical gates. This package is its own exact selection, not an inherited original manifest. The three envelopes are outside the manifest's inventoried payload, but inside the exclusive root. Detached anchors for all three must be supplied to verify.py.

MANIFEST SHA256: '''+MH+'\n')
FH=hashlib.sha256((E/'FINAL.md').read_bytes()).hexdigest()
(E/'REPORT.md').write_text('''# Outside report envelope

PREFREEZE/no nominee. Research handoff only. No independent correctness, contribution, acceptance or count determination. No publication or release.

The exact own-selection manifest inventories '''+str(len(m['files']))+''' payload files and '''+str(len(m['directories']))+''' directories. It excludes exactly envelopes/FINAL.md, envelopes/MANIFEST.json and envelopes/REPORT.md. Private bodies retain original rights. Incoming-original identity and selected-copy membership are separate. The small copied control has its own manifest and never inherits an upstream manifest.

Source/primary byte checks and late-original unchanged checks were completed before sealing. Late snapshots do not prove initial global immutability. Arithmetic diagnostics establish only the displayed scalar identities; the verifier checks bytes, exact file sets, regular files, single links and three explicit detached anchors. No artifact check is a mathematical gate.

FINAL SHA256: '''+FH+'\nMANIFEST SHA256: '+MH+'''

This REPORT's own SHA256 is detached in the tool output and final handoff, avoiding a self-hash cycle. No file in this package is to be changed after this one seal.
''')
RH=hashlib.sha256((E/'REPORT.md').read_bytes()).hexdigest()
args=[sys.executable,str(R/'verify.py'),str(R),'--final',FH,'--manifest',MH,'--report',RH]
subprocess.run(args,check=True)
print(json.dumps({'FINAL':FH,'MANIFEST':MH,'REPORT':RH,'payload_files':len(m['files'])},indent=2))
