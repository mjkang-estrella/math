from pathlib import Path
import shutil,json,hashlib
D=Path(__file__).resolve().parents[1];B=D.parent
for name in ['source-only-packet.zip']:
 shutil.copy2(B/'expanded-corpus-r73/lean-packet'/name,D/'evidence'/('author-'+name))
shutil.copytree(B/'expanded-corpus-r73/lean-packet/fresh-replay-receipts',D/'evidence/author-fresh-replay-receipts',dirs_exist_ok=True)
# Retain independent reviewers' implementation as labelled evidence, not mathematical sources.
for lane in ['collapsing-review-r2','collapsing-prior-r3']:
 shutil.copytree(B/lane/'scripts',D/'evidence'/lane/'scripts',ignore=shutil.ignore_patterns('__pycache__'),dirs_exist_ok=True)
s=(D/'build_paper.py').read_text().replace("import json,html","import json,html,sys\nsys.path.insert(0,str(__import__('pathlib').Path(__file__).resolve().parent/'local-deps'))")
a=s.index("font=Path(");z=s.index("styles=")
s=s[:a]+"pdfmetrics.registerFont(TTFont('Body','/usr/share/fonts/liberation-serif-fonts/LiberationSerif-Regular.ttf'))\npdfmetrics.registerFont(TTFont('Mono','/usr/share/fonts/liberation-mono-fonts/LiberationMono-Regular.ttf'))\n"+s[z:]
(D/'build_paper.py').write_text(s)
s=(D/'tools/author.py').read_text().replace('Matroid subdivisions, tropical linear spaces and tropical curves','Matroidal subdivisions, Dressians and tropical Grassmannians')
(D/'tools/author.py').write_text(s)
# Cache revisions checked without invoking git or modifying anything.
s=(D/'replay.py').read_text()
anchor="    manifest = json.loads((ROOT / 'source-manifest.json').read_text())"
check="""    # Pinned source revisions are metadata checks; cached oleans remain trusted inputs.
    for pkg in pins['dependency_manifest']['packages']:
        gd = PACK / pkg['name'] / '.git'
        assert gd.is_dir(), 'expected cache git metadata directory'
        head = (gd / 'HEAD').read_text().strip()
        if head.startswith('ref: '):
            ref = head[5:]
            if (gd / ref).is_file():
                head = (gd / ref).read_text().strip()
            else:
                records = (gd / 'packed-refs').read_text().splitlines()
                head = next(line.split()[0] for line in records if line.endswith(' ' + ref))
        assert head == pkg['rev'], 'cache source revision ' + pkg['name']
"""
s=s.replace(anchor,check+anchor)
(D/'replay.py').write_text(s)
(D/'REPRODUCE.md').write_text('''# DRAFT replay: MathDB 378395

Extract source-only-proof.zip with `python3 -I safe_extract.py source-only-proof.zip /absolute/new/destination`. The extractor rejects traversal, absolute paths, duplicate names, symlinks and special files; it never overwrites. The replay refuses any existing .olean, controls/ or replay-receipts/. Run from the new extraction:

```sh
LEAN_BIN=/path/to/lean-4.34.1/bin LEAN_PACKAGES=/path/to/.lake/packages python3 -I replay.py
```

Example paths and exact revisions/binary hashes are in pins.json. Here LEAN_BIN is /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin and LEAN_PACKAGES is /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages. No lake update or cache write is performed. Cached dependency oleans are trusted, not rebuilt or source-attested. The driver checks cache source revision metadata and supplied executable hashes.

The build uses -j1 -DwarningAsError=true; leanchecker separately checks the new module. ReviewAudit enumerates all 134 declarations, full types, origins, bodies and transitive axioms (only propext, Classical.choice, Quot.sound). ReviewSanity checks literal definitions, non-vacuity and endpoints. The two Review files are reviewer supplements; MathDB378395.lean is the byte-identical mathematical source.

Each subprocess uses at most two CPUs, CPU 120 seconds, wall 140 seconds, AS 64 GiB, MALLOC_ARENA_MAX=2, sampled 6 GiB private RSS guard. Total VmRSS is reported separately because clean dependency pages are mmapped. A systemd user scope sets MemoryMax=6G, MemorySwapMax=0 and CPUQuota=200% when available. The driver reports whether the scope was used. It writes only within its own fresh extraction, deletes nothing, and waits for each child. Inputs outside the extraction are read-only.

Controls: the unchanged prefix must compile; one perturbed coefficient must fail the validity theorem at its exact line; wrong endpoint polarity must type-error; sorry must fail warning-as-error; a declared cheat axiom must fail the explicit audit; a malformed olean must fail leanchecker. These checks test only their named rejection mechanisms, not completeness or universal reliability of the harness. The exact Python diagnostic is corroboration, not the Lean proof.

Build paper.pdf with Python 3 and reportlab, using `python3 build_paper.py`; install reportlab in your own environment if necessary. paper-source.json is the editable eight-page manuscript source. The recorded build used lane-local dependencies; these are excluded from the archives. Liberation Serif and Liberation Mono font paths appear in build_paper.py and can be adjusted on other systems. Run pdftoppm -r 100 -png paper.pdf qa/page to render; inspect every page. PROOF.md also gives the ordinary proof and finite determinant recurrence. tools/certificate.py regenerates receipts/minor-certificate.json; it is not required by the Lean replay.

source-manifest.json binds the source archive contents (excluding itself). dossier-manifest.json binds the full archive contents (excluding itself). archive-hashes.json binds the two final ZIPs. frozen-before.json and frozen-after.json bind all four protected input trees/files; unrelated r73 files are hash-bound for integrity but not included. Prior-art reviews and historical receipts are labelled evidence. The reviewers' HOLD and root's bounded qualified pass are both preserved; no priority is claimed. Dobra's later-open report is inherited from adjudication and not independently body-verified here.

DRAFT; zero accepted credit; campaign remains 11/20 beyond 39. Root alone accepts.
''')
(D/'receipts/artifact-marker.json').write_text(json.dumps({'operation':'create','expected_output_count':1,'format':'pdf','marker_exit':0,'skill':'pdf','note':'Exact skill marker invoked successfully immediately before authoring.'},indent=2))
print('prepared')
