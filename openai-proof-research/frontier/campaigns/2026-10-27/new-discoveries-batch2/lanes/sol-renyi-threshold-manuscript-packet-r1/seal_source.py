import json,hashlib,shutil,platform,zlib,sys
from pathlib import Path
import reportlab,PIL,charset_normalizer
R=Path(__file__).resolve().parent;P=R/'packet';B=R.parent
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
def cp(p,q):q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
for p in (B/'sol-renyi-deficit-source-formal-r2/logs').glob('*'):
 if 'failed' in p.name or 'before-silent' in p.name or p.stem=='Probe':cp(p,P/'evidence/formal-failures'/p.name)
for p in R.glob('*.log'):cp(p,P/'evidence/packet-setup'/p.name)
for n in ['live-receipts.jsonl','closest-receipts.jsonl','search-notes.md']:
 cp(B/'sol-renyi-threshold-preliminary-review-r1'/n,P/'evidence/primary-receipts'/n)
for n in ['baseline-unread-limits.json','provenance.json']:
 cp(B/'sol-renyi-registry-gap-closure-r3'/n,P/'evidence/registry-bounds'/n)
cp(Path('/usr/share/licenses/liberation-serif-fonts/LICENSE'),P/'assets/Liberation-LICENSE')
cp(R/'replay-fresh/replay-receipt.json',P/'receipts/fresh-replay.json')
for p in (R/'replay-fresh/logs').glob('*'):cp(p,P/'receipts/fresh-replay-logs'/p.name)
cp(R/'freeze-before.json',P/'receipts/freeze-before.json')
cp(R/'consulted-before.json',P/'receipts/consulted-before.json')
tools={'python':platform.python_version(),'python_binary':sys.executable,'python_sha256':sha(Path(sys.executable)),'reportlab':reportlab.Version,'pillow':PIL.__version__,'charset_normalizer':charset_normalizer.__version__,'zlib':zlib.ZLIB_RUNTIME_VERSION,'fonts':{p.name:sha(p) for p in (P/'assets').glob('*.ttf')},'formal_pins':'component/pins.json','guards':{'helper':sha(P/'component/helper_guard.py'),'lean':sha(P/'component/guard.py')}}
(P/'toolchain.json').write_text(json.dumps(tools,indent=2)+'\n')
(P/'requirements.txt').write_text('reportlab==4.4.10\npillow==13.0.0\ncharset-normalizer==3.5.2\n')
(P/'failures.md').write_text('''# Retained failures and limitations

No caps or checks were weakened. The PDF skill marker failed under the fixed helper AS limit: Node aborted in SegmentedTable initialization. A retry with unsupported flags exited 9; low-memory mode, node-24 and the existing alternate Node also aborted. The marker was not successfully completed. This is a disclosed skill-instrumentation failure, not a mathematical or visual verification PASS. Exact available logs are retained in evidence/packet-setup. No approval or cap increase was sought.

First PDF import failed because ReportLab was unavailable. Pinned renderer dependencies were then installed into this assigned lane's vendor directory, excluded from the source ZIP. The next build failed on the assumed Debian font path; source font assets were copied from the actual system paths. The first render accordingly had no PDF input. Subsequent builds and renders succeeded. Initial native broad text displays/searches were truncated; no exhaustive coverage conclusion relies on those outputs. No browser or git command was used.

The formal r2 informational-ring first replay failure and earlier probes/type/linter failures remain in original frozen lanes, with descriptions in SUMMARY and exact small logs copied to evidence/formal-failures. No original source was edited. Earlier candidate optional-inventory termination, CMU404 and invalidated provisional Maxwell/BNT freshness claims remain in original provenance and the retained review. The registry review preserves 51 historical context whole-source hash mismatches and selective baseline semantics. Exact atoms were recovered, not full old contexts. No new registry refresh is claimed here. Independent final review and root acceptance remain pending.
''')
for n in json.loads((R/'consulted-before.json').read_text()):
 p=B/n if not n.startswith('../') else B.parent/n[3:]
 assert sha(p)==json.loads((R/'consulted-before.json').read_text())[n],n
freeze=json.loads((R/'freeze-before.json').read_text())
for n,h in freeze['files'].items():assert sha(Path(freeze['root'])/n)==h,n
(P/'receipts/freeze-after.json').write_text(json.dumps(freeze,indent=2)+'\n')
manifest={p.relative_to(P).as_posix():sha(p) for p in sorted(P.rglob('*')) if p.is_file() and p!=P/'manifest.json'}
(P/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print('Source manifest sealed',len(manifest),'files; frozen originals unchanged')
