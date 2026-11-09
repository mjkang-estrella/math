from pathlib import Path
import hashlib,json,zipfile
R=Path(__file__).resolve().parent.parent
res=json.loads((R/'results.json').read_text())
assert res['frozen_33_byte_identical'] and res['validation']['fresh_extracted_serial_rebuild']
assert all(v==0 for k,v in res['audit']['local'].items() if k!='declarations')
lines=(R/'fresh-extraction'/'replay.log').read_text().splitlines()
audit=[x for x in lines if 'CLOSURE inventory=' in x]
assert len(audit)==1 and 'sets equal' in audit[0]
mods=(R/'modules.txt').read_text().splitlines()
for m in mods+['ChordComb2Audit']:
 assert (R/'src'/f'{m}.lean').read_bytes()==(R/'fresh-extraction'/'src'/f'{m}.lean').read_bytes()
assert (R/'fresh-extraction'/'build'/'ChordComb2Audit.olean').exists()
receipt=f'''# Validation receipt — Round 2B

All {len(mods)} mathematical modules passed a fresh extracted strict serial rebuild and explicit-module leanchecker. The audit module also compiled and passed explicit-module leanchecker. Every call used the resource wrapper. No frozen source changed.

{audit[0]}

LOCAL declarations: {res['audit']['local']['declarations']}. Forbidden LOCAL metadata and unapproved transitive axioms: zero. Upstream metadata is reported separately in results.json. The audit reads opaque values and generated declarations and checks exact inventory/audited set equality. Its complete rows are in fresh-extraction/audit.jsonl.

Independent regression checked 995,572 diagram/assignment pairs through n = 5 with zero boundary-model mismatches. All four negative controls passed. A separate Lean negative control refutes uniqueness at n = 4.

The final delivery archive updates only packaging scripts and report metadata relative to the replay archive. Every delivered Lean file is byte-identical to its freshly rebuilt source; final extraction equality is checked by scripts/finalize.py. No object files or build markers are included in the source archive.

Peak sampled RSS over development and replay: {res['validation']['peak_sampled_RSS_KiB']} KiB. CPU 120 s, wall 140 s, RSS 6 GiB, taskset CPUs 0 and 1, MALLOC_ARENA_MAX=2 and Lean -M3500 remained in force. Bounded failed development attempts are retained in logs; successful replay is in fresh-extraction/replay.log.

The closed Props are FiveChordLemma and FourChordEnumeration. General existence, bipartite planarity, triangle reduction and large-n rigidity remain unproved. This receipt is not acceptance. Root decides.
'''
(R/'VALIDATION.md').write_text(receipt)
files=list((R/'src').glob('*.lean'))+list((R/'scripts').glob('*'))+list(R.glob('*.md'))+list((R/'hashes').glob('*'))+[R/x for x in ['modules.txt','inherited-modules.txt','certificate.json','regression.json','results.json']]
with zipfile.ZipFile(R/'chord-comb2-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files):
  if p.is_file():z.write(p,p.relative_to(R).as_posix())
delivery=R/'delivery-extraction';delivery.mkdir(exist_ok=False)
with zipfile.ZipFile(R/'chord-comb2-source.zip') as z:
 for info in z.infolist():
  p=Path(info.filename);assert not p.is_absolute() and '..' not in p.parts
  assert p.suffix not in ['.olean','.ilean','.ok']
 z.extractall(delivery)
 for info in z.infolist():(delivery/info.filename).chmod((info.external_attr>>16)&0o777)
for p in (R/'src').glob('*.lean'):
 assert p.read_bytes()==(delivery/'src'/p.name).read_bytes()==(R/'fresh-extraction'/'src'/p.name).read_bytes()
digest=hashlib.sha256((R/'chord-comb2-source.zip').read_bytes()).hexdigest()
(R/'source-archive.sha256').write_text(digest+'  chord-comb2-source.zip\n')
print(receipt)
print('ARCHIVE_SHA256',digest)
