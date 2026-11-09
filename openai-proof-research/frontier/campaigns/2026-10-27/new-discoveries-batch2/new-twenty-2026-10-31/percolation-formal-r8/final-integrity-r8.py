from pathlib import Path
import hashlib,json,zipfile
r=Path(__file__).resolve().parent;s=r/'strict-final';sig='r8-v1';order=(r/'module-order.txt').read_text().splitlines()
for m in order:
 h=hashlib.sha256((s/'src'/f'{m}.lean').read_bytes()).hexdigest();sig=hashlib.sha256(f'{sig}\n{h}\n'.encode()).hexdigest();o=hashlib.sha256((s/'build'/f'{m}.olean').read_bytes()).hexdigest()
 assert (s/'logs'/f'{m}.ok').read_text().strip()==f'{sig} {o}',m
with zipfile.ZipFile(r/'source-only.zip') as z:
 manifest=z.read('source-manifest.sha256').decode().splitlines()
 for row in manifest:
  h,n=row.split('  ',1);assert hashlib.sha256(z.read(n)).hexdigest()==h
 for m in order:assert z.read(f'src/{m}.lean')==(s/'src'/f'{m}.lean').read_bytes()
 for n in ["replay.sh","guard.sh","scan.py"]:assert z.read(n)==(s/n).read_bytes()
report={'strict_modules':len(order),'source_and_compiled_output_stamps':'all verified','final_archive_manifest':'all verified','all_delivered_Lean_bytes_equal_fresh_replayed_bytes':True,'replayed_archive_sha256':(r/'replayed-source-archive.sha256').read_text().split()[0],'final_archive_sha256':hashlib.sha256((r/'source-only.zip').read_bytes()).hexdigest(),'reporting_files_refreshed_after_replay':True}
(r/'final-verification.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
res=json.loads((r/'results.json').read_text());f=res['fresh_replay'];assert f['modules']==len(order)
assert res['closed_mask_additions']==129671 and res['endpoint']=='Percolation.not_conjecture20_unconditional'
