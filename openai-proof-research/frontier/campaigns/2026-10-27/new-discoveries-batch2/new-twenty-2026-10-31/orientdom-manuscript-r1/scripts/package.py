from pathlib import Path,PurePosixPath
import hashlib,json,zipfile,stat,sys,subprocess,xml.etree.ElementTree as E
R=Path.cwd()
def h(b): return hashlib.sha256(b).hexdigest()
def info(p):
 b=p.read_bytes(); return dict(sha256=h(b),bytes=len(b))
def write(p,d): (R/p).write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
# Documentary receipt for source inspection; original acquisition receipts remain unchanged.
write('receipts/source-reading.json',dict(network_used=False,original_sources='All source copies and historical acquisition receipts preserved under inputs/expanded-corpus-r178/sources; historical review/prior-art downloads preserved under their own input lanes.',read=[dict(path='inputs/expanded-corpus-r178/sources/domination1999.pdf',pages='Title page (159) and printed 179–181, visually via preserved renders',sha256=info(R/'inputs/expanded-corpus-r178/sources/domination1999.pdf')['sha256']),dict(path='inputs/expanded-corpus-r178/sources/2311.16307v1.pdf.txt',locations='Definitions, C, Conjecture 3.1, complete-bipartite theorem context, bibliography; explicit historical review correspondence'),dict(path='inputs/expanded-corpus-r178/sources/domination2026.txt',locations='Journal title, authors, definitions and DOI; related-work comparison qualified by preserved review'),dict(path='packet-safe-extraction/Interpolation.lean',locations='Entire source and definitions; Audit.lean read in full'),dict(path='inputs/orientdom-root-ruling-r2.json',locations='Entire ruling, exact qualifications transferred')],unread=['Chartrand–VanderJagt–Yue 1996 primary body','Anderson–Dravec–Johnston–Kuenzel DAM 2026 version of record'],limitations='No new source acquisition. Historical source-access statements are attributed to the ruling/reports.'))
# Parse PDF metadata via Poppler for exact final page count.
r=subprocess.run(['pdfinfo','paper.pdf'],capture_output=True,text=True,check=True); (R/'qa/pdfinfo.txt').write_text(r.stdout)
assert 'Pages:           5' in r.stdout
source_files=[R/p for p in ['paper.md','paper-expanded.md','paper.fodt','PROOF.md','REPRODUCE.md','PRIOR-ART-LIMITATIONS.txt','MathDB-360905.raw.jsonl','Lean-packet.zip','results.json','SUMMARY.md','inputs/orientdom-root-ruling-r2.json']]
source_files+=sorted((R/'scripts').glob('*.py'))+sorted((R/'recomputed').glob('*.json'))
def archive(name,files):
 files=sorted(set(files)); entries={str(p.relative_to(R)):info(p) for p in files}
 for path in entries:
  pp=PurePosixPath(path); assert not pp.is_absolute() and '..' not in pp.parts
 meta=dict(format='sha256',files=entries,excludes='This manifest itself, to avoid circular hashing.')
 with zipfile.ZipFile(R/name,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
  for p in files:
   zi=zipfile.ZipInfo(str(p.relative_to(R)),date_time=(2026,11,5,0,0,0)); zi.external_attr=0o100644<<16; zi.compress_type=zipfile.ZIP_DEFLATED; z.writestr(zi,p.read_bytes())
  zi=zipfile.ZipInfo('ARCHIVE-MANIFEST.json',date_time=(2026,11,5,0,0,0)); zi.compress_type=zipfile.ZIP_DEFLATED; z.writestr(zi,json.dumps(meta,indent=2).encode()+b'\n')
 with zipfile.ZipFile(R/name) as z:
  assert z.testzip() is None
  assert set(z.namelist())==set(entries)|{'ARCHIVE-MANIFEST.json'}
  for p,e in entries.items():
   b=z.read(p); assert h(b)==e['sha256'] and len(b)==e['bytes']
 return dict(path=name,files=len(files),**info(R/name),integrity='PASS: CRC and every internal SHA-256 checked')
a=archive('manuscript-source.zip',source_files)
excluded={'PAYLOAD-MANIFEST.json','ARTIFACTS.sha256','full-dossier.zip','receipts/packaging.json','receipts/package.json','receipts/verify-final.json','receipts/final-integrity.json','receipts/index.json'}
files=[p for p in R.rglob('*') if p.is_file() and 'tmp' not in p.relative_to(R).parts[:1] and str(p.relative_to(R)) not in excluded]
# tmp exclusions apply only to the manuscript's own work area, not preserved historical input tmp evidence.
write('PAYLOAD-MANIFEST.json',dict(format='sha256',scope='All delivered payload files except this manifest, full-dossier.zip, ARTIFACTS.sha256 and subsequent packaging/final-verification receipts; lane-local tmp excluded.',files={str(p.relative_to(R)):info(p) for p in sorted(files)}))
b=archive('full-dossier.zip',files+[R/'PAYLOAD-MANIFEST.json'])
write('receipts/packaging.json',dict(status='PASS',archives=[a,b],unchanged_packet=info(R/'Lean-packet.zip'),manifest=info(R/'PAYLOAD-MANIFEST.json'),note='Packaging receipts and the outer ARTIFACTS.sha256 are external to full-dossier.zip to avoid recursive hashes.'))
print('PASS archives:',a['files'],'source files;',b['files'],'full payload files')
