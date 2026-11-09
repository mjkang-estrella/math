from pathlib import Path, PurePosixPath
import hashlib, json, zipfile, stat, resource, time, os, shutil
O=Path(__file__).resolve().parents[1]; started=time.monotonic()
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''): h.update(chunk)
    return h.hexdigest()
def dump(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
expected='987233b0343fb9855f659eefedaf28bc2a91576cf5c6c3a50342671895d3d175'
assert sha(O/'lean-source.zip')==expected
assert (O/'scripts/build_pdf.py').read_bytes()==(O.parent/'antimagic-manuscript-r1/scripts/build_pdf.py').read_bytes()
before=json.loads((O/'inputs-before.json').read_text());after={p:sha(Path(p)) for p in before}
assert before==after, [p for p in before if before[p]!=after[p]]
dump(O/'inputs-after.json',after)
dump(O/'receipts/input-integrity.json',{'status':'PASS','files':len(after),'all_equal':True,'before_sha256':sha(O/'inputs-before.json'),'after_sha256':sha(O/'inputs-after.json'),'required_pre_hash_reads':'TASK.txt, r1 REPRODUCE.md and root-example-check.txt read first as expressly required; all bound before substantive review/copy'})
q=json.loads((O/'receipts/visual-qa.json').read_text());assert sha(O/'paper.pdf')==q['pdf_sha256']
for p in q['pages']: assert sha(O/p['image'])==p['sha256'] and p['visually_inspected']
assert len(q['pages'])==8
for r in json.loads((O/'receipts/source-copies.json').read_text()): assert sha(O/r['copy'])==r['sha256']
dump(O/'receipts/seal-process.json',{'status':'PRESEAL_CHECKS_PASS','cpu_affinity':sorted(os.sched_getaffinity(0)),'MALLOC_ARENA_MAX':os.environ['MALLOC_ARENA_MAX'],'cpu_limit':resource.getrlimit(resource.RLIMIT_CPU)[0],'address_space_limit':resource.getrlimit(resource.RLIMIT_AS)[0],'note':'Complete outer wrapper process receipt is in excluded tmp/; full archive verification receipt is detached to avoid circular hashes.'})
excluded={'manifest.sha256','archive-sha256.json','dossier.zip','receipts/dossier-verification.json'}
paths=sorted(p for p in O.rglob('*') if p.is_file() and 'tmp' not in p.relative_to(O).parts and str(p.relative_to(O)) not in excluded)
assert all(not p.is_symlink() for p in paths)
manifest={str(p.relative_to(O)):sha(p) for p in paths}
(O/'manifest.sha256').write_text(''.join(f'{h}  {name}\n' for name,h in manifest.items()))
with zipfile.ZipFile(O/'dossier.zip','w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
    for name in list(manifest)+['manifest.sha256']: z.write(O/name,name)
# Fresh, bounded safe extraction; never use extractall on unchecked paths.
D=O/'tmp/dossier-fresh'
if D.exists():shutil.rmtree(D)
D.mkdir(parents=True)
with zipfile.ZipFile(O/'dossier.zip') as z:
    names=set();total=0
    for x in z.infolist():
        p=PurePosixPath(x.filename);mode=x.external_attr>>16
        assert x.filename and not p.is_absolute() and '..' not in p.parts and '\\' not in x.filename and str(p)==x.filename
        assert x.filename not in names and not x.is_dir() and not stat.S_ISLNK(mode)
        assert not stat.S_IFMT(mode) or stat.S_ISREG(mode)
        assert x.file_size<32*1024**2 and p.suffix not in ('.olean','.ilean','.so')
        total+=x.file_size;assert total<128*1024**2
        names.add(x.filename);dest=D/x.filename;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(z.read(x))
assert names==set(manifest)|{'manifest.sha256'}
assert (D/'manifest.sha256').read_bytes()==(O/'manifest.sha256').read_bytes()
for name,h in manifest.items(): assert sha(D/name)==h
assert sha(D/'lean-source.zip')==expected
assert before=={p:sha(Path(p)) for p in before}
receipt={'status':'PASS','zip_sha256':sha(O/'dossier.zip'),'manifest_sha256':sha(O/'manifest.sha256'),'fresh_extraction':'tmp/dossier-fresh','members':len(names),'payload_files_verified':len(manifest),'uncompressed_bytes':total,'safe_relative_paths':True,'no_duplicates_or_links':True,'all_manifest_hashes_match':True,'exact_membership':True,'lean_packet_byte_identical':True,'inputs_unchanged':len(before),'wall_seconds':time.monotonic()-started,'sampled_self_peak_RSS_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'cpu_seconds':resource.getrusage(resource.RUSAGE_SELF).ru_utime+resource.getrusage(resource.RUSAGE_SELF).ru_stime,'acceptance_credit':0,'acceptance_authority':'root only'}
dump(O/'receipts/dossier-verification.json',receipt)
dump(O/'archive-sha256.json',{name:sha(O/name) for name in ['dossier.zip','manifest.sha256','receipts/dossier-verification.json']})
print(json.dumps(receipt,indent=2))
