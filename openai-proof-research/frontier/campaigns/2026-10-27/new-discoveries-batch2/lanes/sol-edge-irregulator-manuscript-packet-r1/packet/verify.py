from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;archive=Path(sys.argv[1]).resolve();dest=Path(sys.argv[2]).resolve()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run([sys.executable,str(P/'replay.py'),str(archive),str(dest)],check=True)
for name in ['OriginAudit','AuditPrint']:
 assert (dest/'logs'/f'{name}.log').read_bytes()==(dest/'evidence/audit'/f'{name}.log').read_bytes(),name
old=sha(dest/'paper.pdf')
subprocess.run([sys.executable,str(dest/'build_paper.py')],check=True)
assert sha(dest/'paper.pdf')==old,'PDF not byte identical'
rebuilt=dest/'rebuilt.zip';subprocess.run([sys.executable,str(dest/'pack.py'),str(rebuilt)],check=True)
assert sha(rebuilt)==sha(archive),'ZIP not byte identical'
r=json.loads((dest/'replay-receipt.json').read_text())
r.update(pdf_byte_identical=True,zip_byte_identical=True,paper_sha256=old,root_final_review='PENDING; implementation verification only')
(dest/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print('IMPLEMENTATION VERIFY COMPLETE',r['declaration_count'],old,sha(archive))
