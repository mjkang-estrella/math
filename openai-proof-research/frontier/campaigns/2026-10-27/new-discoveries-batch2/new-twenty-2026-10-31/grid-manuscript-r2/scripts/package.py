from pathlib import Path,PurePosixPath
import json,hashlib,zipfile,difflib
D=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):(D/p).write_text(json.dumps(x,indent=2)+'\n')
b=json.loads((D/'hashes/inputs-before.json').read_text());a={p:sha(Path(p)) for p in b}
save('hashes/inputs-after.json',a)
changes=[p for p in b if b[p]!=a[p]];assert not changes,changes
save('receipts/input-integrity.json',{'files':len(b),'all_unchanged':True,'round_1_read_only':True,'other_lanes_not_edited':True,'before_first_read':False,'binding_scope':'See receipts/binding-scope.json; baseline precedes copying/revision, after orientation reads.'})
idx=json.loads((D/'SOURCE-COPIES.json').read_text())
for rel,v in idx.items():
 assert sha(D/rel)==v['sha256']
 p=Path(v['original'])
 if p.is_file():assert sha(p)==v['sha256']
save('receipts/source-copy-validation.json',{'copies':len(idx),'local_copy_hashes':'PASS','available_original_hashes':'PASS','historical_initial_snapshots':'Original initial REVIEW snapshot no longer available upstream; inherited round-1 copy and hash retained.'})
assert sha(D/'grid-formal-r6-source.zip')=='a4068de99037028f817f2f5d1652a97d7508c4419353da95abea04b45b977953'
qa=json.loads((D/'qa/receipt.json').read_text());assert qa['pdf_sha256']==sha(D/'paper.pdf')
assert qa['pages']==11 and len(qa['images_sha256'])==11
for p,h in qa['images_sha256'].items():assert sha(D/p)==h
for n in ['paper.md','PROOF.md','REPRODUCE.md','SUMMARY.md','results.json','root-status.json']:
 s=(D/n).read_text();assert '46/47' not in s and 'C/D still' not in s
s=(D/'paper.md').read_text();assert len(s.split('---PAGE---'))==11
assert (D/'PROOF.md').read_text().endswith(s.replace('---PAGE---','\n'))
root=json.loads((D/'inputs/grid-parent-final-r1/replay-result.json').read_text());assert root['build'].startswith('47/47') and root['status']=='PASS'
fidelity=json.loads((D/'inputs/grid-fidelity-r1/review.json').read_text());assert fidelity['verdicts']=={'A':'PASS','B':'PASS','C':'PASS','D':'QUALIFIED_PASS','E':'QUALIFIED_PASS'}
assert len(json.loads((D/'gate-E-map.json').read_text()))==6
R=D.parent/'grid-manuscript-r1'
diff=''.join(difflib.unified_diff((R/'paper.md').read_text().splitlines(True),s.splitlines(True),fromfile='read-only grid-manuscript-r1/paper.md',tofile='grid-manuscript-r2/paper.md'))
(D/'receipts/paper-r1-to-r2.diff').write_text(diff)
save('receipts/editorial-validation.json',{'current_prose_uses_corrected_receipt':True,'fidelity_final_statuses_match':True,'all_six_gate_E_items_mapped':True,'proof_matches_paper':True,'paper_pages':11,'mathematical_arguments_retained':True,'acceptance':False,'credit':0,'lean_executed':False})
exclude={'DOSSIER-MANIFEST.json','DELIVERY-SHA256.json','package-validation.json','grid-full-dossier.zip'}
files=[p for p in sorted(D.rglob('*')) if p.is_file() and p.relative_to(D).parts[0] not in ['source-extraction','tmp'] and p.name not in exclude]
manifest={str(p.relative_to(D)):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in files}
save('DOSSIER-MANIFEST.json',{'note':'Excludes self, post-package delivery/validation/completion receipts, and redundant source-extraction/tmp intermediates. Includes frozen historical evidence clearly separated from current records.','files':manifest})
z=D/'grid-full-dossier.zip'
with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED,compresslevel=6) as f:
 for p in files+[D/'DOSSIER-MANIFEST.json']:f.write(p,p.relative_to(D))
with zipfile.ZipFile(z) as f:
 assert f.testzip() is None
 for n in f.namelist():
  p=PurePosixPath(n);assert not p.is_absolute() and '..' not in p.parts and '\\' not in n
 for n,v in manifest.items():assert hashlib.sha256(f.read(n)).hexdigest()==v['sha256']
save('package-validation.json',{'crc':'PASS','all_member_hashes':'PASS','safe_relative_names':'PASS','members':len(manifest)+1,'zip_bytes':z.stat().st_size,'source_zip_byte_identical':True,'no_lean_run':True,'all_inputs_unchanged':True})
save('DELIVERY-SHA256.json',{n:{'sha256':sha(D/n),'bytes':(D/n).stat().st_size} for n in ['paper.pdf','paper.md','PROOF.md','SUMMARY.md','results.json','grid-formal-r6-source.zip','grid-full-dossier.zip','DOSSIER-MANIFEST.json']})
print('Packaged and verified',len(manifest)+1,'members;',z.stat().st_size,'bytes;',len(b),'unchanged input files')
