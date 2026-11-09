from pathlib import Path
import re,json,hashlib,shutil,stat,difflib
R=Path.cwd();P=R/'packet/public';OLD=R.parent/'t088p133-manuscript-r1';PROJECT=R.parents[3]
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,obj):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
# Historical named private binding: deliberately distinct from the public verifier.
f=json.loads((OLD/'FINAL.json').read_text());m=OLD/'private/MANIFEST.json'
assert h(m)==f['private_evidence_manifest_sha256']
private=json.loads(m.read_text())['files']
for name,v in private.items():
 p=OLD/name;assert h(p)==v['sha256'] and p.stat().st_size==v['bytes'] and stat.S_IMODE(p.stat().st_mode)==v['mode']
assert len(private)==36
# Reread/retained evidence, without carrying forward obsolete current-stage claims.
d=json.loads((P/'provenance/r1-source-reading-records.json').read_text())
for row in d['sources']:
 row['r1_local_path']=row['local'];row['local']=row['local'].replace('private/','private/r1-evidence/',1)
 assert h(R/row['local'])==row['sha256']
 row['r2_read_extent']=row.pop('actual_read_extent')
 row['acquisition']='Local reuse from authenticated r1 private evidence; no new acquisition. Reading extents refer to actual r2 rereads except explicitly byte-only records.'
d['sources'][9]['r2_read_extent']='text derivative lines1-200 and1282-1360; opening/main statements and Section7, not interior proof sections'
d['sources'][15]['r2_read_extent']='lines18-24, relevant paragraph21 only'
d['stage']='manuscript-r2 actual reads/reuse, distinct from unchanged r1 historical record'
d['primary_urls_and_versions']='private/r1-evidence/evidence/r3-acquisition.json and contribution-acquisition.json; unchanged historical acquisition records'
d['limits']='No fresh worldwide/project priority or open-status survey, no download or upstream truth audit. Klefsjo metadata only; Brannen/CFLXX bodies unavailable. No active fresh-structural-discovery-r137 content read. Completed formal implementation/review read as expressly required. All ten witness rows, all five polynomials and strict subsets decoded/printed in full. Full required r1 mathematical source, bibliography, appendix and supporting code/evidence read; historical inventory metadata authenticated programmatically, not claimed mathematical/body reading.'
d['r1_private_named_inventory']={'sha256':h(m),'named_files':36,'checked':True,'public_verifier_coverage':False}
save(P/'source-reading-records.json',d)
# Exact preservation of every theorem/proof and all mathematical-section bytes.
a=(OLD/'packet/public/main.tex').read_text();b=(P/'main.tex').read_text()
b_clean=re.sub(r'% BEGIN R2 FORMAL USE-SITE NOTE\n.*?% END R2 FORMAL USE-SITE NOTE\n\n','',b,flags=re.S)
start=r'\section{Statement, context and proof structure}'
end=r'\section{Positioning, provenance and coverage}'
assert start in a and end in a
ac=a[a.index(start):a.index(end)];bc=b_clean[b_clean.index(start):b_clean.index(end)]
assert ac==bc
blocks={}
for env in ['theorem','lemma','proposition','proof']:
 pattern=r'\\begin\{'+env+r'\}.*?\\end\{'+env+r'\}'
 x=re.findall(pattern,a,re.S);y=re.findall(pattern,b,re.S);assert x==y
 blocks[env]={'count':len(x),'byte_identical':True,'sha256':hashlib.sha256('\n'.join(x).encode()).hexdigest()}
unchanged={}
for name in ['witness-tables.tex','support/author-certificate.py','support/geometry_control.py','support/independent_certificate.py','support/certificate-witness.json','support/reproduce.py','build.sh','bootstrap.py']:
 assert (P/name).read_bytes()==(OLD/'packet/public'/name).read_bytes();unchanged[name]=h(P/name)
for row in json.loads((P/'support-origin.json').read_text()):assert h(P/row['path'])==h(Path(row['source']))==row['sha256']
origins=json.loads((P/'formal/origin.json').read_text())
for rel,rec in origins.items():assert h(P/rel)==h(PROJECT/rec['original'])==rec['sha256']
oldbib=(OLD/'packet/public/references.tex').read_text();newbib=(P/'references.tex').read_text()
def items(t):return dict(re.findall(r'\\bibitem\{([^}]+)\}(.*?)(?=\\bibitem|\\end\{thebibliography\})',t,re.S))
olditems=items(oldbib);newitems=items(newbib)
for k,v in olditems.items():assert v.strip()==newitems[k].strip(),k
save(P/'qa/source-preservation.json',{'r1_main_sha256':h(OLD/'packet/public/main.tex'),'r2_main_sha256':h(P/'main.tex'),'mathematical_sections_through_appendix_A_byte_identical_after_removing_explicit_new_note':True,'core_sha256':hashlib.sha256(ac.encode()).hexdigest(),'theorem_and_proof_blocks':blocks,'unchanged_files':unchanged,'original_bibliography_entries_preserved':len(olditems),'formal_public_files_unchanged':len(origins),'full_sparse_terms':sum(len(x['T']) for x in json.loads((P/'support/certificate-witness.json').read_text())),'scope':'Text/data preservation only; not a new mathematical truth audit'})
(P/'qa/main-r1-to-r2.diff').write_text(''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='r1/main.tex',tofile='r2/main.tex')))
# Preserve all actual new formal logs and receipt, no binaries or cached bodies.
B=R/'build/extracted-proof-support/build/work/replay-1';Q=P/'qa/formal';Q.mkdir(exist_ok=True)
for f in sorted(B.iterdir()):
 if f.is_file() and f.suffix in ['.json','.log']:shutil.copy2(f,Q/f.name)
for f in ['Checks.lean','ReviewChecks.lean']:shutil.copy2(B/'package/work/fresh'/f,Q/f)
copyroot=R/'build/extracted-proof-support'
copyfiles={str(q.relative_to(copyroot)):h(q) for q in sorted((copyroot/'packet').rglob('*')) if q.is_file()}
save(Q/'extracted-context.json',{'context':str(copyroot),'supplied_files':copyfiles,'external_execution_inputs':['explicit trusted Lean compiler/runtime','explicit trusted pinned precompiled .lake/packages cache'],'historical_metadata_not_executable_dependencies':True,'no_author_manuscript_private_source_inputs':True,'wrapper_sha256':h(P/'support/formal_reproduce.py'),'status':json.loads((B/'receipt.json').read_text())['status'],'note':'A separate writable copy context, not execution in either sealed historical package; no OS-level dependency filesystem isolation claimed.'})
# Bind the actual inspected images before repeat build.
comments=['Title, author, abstract, scope and theorem readable; no affiliation/contact.','Positioning and facet start; pin and references fit.','Projection/mixed-volume equations and section maximum readable.','Attainment proof, coarea and Gamma equations unclipped.','Density and Laplace normalization equations fit.','Log-concavity and survival integration legible.','Proposition B proof and new use-site paragraph; two-bracket equation clear.','Use-site continuation and partial fractions fit.','Strict endpoint/continuity assembly and equality section clear.','Simplex equality and auxiliary-limit equations fit.','Recurrence and complete-certificate description legible.','Summary and first three sparse tables legible.','Sparse tables, start of 118-term table fit.','118-term continuation and 84-term start; high-resolution table crop also checked.','84-term continuation, final table and provenance readable.','History, limited formal adoption and rights paragraphs fit.','Exact Lean hypotheses, residuals, names and mapping readable.','Scalar premise, endpoints, trust/exclusions readable; long hashes fit.','References1-12 and source links fit.','Reference13 alone at page top; deliberate ordinary bibliography continuation, no clipping.']
save(P/'qa/visual-inspection.json',{'observer':'r2 implementation agent, not independent reviewer','method':'All20 final120dpi page PNGs viewed individually; page14 table also inspected at240dpi crop','pdf_sha256':h(P/'output/pdf/main.pdf'),'pages':[{'page':i+1,'file':f'renders/page-{i+1:02}.png','sha256':h(P/f'renders/page-{i+1:02}.png'),'observation':c,'clipping_or_overlap_found':False} for i,c in enumerate(comments)],'all_pages_inspected':True,'independent_manuscript_gate':False})
pre={'pdf_sha256':h(P/'output/pdf/main.pdf'),'renders':{p.name:h(p) for p in sorted((P/'renders').glob('*.png'))},'engine_sha256':h(R/'tools/tectonic'),'cache':{str(p.relative_to(R/'build/cache')):h(p) for p in sorted((R/'build/cache').rglob('*')) if p.is_file()}}
save(R/'work/before-repeat-build.json',pre)
print(json.dumps({'source_preservation':True,'formal_files_unchanged':len(origins),'proof_blocks':blocks,'private_r1_named_files':36,'visual_pages':20}))
