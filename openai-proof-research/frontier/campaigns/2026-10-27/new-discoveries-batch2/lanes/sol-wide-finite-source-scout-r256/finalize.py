from pathlib import Path
import json,hashlib,datetime,xml.etree.ElementTree as E
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(s) for s in (L/'retrieval.jsonl').read_text().splitlines()]
recovery=json.loads((L/'recovery.json').read_text())
for r in rows:
 if r.get('sha256') in recovery:
  r['original_logged_path']=r['path'];r['path']=recovery[r['sha256']]
for r in rows:
 if 'sha256' in r:assert sha(Path(r['path']))==r['sha256']
(L/'sources/bindings.json').write_text(json.dumps(rows,indent=2))
ns={'a':'http://www.w3.org/2005/Atom'};chron={}
for p in (L/'sources').glob('*.xml'):
 for e in E.parse(p).findall('a:entry',ns):
  id=e.findtext('a:id',namespaces=ns)
  chron[id]={k:e.findtext('a:'+k,namespaces=ns) for k in ['title','published','updated']}
(L/'sources/chronology.json').write_text(json.dumps(chron,indent=2))
sources=['# Frozen source bindings and access limits','', 'All successful retrievals were written and byte-hashed before body extraction/reading. The HTTP original is represented by URL, retrieval time and frozen bytes; no claim of re-fetching an unchanged live original is made. Local original/copy pairs and reused immutable references receive separate after-reading verification.','', '## Primary bodies','']
for p in sorted((L/'sources').glob('*.pdf')):
 r=next(x for x in rows if x.get('path')==str(p))
 sources.append(f"- [{p.name}]({r['url']}): SHA256 `{r['sha256']}`, frozen {r['utc']}.")
sources+=['','## Dated chronology and boundedness','','Juráš–Ursul: arXiv first2Oct2020; publisher received25May2020, accepted30Sep2021, volume9(1)(2022), pp9–15. Equation(2), p12, explicitly open. The same content survives in the fetched published body. Buckley–MacHale author PDF is the original conjecture source; its precise release date was not independently established. Later sources cite it as2014. Mendelsohn v2 is1Nov2023. MacLean target-successor first9May2025/latest4Oct2025, prior to this campaign. Mantica regularity proof and sourcev2 both carry28Oct2016. Exact feed dates are recorded in chronology.json.','','The known Mendelsohn citation missing from the OpenAlex published-record citer list demonstrates that the single reported citer is incomplete. No OpenAlex absence is treated as novelty evidence. Live OpenAI/Omega/D5/Problems registry heads are NOT cleared: forbidden GitHub API/raw/codeload/diff/patch routes were not retried. Pinned OpenAI revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is a dated catalogue/path screen only; no relevant registry theorem body was inferred from titles. Buckley2015 and Mal’cev remain uninspected. The author papers DIRECTORY returned403; this failure is preserved and no bypass or retry was attempted. The two directly cited author PDFs had already succeeded before that denial.','']
(L/'sources/README.md').write_text('\n'.join(sources))
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
provenance=dict(lane=str(L),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),counts={'additional':9,'total':39,'next':40,'modified':False},guard={'path':str(guard),'sha256':sha(guard),'AS_bytes':512*1024*1024,'group_RSS_bytes':512*1024*1024,'CPU_seconds':210,'wall_seconds':230,'cap_raises':False},status='full mathematical derivation; HOLD novelty/substantive qualification; no credit requested',primary_pdfs=len(list((L/'sources').glob('*.pdf'))),retrieval_successes=sum('sha256' in r for r in rows),failures=[r for r in rows if 'failure' in r],historical_reference_policy='731 immediate reports only; no recursively copied trees',current_registry_clearance=False,independent_review=False,lean_written=False,manuscript_written=False,external_mutations=False,scientific_limitations=['classical bimap/isoclinism subsumption unexamined','current proof registry heads uncleared','no comprehensive citer or subscription-index sweep','bounded diagnostics not universal proof'])
(L/'provenance.json').write_text(json.dumps(provenance,indent=2))
commands=[]
for name in ['check.py','verify_math.py','verify_final.py']:
 commands.append('OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python '+str(guard)+' python '+str(L/name))
(L/'RUN.md').write_text('# Fixed-cap replay\n\nRun the following individually from any directory. No cap raises; each invocation has AS/groupRSS512MiB, CPU210s, wall230s. The first two rewrite deterministic diagnostic result files; run final verification after them. The verifier checks byte binding, not mathematical correctness or novelty.\n\n```sh\n'+'\n'.join(commands)+'\n```\n\nRegenerate manifest with finalize.py only after intentional artifact changes; then invoke verify_final.py separately. Preserve failure reports.\n')
excluded={'final-manifest.json','final-verification.json'}
manifest={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded}
(L/'final-manifest.json').write_text(json.dumps(manifest,indent=2))
print('FINALIZED',len(manifest),'artifacts; PDFs',provenance['primary_pdfs'])
