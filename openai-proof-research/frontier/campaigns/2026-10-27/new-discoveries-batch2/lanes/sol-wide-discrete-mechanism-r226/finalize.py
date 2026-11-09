from pathlib import Path
import hashlib,json,datetime,xml.etree.ElementTree as E
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
bindings=json.loads((L/'freeze.json').read_text())
b=L.parent.parent
p=b/'lanes/sol-fresh-source-discovery-r213/qualified-original-index.json';q=L/'frozen/history-index.json'
assert sha(p)==sha(q)
bindings.append({'original':str(p),'copy':str(q),'sha256':sha(q)})
(L/'freeze.json').write_text(json.dumps(bindings,indent=2)+'\n')
scopes={
'1705.04554v1':'Definitions1.1–1.2, dimension2 theorem/proof, Section4 including Theorem4.2 proof and Question4.4p14',
'1408.3457v1':'Definitions1.1–1.6; Section4 local-degree recurrence, Proposition4.8/4.9 proofs, Questions4.11/4.12/4.16',
'1907.04349v1':'Definitions/sign-switching; Section3 problem statements; Theorem3.8 and spectral/Gram/signing comparisons; Section3.7 Seidel questions',
'1612.03644v3':'QuestionA; Section3 block examples; Proposition5.3 proof/Corollary5.4; Lemma5.11 proof/Theorem5.14; Table2',
'1703.02943v1':'Section4 classification method, Theorems4.7/4.8 and conference examples; no computation replicated',
'1909.06821v1':'Sections2–3 including NEPS Theorem4 proof and rooted product mechanism; non-sign-symmetry example explicitly incomplete locally',
'2011.06435v2':'Problem1 and rank definition; Lemma3.1/Theorem3.2; complete Theorem4.1 recursive counterexample proof',
'2511.03396v2':'Theorem2, attribution correction, degree/multiplicity framework; not every auxiliary proof independently checked',
'1102.5727v1':'Definitions of Costas/subpermutations; Problems8/14 and adjacent construction mechanisms; chronology discrepancy retained',
'math9801060v3':'Problems17/19, local replacement weights and boundary explanation, nonplanar cube enumeration context',
'1705.04055v1':'Selected retrospective question statements only; not counted as primary new families'}
http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
versions=[]
p=L/'primary/versions.xml'
if p.exists():
 ns={'a':'http://www.w3.org/2005/Atom'}
 for e in E.fromstring(p.read_bytes()).findall('a:entry',ns):
  versions.append({k:e.findtext('a:'+k,namespaces=ns) for k in ['id','title','published','updated']})
(L/'provenance.json').write_text(json.dumps({'utc':str(datetime.datetime.now(datetime.timezone.utc)),'primary':http,'actual_read_scopes':scopes,'metadata_versions':versions,'chronology_limit':'Use exact retrieved version/date; Costas cover2024 vs header2011 unresolved; journal identities not assumed','administrative':'snapshots only','history':'1589 immutable references, before/after hashes; no recursive copying','registry':'current heads unavailable within allowed evidence; previously denied routes not retried','resources':{'AS_bytes':536870912,'sampled_group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230},'count_credit':0},indent=2)+'\n')
files={str(p.relative_to(L)):sha(p) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
(L/'finalmanifest.json').write_text(json.dumps({'algorithm':'sha256','excludes':['finalmanifest.json','verification-receipt.json'],'files':files},indent=2)+'\n')
print(json.dumps({'manifest_files':len(files),'bindings':len(bindings),'primary_responses':len(http)}))
