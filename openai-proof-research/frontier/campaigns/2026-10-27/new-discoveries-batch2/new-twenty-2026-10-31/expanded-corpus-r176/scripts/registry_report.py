import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];p=D/'outputs/registry-screen.json';r=json.loads(p.read_text());ext=json.loads((D/'extracted.json').read_text());r['per_id']={}
keywords={364985:['Mycielsk'],365076:['kipas','Gallai'],365077:['wheel','Gallai'],365295:['SumFree','sum-free','InverseSum'],365360:['TreePacking'],365368:['Clifford','ShadowNorm','stabilizer'],365523:['Eigenvariety','TensorMultiplicity'],365572:['Cichacz','ZeroSumPartition'],365579:['CommonNeighbourConjecture','Saxl'],365610:['Unavoidability'],365611:['Unavoidability'],365612:['Unavoidability'],366011:['RadialMoore'],366175:['MagneticDirichlet'],366321:['Arborescence'],366341:['NathSaikia','RegularPartitions'],366405:['RegularOverpartitions'],357281:['Jacobian'],357395:['ThueMorse','TwoBlock'],357557:['Doolittle','PolytopeReconstruction']}
files=list((D/'sources').glob('lean-pool-file-*.txt'))+list((D/'sources').glob('lean-pool-projects-actual-*.yml'))
trees=['lean-pool-tree.json','trureturing-D5-tree.json','trureturing-Problems-tree.json','math-preprints-tree.json']
for i,o in ext.items():
 terms=[i,o['source_url'].rsplit('/',1)[1]]+keywords[int(i)];hits=[]
 for name in trees:
  f=D/'sources'/name;j=json.loads(f.read_text());paths=[x['path'] for x in j['tree'] if any(t.lower() in x['path'].lower() for t in terms)]
  if paths:hits.append({'file':name,'paths':paths,'truncated':j.get('truncated')})
 for f in files:
  lines=[x[:600] for x in f.read_text().splitlines() if any(t.lower() in x.lower() for t in terms)]
  if lines:hits.append({'file':f.name,'lines':lines[:20]})
 r['per_id'][i]={'terms':terms,'hits':hits,'interpretation':'bounded path/metadata search; keyword hits are not proof matches; authors not comprehensively indexed'}
r['limitations']=['Initial trureturing recursive root download was cut at 15000000 bytes by this script; it is invalid JSON and was not screened. Complete D5 and Problems subtree listings fetched separately and used instead.','No external Lean replay performed.','Exactly eight repository queries, spaced eight seconds; no GitHub code-search completeness asserted.','Source arXiv IDs and MathDB IDs searched in metadata, plus distinctive keywords; not every conjecture author received a separate GitHub query.','The brief names root projects.yml, which returned 404. The actual pinned manifest is LeanPool/projects.yml, downloaded and screened. This correction occurred after the bounded numerical searches; the complete recursive Lean Pool code tree and candidates files had been screened before them. This sequencing limitation is retained rather than claiming perfect compliance.']
r['projects_receipts']=json.loads((D/'outputs/fetch-poolprojects.json').read_text())
r['manifest']={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in (D/'sources').iterdir() if f.is_file() and ('tree' in f.name or 'head' in f.name or 'lean-pool-file' in f.name or 'lean-pool-projects' in f.name)}
r['matched_prior_resolution']={'365579':{'repository':'Vilin97/lean-pool','main_module':'LeanPool/CommonNeighbourConjecture/Examples/MainTheorems.lean','endpoint':'SaxlCounterexamples.MainTheorems.mainTheorem','source_bridge':'Source Theorem 6.7; failure of common-neighbour property contradicts neighbourhood meeting every almost-regular orbit. Main theorem statement and generalized adjacency bridge read; external certificate not replayed.'}}
p.write_text(json.dumps(r,indent=2)+'\n');print('updated registry screen')
