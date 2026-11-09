from pathlib import Path
import os,re,json
R=Path('frontier/campaigns/2026-10-14/t177c143-contribution-r1')
forbidden=re.compile(r'(?:analytic.*r(?:135|136|137)|arithmetic.*r107|t177c143-|t373e135-|k369r134-|t088p133-)',re.I)
coarse=re.compile(r'(?:parent|review|contribution|intake|brief|context|followup|archive|copy|copied|mirror|corpus|fixture|control|source|render|vendor|frozen|outside|download|extract|inventory|snapshot|provenance|private|inputs|payload|packet-cache|release|build|cache|scratch|work|\.git|\.lake|venv|node_modules|formal|active|discovery-r(?:13[5-9]|14[0-9]))',re.I)
flat=re.compile(r'(?:history|catalogue|preprints-tree|pinned-blobs|acquire|manifest|sha256|final\.json|task|ledger|authentication|receipt|baseline|capture|preserv|history-hits|navigation|mutation|external-input|evidence)',re.I)
pat=re.compile(r'(?:source\s*177|family\s*177|bounded.degree.coboundary|coherent.{0,20}(?:fill|lift)|stochastic.{0,15}section|cut.equivari|character.coset|random.{0,15}cofill|collective.{0,15}(?:fill|expan)|right.inverse.{0,30}(?:Lipschitz|coupl)|Khot.{0,5}Naor)',re.I)
files=[];hits=[];omitted=[];errors=[]
for base in ['campaigns','iterations','experiments','proposals','scouts','notes','findings']:
 root=Path('frontier')/base
 if not root.exists():continue
 for d,ds,fs in os.walk(root,topdown=True,followlinks=False):
  keep=[]
  for name in sorted(ds):
   if forbidden.search(name) or coarse.search(name) or (Path(d)/name).is_symlink():omitted.append(str(Path(d)/name))
   else:keep.append(name)
  ds[:]=keep
  for name in sorted(fs):
   if forbidden.search(name) or coarse.search(name) or flat.search(name):continue
   p=Path(d)/name
   if p.is_symlink():continue
   try:
    b=p.read_bytes()
    if b'\0' in b:continue
    s=b.decode('utf-8')
   except (UnicodeError,OSError) as e:errors.append({'path':str(p),'error':str(e)});continue
   files.append({'path':str(p),'bytes':len(b)})
   for n,line in enumerate(s.splitlines(),1):
    if pat.search(line):hits.append({'path':str(p),'line':n,'text':line})
(R/'private/history-search-refined.json').write_text(json.dumps({'policy':'topdown pruning before descent/body selection; hidden ignored JSON large UTF8 included; no size cutoff; coarse exclusions omit authored material too; no priority clearance','selected':files,'omitted_directories':omitted,'errors':errors,'hits':hits},indent=2)+'\n')
print('selected',len(files),'hits',len(hits),'omitted',len(omitted),'errors',len(errors))
for p in sorted(set(x['path'] for x in hits)):print(p)
