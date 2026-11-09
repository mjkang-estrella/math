from pathlib import Path
import re,json,sys
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r225')
f=sys.argv[1];a=int(sys.argv[2]);z=int(sys.argv[3]);b=(R/f).read_bytes();lines=b.splitlines(keepends=True);o=0;mask=[];bounds=[]
for n,l in enumerate(lines,1):
 s=l.decode().strip()
 if a<=n<=z:
  if re.search(r'acknowl|acknowg|thank|communicat|funded|licen[cs]e|copyright|all rights|downloaded|e-mail|\w@\w|Department of|Institute for',s,re.I):mask.append([n,o,o+len(l),'editorial candidate—requires resolution'])
  elif re.fullmatch(r'[\d\s]*',s) or re.match(r'^(?:\d+\s+)?(?:BRIAN WHITE|CURRENTS AND FLAT CHAINS|FERNANDO C\. MARQUES|MIN-MAX THEORY|MINIMAL HYPERSURFACES IN POSITIVE RICCI|EXISTENCE OF INFINITELY MANY MINIMAL HYPERSURFACES|SHARP SCHR|ANASS NIFA|SCHRÖDINGER INEQUALITIES)',s):mask.append([n,o,o+len(l),'page furniture/blank'])
  if re.match(r'^(?:(?:\d+\.){1,3}\s*\w|(?:Theorem|Lemma|Proposition|Corollary|Remark|Definition)\s+[\dA-Z][\dA-Za-z.′\x27]*|Appendix)',s):bounds.append([n,o,o+len(l),s[:95]])
 o+=len(l)
row={'file':f,'lines':[a,z],'mask':mask,'boundaries':bounds}
out=R/'private/primary'/(Path(f).stem+f'-selection-{a}-{z}.json');out.write_text(json.dumps(row,indent=2)+'\n')
print(json.dumps({'file':f,'lines':[a,z],'boundaries':bounds,'nonempty_masks':[x for x in mask if lines[x[0]-1].strip() and not lines[x[0]-1].strip().isdigit()]},indent=2))
