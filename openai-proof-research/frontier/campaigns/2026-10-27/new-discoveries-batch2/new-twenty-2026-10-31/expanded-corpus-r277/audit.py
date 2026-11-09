from pathlib import Path
import json,hashlib,re,subprocess,resource,os,datetime
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=Path(__file__).resolve().parent;s=p/'sources';sha=lambda b:hashlib.sha256(b).hexdigest()
(p/'version-extraction-first-pass.json').write_bytes((p/'version-read-inventory.json').read_bytes())
records=json.loads((p/'provenance.json').read_text());patterns=[]
for e in records.values():patterns += [e['parsed']['title'],e['parsed']['source_url'].rsplit('/',1)[1]]
(p/'history-patterns.txt').write_text('\n'.join(patterns)+'\n')
cmd=['rg','-n','-i','-F','-f',str(p/'history-patterns.txt'),str(p.parent.parent),'--glob','*.md','--glob','*results*.json','--glob','!**/expanded-corpus-r277/**']
z=subprocess.run(cmd,capture_output=True,timeout=75);(p/'history-title-source-hits.txt').write_bytes(z.stdout)
# Correct misleading automated first-pass matches: distinguish bibliography, absent and renumbered targets.
selectors={'1001.0186':r'^(Conjecture .*Crosspolytopal|5     Inscribed crosspolytopes)|Guggenheimer.*proved', '1001.1812':r'^Conjecture 18.6','1002.0190':r'^Conjecture 29','1003.4728':r'^Conjecture 22','1003.5875':r'^Conjecture 12.2','1004.0582':r'^Conjecture 3','1004.5167':r'^Conjecture .*Buzzard','1005.5469':r'^Conjecture 8','1006.1226':r'^Conjecture 1.1','1006.1324':r'^Conjecture (18|19)\. Let T1','1006.1686':r'^Corollary 1.4','1007.1670':r'^Conjecture 1. The class','1008.2134':r'^Conjecture 1 The matrix','1009.4062':r'^Conjecture 7.2','1010.4717':r'^Conjecture 4.1','1010.5167':r'^Conjecture 8\.','1010.5841':r'^Conjecture 5.1','1011.3236':r'^Conjecture (3.6|4.6)\.','1212.3345':r'^Construction 5\.|^Proposition [67]\.','1605.00273':r'^Conjecture 1.[56]\.|^Proposition 5.3\.'}
inv=[];excerpts=[]
for f in sorted(s.glob('*v*.txt')):
 a=f.stem.split('v')[0]
 if a not in selectors:continue
 l=f.read_text().splitlines();ranges=[]
 for i,t in enumerate(l):
  if re.search(selectors[a],t):
   lo=max(0,i-1);hi=min(len(l),i+(37 if a=='1009.4062' else 11));b=('\n'.join(l[lo:hi])+'\n').encode();ranges.append({'line_start':lo+1,'line_end':hi,'passage_sha256':sha(b)})
   excerpts += [f'\n## {f.name}:{lo+1}–{hi}\n'+b.decode()]
 inv.append({'file':str(f.relative_to(p)),'sha256':sha(f.read_bytes()),'matched_target_ranges':ranges,'read_depth':'target-passages reviewed where identified; no complete proof audit; see per-ID results','absence_note':('No matched target label. v4 Petersen target absent; v1 Sakhnovich target not the later monotonicity formulation; other absence requires manual renumbering check.' if not ranges else None)})
(p/'version-read-inventory.json').write_text(json.dumps(inv,indent=2));(p/'version-target-excerpts.md').write_text('\n'.join(excerpts))
# Save dated bounded registry screening; do not confuse no index hit with no public proof.
reg=[]
for n in ['registry-pool.yml','registry-pool.lean']:
 f=s/n;l=f.read_text().splitlines();matches=[]
 for i,t in enumerate(l):
  if re.search('crosspolytop|zigzag.word|2.left.nest|Novosibirsk|ayyer|mallick|Borcea|chooser.picker|duplicate.leaf|cyclic.defect|prolongation.intersection',t,re.I):matches.append({'line':i+1,'text':t})
 reg.append({'file':str(f.relative_to(p)),'sha256':sha(f.read_bytes()),'matches':matches})
oid=re.search(r'"currentOid":"([a-f0-9]{40})"',(s/'registry-openai.html').read_text()).group(1)
(p/'registry-screen.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'openai_public_root_oid':oid,'leanpool_indexes':reg,'limits':['No GitHub API calls; inherited rate limit respected.','Root page is not a complete current code tree. Index searches are routing only. No global absence or current complete-tree claim.','Current trureturing search yielded a target-specific prior warning at 320280; direct requests 403, stopped.','No new candidate, so no matched theorem body treated as novelty clearance.']},indent=2))
print('history output',len(z.stdout),'bytes; target versions',len(inv),'current root',oid);print(resource.getrusage(resource.RUSAGE_SELF))
