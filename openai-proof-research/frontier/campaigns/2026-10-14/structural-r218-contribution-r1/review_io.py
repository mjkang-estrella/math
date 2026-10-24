from pathlib import Path
import json,hashlib,re,fnmatch,stat,sys
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
R=P/'frontier/campaigns/2026-10-14/structural-r218-contribution-r1'
A=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r218'
M=json.loads((A/'MANIFEST.json').read_bytes())
W=[f'*{kind}*{r}{n}*' for kind,lo,hi in [('analytic',144,195),('arithmetic',116,168),('structural',151,218)] for n in range(lo,hi+1) for r in ['r','']]
W+='*t126s161* *t360s147* *t337a161* *h138-* *t185r144-* *t185144-* *t177c143-* *t373e135-* *k369r134-* *k369134-* *t088p133-* *s176a* *owner-recovery*'.split()
S='corpus source primary history derivative search inventory fixture control extract render vendor build copy copied frozen role formal manuscript release parent private input upstream shortlist context fetched scratch preprint catalogue catalog receipt brief intake bundle recovery manifest authentication task work family-title literature venv site-packages packet payload archive cache download external third-party hits index navigation audit log provenance evidence ledger helper readme direct.tex pinned- scan snapshot submissions retention retrieve record_evidence validation invocation checkpoint-output journal status progress final report handoff disposition integrity checkpoint contribution proof-role ten-findings twenty-findings new-ten sharedtasks terminal-summary summary.json summary sawin-2018 tao-teravainen acquire checks verify seal_once exact_moments tools scripts verification prepare metadata contracts bind_passages replay stderr author-completion reading-limit reading-limits verifier fetch-family seal-family isolation reading-and-failures compound-history write_notes diagnostics result-helper reading failure outcome completion retrieval seal diagnostic history-scout history-focused screen review proof-r check- freeze rights dispatch integration reproduce reproduction resume launch scout dependencies node_modules .git __pycache__ toolkit canonical-bindings capture.py bind.py publication check .diff state_probe consolidate activity matrix-disk-discovery glm-calibration frontier/experiments/i251_quantitative_scalarization_proof frontier/experiments/i291_crouzeix_counterexample_proof frontier/experiments/i316_quantitative_amplification_proof i299_gaussian_stability_proof i304_global_soft_proof scope.json'.split()
D='*history[0-9]* *further-history-* *screen-* *screen[0-9][0-9][0-9]* *role* *proof-r[0-9]* *check* *freeze* *summary* *rights* *toolkit* *canonical-bindings* *capture.py* *bind.py*'.split()
assert len(W)==359 and len(S)==162
G=json.loads((A/'private/guards.json').read_bytes())
assert set(W)==set(G['wildcards']) and set(S)==set(G['substrings']) and set(D)==set(G['derivative_wildcards'])
def excluded(rel):
 s=rel.casefold();return any(fnmatch.fnmatchcase(s,w) for w in W+D) or any(x in s for x in S)
def allowed(p):
 p=Path(p)
 if p.is_relative_to(R):return True
 if p.is_relative_to(A):return p.relative_to(A).as_posix() in set(M['files'])|{'MANIFEST.json','REPORT.md','ANCHORS.json'}
 return not excluded(p.relative_to(P).as_posix())
def parsed(p):
 p=Path(p);assert allowed(p),p;assert not p.is_symlink();b=p.read_bytes(); ls=b.splitlines(keepends=True); offsets=[0]
 for l in ls:offsets.append(offsets[-1]+len(l))
 assert offsets[-1]==len(b)
 return b,ls,offsets
editor=re.compile(r'acknowledg|acknowleg|aknowledg|acknowled|licen[cs]e|all rights reserved|downloaded from|publisher.?s note|private communication|personal communication|we thank|author thanks|grateful|discussions with',re.I)
heading=re.compile(rb'^\s*(?:\\(?:sub)*section\*?\{|#{1,6}\s|(?:\d+\.)+\d*\s+[A-Z]|References\s*$|Bibliography\s*$)',re.I)
def classify(p):
 b,ls,o=parsed(p); print('CLASSIFY',str(p),'bytes',len(b),'lines',len(ls))
 for i,l in enumerate(ls):
  t=l.decode('utf8','replace').rstrip('\r\n')
  if editor.search(t): print(f'{i+1} [{o[i]},{o[i+1]}) [EDITORIAL MARKER: CONTENT WITHHELD]')
  elif heading.search(l): print(f'{i+1} [{o[i]},{o[i+1]}) '+t[:600])
def show(p,lo,hi,classification):
 b,ls,o=parsed(p);assert 1<=lo<=hi<=len(ls);out=b''.join(ls[lo-1:hi]);assert out==b[o[lo-1]:o[hi]]
 entry={'path':str(Path(p).relative_to(P)),'sha256':hashlib.sha256(b).hexdigest(),'lines':[lo,hi],'bytes':[o[lo-1],o[hi]],'classification':classification}
 with (R/'private/reads.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
 print(json.dumps(entry))
 if '/primary/' in str(p) and str(p).endswith('.txt'):
  skipped=[]
  for i in range(lo-1,hi):
   t=ls[i].decode('utf8');z=t.strip(' \t\r\n\f');letters=''.join(c for c in z if c.isalpha())
   if (len(letters)>8 and letters.isupper() and not any(c in z for c in '=∧∈∩∪⊕')) or z.isdigit():
    skipped.append([i+1,o[i],o[i+1]]);continue
   print(t.replace('\f',''),end='')
  with (R/'private/reads.jsonl').open('a') as f:f.write(json.dumps({'running_headers_excluded':skipped,'path':entry['path']})+'\n')
 else:print(out.decode('utf8'))
if __name__=='__main__':
 cmd=sys.argv[1];p=Path(sys.argv[2])
 if not p.is_absolute():p=A/p
 if cmd=='classify':classify(p)
 elif cmd=='show':show(p,int(sys.argv[3]),int(sys.argv[4]),sys.argv[5])
