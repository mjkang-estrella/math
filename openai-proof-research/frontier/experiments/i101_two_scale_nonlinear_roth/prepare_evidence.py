"""I101 evidence preparation only; not imported by read-only verifier."""
from pathlib import Path
import json,hashlib,re,subprocess
S=Path('frontier/sources/i101_two_scale_nonlinear_roth');E=Path('frontier/experiments/i101_two_scale_nonlinear_roth');I=Path('frontier/sources/i99_quantitative_arithmetic_patterns_discovery')
def sha(b):return hashlib.sha256(b).hexdigest()
def write(p,v):p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
P='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
IP=P+'A-power-saving-for-intersective-polynomial-differences-with-an-exponent-depending-only-on-the-degree-October-5-2026/build/manuscript/sections/'
AP=P+'Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/build/'
L=str(I/'literature')+'/'
requests=[
('original-report','frontier/iterations/i99-quantitative-arithmetic-patterns-discovery.md',1,None,'LF','complete original report and all original proof endings',None),
('IP-main',IP+'introduction.tex',1,34,'LF','fixed-square input contract; no upstream truth audit',None),
('IP-mixing',IP+'tuples.tex',526,600,'LF','complete conditional-mixing proof through end',None),
('IP-kernel-contract',IP+'kernel.tex',1,70,'LF','ordered pair rather than common-parameter triple',None),
('IP-higher-lifts',IP+'kernel.tex',372,477,'LF','complete coefficient comparison proof end',None),
('IP-transfer-end',IP+'kernel.tex',479,539,'LF','complete comparison and ordered Plancherel proof ends',None),
('AP-cells',AP+'sections/01-setup.tex',1,231,'LF','cell definitions, triangular recurrence, absolute rule and proof end',None),
('AP-lifting-statement',AP+'foundations/04-counting.tex',586,649,'LF','relative lifting contract; statement not positive nonlinear input',None),
('AP-scalar-transfer',AP+'foundations/06-transfer.tex',1,50,'LF','fixed scalar score transfer statement only; not invoked positively',None),
('AP-lifting-end',AP+'foundations/07-lifting.tex',1184,1394,'LF','complete final lifting proof, base support check and finite-depth resource recurrence',None),
('PP-increment-statement',L+'peluse-prendiville.txt',286,366,'splitlines','increment contract and complete iteration ending','https://arxiv.org/abs/2003.04122v2'),
('PP-increment-proof',L+'peluse-prendiville.txt',612,663,'splitlines','complete Lemma 2.1 proof through ending','https://arxiv.org/abs/2003.04122v2'),
('SW-inverse-contract',L+'shao-wang-v2.txt',559,615,'LF','all-slot inverse and allowed shorter M; statement only','https://arxiv.org/abs/2505.16822v2'),
('SW-short-M-proof',L+'shao-wang-v2.txt',1167,1255,'LF','complete short-window localization and gluing proof end','https://arxiv.org/abs/2505.16822v2'),
('SW-increment-proof',L+'shao-wang-v2.txt',1570,1986,'LF','complete section 4 regularity, increment and terminal proof ending','https://arxiv.org/abs/2505.16822v2'),
('AS-final-transfer',L+'altman-sawhney-v1.txt',2044,2477,'LF','complete section 2.4 model lemma and terminal transfer ending; earlier inputs not independently audited','https://arxiv.org/abs/2506.13010v1'),
('PPS-main',str(S/'literature/pps-v1.txt'),64,99,'LF','main density/popular theorem contracts','https://arxiv.org/abs/2407.08338v1'),
('PPS-final',str(S/'literature/pps-v1.txt'),662,718,'LF','complete section 7 count and 1D deduction through proof end','https://arxiv.org/abs/2407.08338v1'),
]
rows=[]
for key,p,a,b,conv,note,url in requests:
 raw=Path(p).read_bytes();text=raw.decode();lines=text.splitlines() if conv=='splitlines' else text.split('\n')
 if conv=='LF' and lines[-1]=='':lines.pop()
 b=b or len(lines)
 assert b<=len(lines),(key,b,len(lines))
 excerpt='\n'.join(lines[a-1:b])+'\n'
 if p.startswith(P):url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/'+p[len(P):]
 rows.append({'key':key,'path':p,'start':a,'end':b,'line_convention':conv+'; excerpt newline-joined with final newline','source_sha256':sha(raw),'excerpt_sha256':sha(excerpt.encode()),'total_lines_in_convention':len(lines),'url':url,'scope':note})
write(S/'passages.json',rows)
expressions=[r'non.?linear.{0,16}Roth',r'two.?scale|block.condition|cut.norm',r'conditional.mixing|higher.conductor|normal.character',r'(short|local).{0,30}(window|parameter|cutoff)']
rx=[re.compile(e,re.I) for e in expressions];hits=[[] for _ in rx]
domain=json.loads((I/'search-domain.json').read_text())
for row in domain:
 for ln,line in enumerate(Path(row['local']).read_bytes().decode(errors='replace').splitlines(),1):
  for j,r in enumerate(rx):
   for m in r.finditer(line):hits[j].append({'path':row['path'],'line_splitlines':ln,'start':m.start(),'match':m.group(),'text':line})
write(S/'lexical-search.json',[{'expression':e,'flags':'IGNORECASE','occurrences':h} for e,h in zip(expressions,hits)])
write(S/'contracts.json',{'positive_input':{'source':'IP thm:main','polynomial':'t^2 fixed once','constants':'C>=max(C_h,N_h^c,1), 0<c<=min(c_2,1/4); independent of q,D','domain':'every integer length L>=1, positive integer square differences','uses':['(1)-(4)','(13)','(20)']},'comparison_only':['IP conditional mixing and higher-lift scalar kernel','AP absolute increment (linear progression-free support)','AP relative lifting (same support plus absolute-rule/sampler contracts)','AP fixed scalar-score transfer (requires already productive patch)','PP v2 density increment','SW v2 inverse/short M/regularity/increment','AS v1 integer transfer','PPS v1 popular count'],'original_verdicts':{k:'ORIGINAL PASS WITHOUT REPAIRS' for k in ['A1','A2','A3 stated range','p^2 normal character','A4','A5 complex/real kernel','B1','B2','B3','B4','height/local/support counterexamples']},'pass_after_repairs':[],'fail_at_original_scope':[],'contribution':'technical only; no nomination; C99 unproved and unrefuted'})
result=subprocess.run(['python3','-B',str(E/'diagnostics.py')],check=True,capture_output=True,text=True);write(E/'diagnostics-result.json',json.loads(result.stdout))
result=subprocess.run(['python3','-B','frontier/experiments/i99_quantitative_arithmetic_patterns_discovery/verify.py'],capture_output=True,text=True)
write(E/'original-i99-replay.json',{'command':result.args,'exit_code':result.returncode,'stdout':result.stdout,'stderr':result.stderr})
assert result.returncode==0
print(json.dumps({'passages':len(rows),'search_counts':[len(h) for h in hits],'original_replay':json.loads(result.stdout)['status']}))
