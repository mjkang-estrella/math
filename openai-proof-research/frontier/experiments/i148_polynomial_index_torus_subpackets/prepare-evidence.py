"""One-time evidence assembly; never run after sealing. No inherited code execution."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[3]
S='frontier/sources/i148_polynomial_index_torus_subpackets';E='frontier/experiments/i148_polynomial_index_torus_subpackets'
OLD='frontier/sources/i145_arithmetic_automorphic_discovery'
assert not (R/S/'seal.json').exists()
def load(p):return json.loads((R/p).read_text())
def digest(p):return hashlib.sha256((R/p).read_bytes()).hexdigest()
def save(p,x):(R/p).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
inherit=load(OLD+'/inheritance.json')
inherit['anchors'].append(dict(base=OLD,seal=OLD+'/seal.json',inventory=OLD+'/inventory.json',sha256=digest(OLD+'/seal.json')))
inherit['anchors'].sort(key=lambda a:a['base'])
refs={r['path']:r['sha256'] for r in inherit['immutable']}
for p in load(OLD+'/inventory.json')['owned_paths']+[OLD+'/seal.json']:
 refs[p]=digest(p)
for x in load(S+'/input-freeze.json'):
 if x['path'] not in inherit['live_ledgers']:refs[x['path']]=x['sha256']
inherit['inherited_passages']+=load(OLD+'/read-manifest.json')['passages']
inherit['lexical_records'].append(OLD+'/lexical-search.json')
inherit['scope']='Flat immutable references only; no inherited verifier/diagnostic execution. I146/I147 outputs excluded.'
passages=[]
def passage(p,start=1,end=None,credit='actual semantic reading'):
 b=(R/p).read_bytes();ls=b.decode().splitlines();end=end or len(ls)
 assert 1<=start<=end<=len(ls),(p,start,end,len(ls))
 passages.append(dict(local=p,file_sha256=hashlib.sha256(b).hexdigest(),start=start,end=end,line_count=len(ls),passage_sha256=hashlib.sha256('\n'.join(ls[start-1:end]).encode()).hexdigest(),ending=ls[end-1],convention='splitlines; LF joined without appended LF',credit=credit))
 if not p.startswith(S+'/'):refs[p]=digest(p)
for p in [S+'/direct-context.txt',OLD+'/direct-context.txt','frontier/sources/i142_uniform_algebraic_allocation/direct-context.txt','frontier/sources/i139_diffuse_weighted_positivity/direct-context.txt','frontier/sources/i136_birational_positivity_discovery/context-reading.txt']:
 passage(p)
for p in ['AGENTS.md','sources/upstream.json']:
 passage(S+'/snapshots/'+p)
passage(S+'/snapshots/frontier/TEN-FINDINGS.md',1,65)
passage(S+'/snapshots/frontier/TEN-FINDINGS.md',691,693)
passage(S+'/snapshots/frontier/iterations/README.md',1755)
# Original report/finalized response were supplied in full and decoded in mandatory record.
passage(S+'/snapshots/frontier/iterations/i145-arithmetic-automorphic-discovery.md',credit='full user-supplied original report, identical frozen bytes')
passage(OLD+'/reading-notes.json')
P='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
for name in ['paper','packets','local','analytic','geometry','entropy','adelic']:
 passage(P+'Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/build/'+name+'.tex')
for name in ['introduction','family','hecke','conclusion']:
 passage(P+'Unrestricted-pro-modularity-at-the-prime-two-October-6-2026/build/source/sections/'+name+'.tex')
passage(P+'Fontaine-Mazur-modularity-at-the-prime-2-October-6-2026/build/sections/introduction.tex')
passage(P+'The-Dimension-of-the-Two-Adic-Hecke-Algebra-at-Odd-Level-October-5-2026/build/main.tex',1,160)
for name in ['01-introduction','06-global']:
 passage(P+'Ramanujan-Arthur-Decompositions-of-Cuspidal-Functions-at-Full-Finite-Level-September-24-2026/build/sections/'+name+'.tex')
for name in ['introduction','global','local-criterion','parameters','monodromy','local-coefficients']:
 passage(P+'Temperedness-at-ramified-places-for-globally-generic-exceptional-groups-October-5-2026/build/sections/'+name+'.tex')
passage(P+'The-Restricted-Geometric-Langlands-Equivalence-in-Positive-Characteristic-September-24-2026/build/sections/01-introduction.tex')
passage(P+'Global-Arthur-Enhancements-of-Cuspidal-Excursion-Parameters-October-5-2026/build/manuscript.tex',1,255)
passage(P+'Rationality-of-the-Canonical-Unramified-Arthur-Filtration-September-24-2026/build/sections/01-introduction.tex')
passage(S+'/primary/khayutin-class.txt')
passage(S+'/primary/wu.txt',1,180)
for name,ranges in {'elmv09.txt':[(831,1185),(1196,1275)],'elmv11-current.txt':[(785,885),(2236,2590),(2781,2875)],'aka-current.txt':[(241,489)]}.items():
 for a,b in ranges:passage(OLD+'/primary/'+name,a,b)
passages.sort(key=lambda x:(x['local'],x['start'],x['end']))
save(S+'/read-manifest.json',dict(passages=passages))
inherit['immutable']=[dict(path=p,sha256=h) for p,h in sorted(refs.items())]
save(S+'/inheritance.json',inherit)
domain=load('frontier/sources/i112_inverse_boundary_discovery/search-domain.json')
selected={p['local'] for p in passages if p['local'].startswith(P)}
save(S+'/selected-source-bindings.json',[x for x in domain if x['local'] in selected])
patterns={'polynomial_index_torus':r'(?i)(class[ -]character|class[ -]group|subconvex|weighted.count|weight.moment|shell.sum|local.type|dominated|probability.limit|regulator|Hecke.character|torus.packet)'}
results={k:[] for k in patterns};rx={k:re.compile(v) for k,v in patterns.items()}
# One flat preparation scan, no corpus copy. Replay verifies this against every immutable binding.
for x in domain:
 for i,line in enumerate((R/x['local']).read_bytes().decode('utf-8',errors='replace').splitlines(),1):
  for key,pat in rx.items():
   mm=list(pat.finditer(line))
   if mm:results[key].append(dict(path=x['path'],local=x['local'],splitlines_line=i,text=line,spans=[list(m.span()) for m in mm]))
save(S+'/lexical-search.json',dict(patterns=patterns,results=results,scope='Exact ordered matching-line multisets and occurrence positions; lexical coverage is not semantic reading.'))
receipts=load(S+'/primary/retrievals.json')
for r in receipts:
 if r['path'].endswith('.pdf'):
  p=r['path'][:-4]+'.txt';r.update(text_path=p,text_sha256=digest(p),extraction='pdftotext -layout',extraction_exit=0)
save(S+'/primary/retrievals.json',receipts)
save(S+'/original-audit-checkpoint.json',dict(required_i145_sha256='728019d743f52629c3864135085b0bfaa996f8a1b6f96e3b63ae1a926043db6b',mandatory_context_complete=True,verdict='All original paid I145 claims PASS without repairs at their stated scopes; A145/B145/C145 targets unresolved',inherited_literal_I133_I5='FAIL unchanged; corrected finite-initial-norm version separate',U142_V142='Original PASS at unchanged scopes',scope='Written mathematical assessment under stipulated premises; evidence replay does not certify this verdict.'))
save(S+'/reading-notes.json',dict(mandatory_context_completed_before_audit=True,normalization='Python splitlines; LF joining without appended LF; PDF text is saved pdftotext -layout output, including control characters.',inherited_scope='All complete recursive original briefs/reports/finalized responses/objections/scalars read. Earlier corpus semantic reading is not newly claimed. Original parent review remains selective.',source_scope='All seven prime-degree sections and listed 010/014 proof sections read through endings. Dimension manuscript only 1-160 credited; Arthur monograph only 1-255 credited. Quartic/sextic internals, old Khayutin/LOTZ full proofs, and Wu after 180 not newly read or invoked.',truncated_displays=[{'stream':'I142 direct context','recovery':'285-375'},{'stream':'I136 recursive 4499-line context','recoveries':['18-35','1290-1375','1560-1680']},{'stream':'010 dimension plus companion broad display','action':'Only completely read 1-160 dimension range credited; companion introduction complete.'},{'stream':'Arthur monograph broad combined display','action':'Massive truncation; explicit recovered 1-255 only. Geometric/rational introductions separately complete.'},{'stream':'Khayutin class paper broad display','action':'Recovered 236-500; complete 749 splitlines read.'},{'stream':'root README/frontier README long ledger lines','action':'Frozen but no complete semantic-reading claim for these huge summary lines.'}],failed_commands=[{'action':'Read manifest treated dict as list','result':'AttributeError','recovery':'Used passages key; no evidence lost or changed.'},{'action':'rg elm v09-current name','result':'Nonexistent elmv09-current.txt','recovery':'Correct existing elmv09.txt read.'}],primary=dict(new_pdf_count=2,inherited_pdf_reextractions=0,khayutin='1901.06710v2 complete 749 lines; PDF page 4 rendered and visually inspected',wu='1604.08551v6 introduction 1-180 only; field-dependent constants, not a theorem premise',elmv='0708.1113v2 and math/0607815v1 current metadata checked; old immutable metadata reused',search_scope='Targeted current searches for varying-field class-character subconvexity and class-group torus periods; no worldwide completeness or priority claim. Existing inherited failed TLS and mistaken ciubotaru lead receipts remain unchanged.'),finite_scope='New finite arithmetic and local-module checks only; no universal proof, arithmetic counterexample, acceptance, substantiality or certification.'))
print(json.dumps(dict(passages=len(passages),immutable=len(refs),lexical_lines={k:len(v) for k,v in results.items()},lexical_occurrences={k:sum(len(x['spans']) for x in v) for k,v in results.items()})))
