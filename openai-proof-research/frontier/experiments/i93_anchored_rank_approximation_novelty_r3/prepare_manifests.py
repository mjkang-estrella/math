"""Preseal manifest writer. Refuses execution after the one seal exists."""
from pathlib import Path
import json,hashlib,subprocess
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i93_anchored_rank_approximation_novelty_r3'
assert not (S/'seal.json').exists()
def dump(name,value):(S/name).write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n')
def digest(p):return hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
def record(p,start=1,end=None,scope='complete used operation'):
 ls=(ROOT/p).read_text().splitlines(keepends=True);end=end or len(ls)
 assert 1<=start<=end<=len(ls)
 return dict(path=p,start=start,end=end,scope=scope,line_convention='str.splitlines(keepends=True)',sha256=digest(p),passage_sha256=hashlib.sha256(''.join(ls[start-1:end]).encode()).hexdigest())
old='frontier/sources/i90_anchored_rank_approximation'
families=json.loads((ROOT/old/'families.json').read_text());dump('families.json',families)
corpus='frontier/sources/i14_spectral_width_novelty_r3/corpus/'
f=corpus+'preprints/'+families['F']+'/build/sections/'
reads=[record(f+x+'.tex') for x in ['introduction','blocks','reduction','operators','walks','tests','references']]
c=corpus+'preprints/'+families['C']+'/build/'
reads.extend(record(c+x+'.tex') for x in ['preliminaries','coefficient','walsh','approximation'])
reads.append(record(c+'introduction.tex',1,140,'theorem hypotheses and comparison scope'))
e=corpus+'preprints/'+families['E']+'/build/sections/'
reads.extend(record(e+x+'.tex') for x in ['02-matrix-contract','03-compression'])
reads.append(record(corpus+'preprints/'+families['U']+'/build/nuclear-finiteness.tex',scope='complete screened operation; not a premise'))
reads.append(record('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside/preprints/'+families['F']+'/main.pdf.txt',626,986,'complete operative F PDF sections 4–6 and abstract criterion'))
for name,a,b,scope in [('well-conditioned',257,560,'full well-conditioned basis and sampling proof comparison'),('naor',199,296,'Proposition 6, Remark 7 and complete proof'),('graph',1400,1534,'Algorithm 1, Lemma 58 and complete consistency proof in v1'),('godefroy-ozawa',199,225,'Proposition 7 complete proof and scope'),('subset-selection',182,210,'determinant/Auerbach comparison only'),('subset-selection',925,957,'Lewis-weight interfaces; cited proofs not imported'),('subset-selection',2930,2955,'Lemma 8.20 scope; cited theorem not imported')]:
 reads.append(record(old+'/external/'+name+'.txt',a,b,scope))
new=S.relative_to(ROOT).as_posix()
for name,a,b,scope in [('widths-v1',880,965,'Proposition 4.4 and Lemma 4.5 full packing proofs'),('widths-v1',1466,1540,'width definitions and Theorem 5.1 proof; no import'),('uap-v1',25,145,'UAP and approximation-number definitions; complete Proposition 1.1 proof')]:reads.append(record(new+'/external/'+name+'.txt',a,b,scope))
reads += [record('frontier/iterations/i90-anchored-rank-approximation.md',scope='complete supplied original report including failed conversions'),record('frontier/iterations/i88-nonlinear-banach-discovery.md',scope='complete original report supplied in assignment'),record('frontier/experiments/i90_anchored_rank_approximation/verify.py',scope='complete read-only verifier'),record('frontier/experiments/i90_anchored_rank_approximation/diagnostics.py',scope='complete inherited finite diagnostics; independent implementation also supplied')]
dump('read-manifest.json',reads)
domain=json.loads((ROOT/'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json').read_text())
selected=[dict(r,alias=next(a for a,f in families.items() if f==r['path'].split('/')[1])) for r in domain if r['path'].split('/')[1] in families.values()]
dump('selected-inventory.json',selected)
p=subprocess.run(['rg','--files','--no-ignore','frontier/sources/i14_spectral_width_novelty_r3/corpus'],cwd=ROOT,capture_output=True,check=True)
(S/'i14-rg-inventory.txt').write_text('\n'.join(sorted(p.stdout.decode().splitlines()))+'\n')
refs={r['path'] for r in reads if not r['path'].startswith(new+'/')}
refs.update(['AGENTS.md','sources/upstream.json','sources/preprints-tree.json','sources/CONTENTS.md',old+'/seal.json','frontier/experiments/i90-parent-verification.json','frontier/iterations/iteration90-anchored-rank-approximation-task.json','frontier/sources/i88_nonlinear_banach_discovery/search-domain.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json','frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/outside-requests.jsonl'])
seal=json.loads((ROOT/old/'seal.json').read_text());refs.update(r['path'] for r in seal['files'])
dump('immutable-references.json',[dict(path=p,bytes=(ROOT/p).stat().st_size,sha256=digest(p)) for p in sorted(refs)])
primary=[]
for name,version,labels in [('well-conditioned','Author-hosted SIAM J. Comput. 38(5), 2009, 2060–2078','Section 3.1 and Theorem 6 in 3.2'),('naor','Author-hosted PDF; not asserted identical to arXiv:2009.11373v2','Proposition 6 and Remark 7'),('graph','arXiv:2006.12760v1, 2020-06-23','Algorithm 1, Lemma 58; publication uses different numbering'),('godefroy-ozawa','arXiv:1201.0847v2','Proposition 7'),('subset-selection','arXiv:2304.09217v1, 2023-04-18','Auerbach paragraph and limited Lemmas 2.2, 8.20 statement comparison')]:
 p=old+'/external/'+name+'.pdf';meta=json.loads((ROOT/(p+'.response.json')).read_text());primary.append(dict(path=p,sha256=digest(p),text=old+'/external/'+name+'.txt',metadata=p+'.response.json',url=meta['url'],version=version,locators=labels,scope='retained immutable I90 primary; not fetched again'))
for name,version,labels in [('widths-v1','arXiv:2111.01341v1, 2021-11-02; title page dated November 3','Proposition 4.4, Lemma 4.5, definitions (5.1)–(5.2), Theorem 5.1'),('uap-v1','arXiv:math/9201220v1, 1990-12-31','definitions and Proposition 1.1')]:
 p=new+'/external/'+name+'.pdf';meta=json.loads((ROOT/(p+'.response.json')).read_text());primary.append(dict(path=p,sha256=digest(p),text=new+'/external/'+name+'.txt',metadata=p+'.response.json',url=meta['url'],version=version,locators=labels,scope='new I93 primary, pinned explicit version URL'))
dump('primary-evidence.json',primary)
dump('evidence-scope.json',dict(pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',tree_entries=13223,manuscripts=749,original_blobs=10373,i14_originals=9340,i79_additional_originals=1033,i79_pdf_text_hash_bindings=776,new_search_counts=[181,534,88],selected_blobs=len(selected),selected_family_counts={a:sum(r['alias']==a for r in selected) for a in families},read_records=len(reads),immutable_reference_count=len(refs),primary_comparisons=len(primary),new_primary_pdf_replays=2,inherited_primary_pdf_replays=6,all_corpus_pdf_reextraction=False,proof_verdict='NOT GIVEN; conditional on I92 original-proof acceptance',contribution_verdict='TECHNICAL',search_limit='Exact byte-level corpus domain; bounded regex and primary literature search, not semantic or worldwide exhaustion'))
print(json.dumps(dict(read_records=len(reads),immutable_references=len(refs),selected_blobs=len(selected),families={a:sum(r['alias']==a for r in selected) for a in families}),indent=2))
