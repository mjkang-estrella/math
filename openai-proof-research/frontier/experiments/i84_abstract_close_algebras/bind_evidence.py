"""Preseal acquisition/binding helper. Not called by verifier."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i84_abstract_close_algebras'
sha=lambda b:hashlib.sha256(b).hexdigest()
def dump(name,x):(S/name).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def read(p):return (ROOT/p).read_bytes()
domain=json.loads(read('frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json'))
family=['Close-Separable-Cstar-Algebras-Without-Spatial-Conjugacy-October-5-2026','Near-Inclusions-of-von-Neumann-Algebras-Without-Small-Spatial-Embeddings-October-5-2026','Universal-strong-Kadison-Kastler-stability-September-23-2026','Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026','An-isomorphism-of-the-free-group-factors-September-23-2026','The-trace-cone-classifies-Razak-Jacelon-stabilizations-September-25-2026','A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026','Unitarizability-Implies-Amenability-for-Countable-Groups-September-23-2026']
selected=[x for x in domain if x['path'].split('/')[1] in family];dump('selected-domain.json',selected)
P='frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/'
passages=[]
def bind(local,start,end,label,role):
 b=read(local); lines=b.decode('utf8').splitlines(keepends=True); assert 1<=start<=end<=len(lines),(local,end,len(lines))
 text=''.join(lines[start-1:end]);passages.append(dict(local=local,start=start,end=end,label=label,role=role,source_sha256=sha(b),sha256=sha(text.encode()),text=text))
close=P+family[0]+'/build/main.tex'
for a,b,l,r in [(49,141,'scope and theorem','accepted source'),(143,244,'prop:sequences including complete proof','accepted operation; original §9 audit'),(246,308,'def:tensor; lem:invariant; cor:obstruction','accepted tensor and closure operation'),(310,438,'lem:tree complete proof','actual finite-rank extraction and uniform distance'),(448,471,'lem:absorption','accepted absorption'),(473,528,'eq:D; eq:P; lem:ambient','actual coordinate algebra and commutant'),(530,566,'lem:good-inclusion','accepted good tensor test'),(568,633,'lem:free-norm; lem:bad-inclusion','accepted finite-family obstruction'),(635,661,'assembly','two-sided closeness and common closure')]:bind(close,a,b,l,r)
bind(P+family[1]+'/build/sections/introduction.tex',1,117,'near main theorem and scope','one-sided versus two-sided comparison')
bind(P+family[1]+'/build/sections/circle.tex',1,132,'prop:circle finite-path operations','strong companion; finite-rank already explicit')
bind(P+family[2]+'/build/sections/01-introduction.tex',1,99,'thm:main; representation distinctions','strongest positive companion hypotheses')
bind(P+family[2]+'/build/sections/03-amplification.tex',70,120,'lem:trace-transfer','normal representation assumed')
bind(P+family[2]+'/build/sections/06-modular-preparation.tex',1,82,'common amplification and trace scaling','lower operation comparison')
bind(P+family[2]+'/build/sections/10-comparison.tex',1,98,'uniformity and representation comparison','lower operation comparison')
bind(P+family[3]+'/build/sections/introduction.tex',1,96,'thm:similarity','does not identify arbitrary representations')
bind(P+family[3]+'/build/sections/preliminaries.tex',202,254,'lem:cyclic-factorization','normal faithful restriction and multiplicity')
bind(P+family[4]+'/build/sections/flow.tex',320,405,'Surjectivity, normal extension, and estimates','strongest trace-GNS operation antecedent')
bind(P+family[5]+'/build/sections/01-introduction.tex',1,97,'thm:main and extended trace cone','nuclearity and changed algebra; nondense trace scope')
bind(P+family[6]+'/build/sections/introduction.tex',1,66,'na:main scope','nonseparable representation uniqueness not applied')
bind(P+family[6]+'/build/sections/states.tex',1,26,'GNS and universal normal extension','bidual versus represented closure distinction')
i82='frontier/iterations/i82-measured-group-operator-discovery.md'; lines=read(i82).decode().splitlines();a=next(i+1 for i,s in enumerate(lines) if s.startswith('## 9.'));b=next(i for i,s in enumerate(lines) if s.startswith('## 10.'));bind(i82,a,b,'ORIGINAL I82 section 9','independent scoped audit')
for f,a,b,l in [('pytlik-szwarc.pdf.txt',195,250,'Theorem 1 finite rank'),('cssww-v1.pdf.txt',85,119,'Theorems A/B and nonseparable predecessor'),('cssww-v1.pdf.txt',1510,1539,'Theorem 5.4'),('rwi-v2.pdf.txt',20,70,'relative weak injectivity definition'),('rwi-v2.pdf.txt',260,279,'Theorem 4.1'),('yamagami-published.pdf.txt',20,102,'finite generator domain'),('yamagami-published.pdf.txt',478,511,'Proposition 2.7 and Corollary 2.8'),('yamagami-published.pdf.txt',660,699,'Theorem 2.11 and topology'),('powers-skandalis.pdf.txt',12,45,'Theorems I and II, Powers group hypotheses'),('powers-skandalis.pdf.txt',63,145,'Powers averaging and Proposition 2')]:bind('frontier/sources/i84_abstract_close_algebras/primary/'+f,a,b,l,'external primary comparison; not a stipulated premise')
bind('frontier/sources/i82_measured_group_operator_discovery/primary/bot.pdf.txt',641,708,'Theorem 4.6 and actual finite-path operation','external primary body reused by immutable reference')
dump('passages.json',passages)
# Bind originals once by complete file and Git blob, not just excerpts.
tree=json.loads(read('sources/preprints-tree.json'));blobs={x['path']:x['sha'] for x in tree['tree'] if x['type']=='blob'}
locals_used={x['local'] for x in passages};refs=[]
for x in domain:
 if x['local'] in locals_used and x['kind']=='corpus':refs.append(dict(x,git_blob=blobs[x['path']],url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']))
dump('source-references.json',refs)
contracts=[]
for label in ['thm:main','prop:sequences','lem:invariant','lem:tree','lem:absorption','lem:ambient','lem:good-inclusion','lem:bad-inclusion']:
 text=read(close).decode();lines=text.splitlines(keepends=True);a=next(i for i,s in enumerate(lines) if '\\label{'+label+'}' in s);b=next(i for i in range(a,len(lines)) if re.search(r'\\end\{(theorem|lemma|proposition)\}',lines[i]));block=''.join(lines[a:b+1]);contracts.append(dict(local=close,label=label,start=a+1,end=b+1,text=block,sha256=sha(block.encode())))
dump('source-contracts.json',contracts)
refs=json.loads((S/'immutable-references.json').read_text())
for p in ['frontier/sources/i82_measured_group_operator_discovery/primary/bot.pdf','frontier/sources/i82_measured_group_operator_discovery/primary/bot.pdf.txt','frontier/sources/i82_measured_group_operator_discovery/primary-requests.jsonl']:
 if p not in {x['path'] for x in refs}:refs.append(dict(path=p,sha256=sha(read(p))))
dump('immutable-references.json',refs)
versions=[]
for name in ['cssww','rwi','bot','yamagami']:
 p='frontier/sources/i84_abstract_close_algebras/primary/'+name+'-page.html';text=read(p).decode();match=re.search(r'<meta property="og:url" content="([^"]+)"',text);h=re.search(r'<div class="submission-history">(.*?)</div>',text,re.S)
 versions.append(dict(local=p,sha256=sha(read(p)),observed_version_url=match.group(1) if match else None,history_html=h.group(0) if h else None))
dump('versions.json',versions)
imgs=[]
for page in [276,280]:
 local=f'frontier/sources/i84_abstract_close_algebras/primary/haagerup-p{page}.png';imgs.append(dict(pdf='frontier/sources/i84_abstract_close_algebras/primary/haagerup.pdf',page_index_1based=page-270,dpi=130,local=local,sha256=sha(read(local)),method='pdftoppm -f N -l N -r 130 -png -singlefile PDF PREFIX',read_scope='Complete displayed page visually inspected. p276 Theorem 2.3 and hypotheses; p280 end of proof and beginning of section 3.'))
dump('visual-readings.json',imgs)
dump('inherited-primary.json',[dict(local='frontier/sources/i82_measured_group_operator_discovery/primary/bot.pdf',sha256=sha(read('frontier/sources/i82_measured_group_operator_discovery/primary/bot.pdf')),extraction='frontier/sources/i82_measured_group_operator_discovery/primary/bot.pdf.txt',extraction_sha256=sha(read('frontier/sources/i82_measured_group_operator_discovery/primary/bot.pdf.txt')),version='arXiv:1010.0565v1')])
print(json.dumps(dict(passages=len(passages),contracts=len(contracts),selected_files=len(selected),selected_pdfs=sum(x['kind']=='outside_pdf' for x in selected),source_files=len(refs))))
