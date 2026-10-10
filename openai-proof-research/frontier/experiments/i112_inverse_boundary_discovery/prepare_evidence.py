"""Author preparation only; NOT the offline verifier. Writes only owned I112 paths."""
from pathlib import Path
import hashlib,json,subprocess

ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i112_inverse_boundary_discovery'
E=ROOT/'frontier/experiments/i112_inverse_boundary_discovery'
def sha(b):return hashlib.sha256(b).hexdigest()
def put(p,d):p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
D=json.loads((S/'search-domain.json').read_text())
reads=[]
def passage(p,start,end,convention,labels,url):
    raw=(ROOT/p).read_bytes();t=raw.decode('utf-8')
    lines=t.splitlines() if convention=='splitlines' else t.split('\n')
    assert 1<=start<=end<=len(lines)
    text='\n'.join(lines[start-1:end])
    reads.append({'local':p,'start':start,'end':end,'convention':convention,
                  'file_sha256':sha(raw),'passage_sha256':sha(text.encode()),
                  'labels':labels,'url':url,'passage':text})
for x in D:
    p=x['path'];name=p.split('/')[-1]
    yes=('/sections/' in p and p.endswith('.tex') and
         ('Global-Uniqueness-for-the-Smooth-Isotropic' in p or
          ('Determination-of-a-metric-and-a-unitary' in p and name in ['01-introduction.tex','02-boundary.tex','06-matrix.tex','07-global.tex']) or
          ('Smooth-Anisotropic-Uniqueness' in p and name in ['01-introduction.tex','06-bootstrap.tex'])))
    if yes:
        t=(ROOT/x['local']).read_text()
        import re
        labels=re.findall(r'\\label\{([^}]+)\}',t)
        passage(x['local'],1,len(t.splitlines()),'splitlines',labels,
                'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+p)
for name,intervals,url,labels in [
 ('1708.06307v1.pdf.txt',[(1,634)],'https://arxiv.org/pdf/1708.06307v1',['Theorems 1-3','Propositions 3.1,3.3,5.1,6.1; proofs through endings']),
 ('2609.20134v1.pdf.txt',[(1,50),(103,212),(585,1040)],'https://arxiv.org/pdf/2609.20134v1',['Theorems 1.1-1.3','torsional/separation/quasianalytic proofs through endings']),
 ('1902.04838v2.pdf.txt',[(44,136)],'https://arxiv.org/pdf/1902.04838v2',['Assumptions 1-2; Theorems 1.1-1.3; contract screen only']),
 ('1708.00591v1.pdf.txt',[(181,230)],'https://arxiv.org/pdf/1708.00591v1',['Theorem 1.1; statement screen only']),
 ('lame-carleman.pdf.txt',[(1030,1072)],'https://www.ms.u-tokyo.ac.jp/preprint/pdf/2003-19.pdf',['Theorems 2-3; statement screen only'])]:
    for a,b in intervals:passage(str((S/'literature'/name).relative_to(ROOT)),a,b,'LF',labels,url)
put(S/'read-manifest.json',{'warning':'Passage identity is not semantic proof verification; only the stated ranges are claimed read.','passages':reads})
immutable=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json',
 'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json',
 'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json']
put(S/'immutable-references.json',[{'path':p,'sha256':sha((ROOT/p).read_bytes())} for p in immutable])
put(S/'failures.json',[
 {'stage':'initial read without explicit repository cwd','raw':'cat: AGENTS.md: No such file or directory; cat: frontier/TEN-FINDINGS.md: No such file or directory','resolution':'repeated with explicit workdir; no writes occurred'},
 {'stage':'first manuscript-title filter','raw':'no titles printed: incorrectly required no slash although paths start preprints/','resolution':'corrected to path.count("/")==1; tree itself was not changed'},
 {'stage':'publisher fetch','raw':'HTTP Error 403: Forbidden','url':'https://onlinelibrary.wiley.com/doi/10.1002/mma.70764','resolution':'browser abstract retrieved; full proof unavailable, no quantitative theorem used'},
 {'stage':'optional MathDB HTML parser','raw':"ModuleNotFoundError: No module named 'bs4'",'resolution':'standard-library regex inspected links; successful prior downloads retained'},
 {'stage':'MathDB individual-page browser open','raw':'Internal Error ()','url':'https://mathdb.com/p/363616/anisotropic-calderon-conjecture-at-zero-frequency','resolution':'only listing used as observed evidence'},
 {'stage':'PDF extraction diagnostic','raw':'Syntax Warning: Mismatch between font type and embedded font file','resolution':'extractions exited successfully; selected PDFs replayed before seal'},
 {'stage':'tool output length','raw':'some source displays were truncated','resolution':'re-read missing substantive ranges; statement-only screens explicitly labeled; no full-corpus semantic claim'}])
put(E/'diagnostic-result.json',json.loads(subprocess.check_output(['python','-B',str(E/'diagnostics.py')],cwd=ROOT)))
put(S/'pdf-replay.json',[
 {'pdf':str((S/'literature'/f'{i}.pdf').relative_to(ROOT)),
  'text':str((S/'literature'/f'{i}.pdf.txt').relative_to(ROOT)),
  'command':['pdftotext','-layout','PDF','-'],'convention':'raw stdout bytes; text passages use LF lines'}
 for i in ['1708.06307v1','2609.20134v1']])
owned=sorted(str(p.relative_to(ROOT)) for base in [S,E] for p in base.rglob('*') if p.is_file())
report='frontier/iterations/i112-inverse-boundary-discovery.md'
owned+= [report,str((S/'inventory.json').relative_to(ROOT)),str((E/'validation.json').relative_to(ROOT))]
owned=sorted(set(owned)-{str((S/'seal.json').relative_to(ROOT))})
put(S/'inventory.json',{'owned_paths':owned,'seal_path':str((S/'seal.json').relative_to(ROOT)),
 'allowed_live_ledger_drift':['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'],
 'selective_pdf_replay_limit':2})
print(json.dumps({'prepared':True,'read_passages':len(reads),'owned_before_seal':len(owned)}))
