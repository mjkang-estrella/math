from pathlib import Path
import json,re,hashlib,html,datetime
S=Path('frontier/sources/i82_measured_group_operator_discovery')
def sha(b):return hashlib.sha256(b).hexdigest()
xs=json.load(open(S/'selected-domain.json'));tree={x['path']:x for x in json.load(open('sources/preprints-tree.json'))['tree']}
contracts=[];passages=[];source_refs=[]
for x in xs:
 b=Path(x['local']).read_bytes();assert sha(b)==x['sha256']
 if x['kind']!='corpus':continue
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==tree[x['path']]['sha']
 source_refs.append(dict(path=x['path'],local=x['local'],sha256=sha(b),git_blob=tree[x['path']]['sha'],url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']))
 t=b.decode(); lines=t.splitlines(keepends=True)
 for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}.*?\\end\{\1\}',t,re.S):
  contracts.append(dict(path=x['path'],local=x['local'],start=t[:m.start()].count('\n')+1,end=t[:m.end()].count('\n')+1,text=m.group(),sha256=sha(m.group().encode())))
 # Bind complete source-file text for key operational reads, no copying.
 if re.search(r'(Equivariant-Jiang|Close-Separable|A-group-without-fixed-price|Strong-Ulam|Unitarizability-Implies|Near-Inclusions|Universal-strong-Kadison|Cuntz-comparison)',x['path']) and x['path'].endswith('.tex'):
  passages.append(dict(local=x['local'],start=1,end=len(lines),sha256=sha(''.join(lines).encode()),scope='full file available; report identifies used operations'))
(S/'source-references.json').write_text(json.dumps(source_refs,indent=2)+'\n');(S/'source-contracts.json').write_text(json.dumps(contracts,indent=2)+'\n')
# Local external passages actually compared.
for name,start,end in [('banna-cebron.pdf.txt',185,277),('abert-weiss.pdf.txt',45,87),('szabo-published.pdf.txt',198,239),('bot.pdf.txt',1,170)]:
 p=S/'primary'/name;l=p.read_text().splitlines(keepends=True);passages.append(dict(local=str(p),start=start,end=end,sha256=sha(''.join(l[start-1:end]).encode()),scope='primary comparison'))
# The BOT theorem locations are searched rather than guessed.
p=S/'primary/bot.pdf.txt';l=p.read_text().splitlines(keepends=True)
for i,line in enumerate(l):
 if 'Theorem 3.1.' in line or 'Theorem 3.2.' in line:
  a=max(1,i-2);z=min(len(l),i+100);passages.append(dict(local=str(p),start=a,end=z,sha256=sha(''.join(l[a-1:z]).encode()),scope='amenable global and relative theorem and averaging'))
(S/'passages.json').write_text(json.dumps(passages,indent=2)+'\n')
versions=[]
for p in sorted((S/'primary').glob('*page.html')):
 t=p.read_text();plain=html.unescape(re.sub('<[^>]+>',' ',t));plain=re.sub(r'\s+',' ',plain)
 m=re.search(r'Submission history(.*?)(?:Access Paper|Full-text links|Current browse context)',plain)
 versions.append(dict(local=str(p),sha256=sha(p.read_bytes()),submission_history=m.group(1) if m else None,arxiv_versions=sorted(set(re.findall(r'\b\d{4}\.\d{4,5}v\d+\b',t)))))
(S/'versions.json').write_text(json.dumps(versions,indent=2)+'\n')
(S/'preseal-events.json').write_text(json.dumps([
 {'event':'prior routes retained','detail':'Bernstein polynomial degree/coefficient growth failed to establish a polynomial row bound; it is not a lower bound or target counterexample.'},
 {'event':'sample-splitting correction','detail':'Nonidentical rows need not have matching covariance; use same rows with Lp control.'},
 {'event':'positive-covariance correction','detail':'Do not take square roots of the symmetrized empirical matrix. An actual Pauli-block matrix has quadratic form -2. Use unsymmetrized positive Gram matrix.'},
 {'event':'safety budget','detail':'Tentative 2^180 prefactor enlarged to 2^200 before any theorem was sealed; no old artifacts changed.'},
 {'event':'tool syntax failure','detail':'First large report-writing functions.exec invocation failed SyntaxError: missing ) after argument list, before shell execution; ls verified report did not exist. Successful smaller apply_patch writes followed.'},
 {'event':'diagnostics first run','detail':'Initial exact diagnostic program passed unchanged. Output retained.'},
 {'event':'initial preparation long run','detail':'Output-only printing omitted the live session ID; process was inspected read-only and allowed to finish, without duplicate execution.'}
],indent=2)+'\n')
print('contracts',len(contracts),'passages',len(passages),'source refs',len(source_refs));print(json.dumps(versions,indent=2))
