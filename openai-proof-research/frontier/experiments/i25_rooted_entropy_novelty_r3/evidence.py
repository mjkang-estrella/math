"""Build review-owned, byte-addressed evidence; never write to an input path."""
from pathlib import Path
import json,hashlib,re,html,shutil
S=Path('frontier/sources/i25_rooted_entropy_novelty_r3')
def sha(b): return hashlib.sha256(b).hexdigest()
def out(name,obj): (S/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
inputs=json.loads((S/'inputs.json').read_text())
for path in ['frontier/reviews/i25-rooted-entropy-proof-r2.md','frontier/sources/i25_matching_entropy_improvement_resumed/artifact-seal.json','frontier/sources/i25_matching_entropy_improvement_resumed/original-checkpoint.json','frontier/sources/i25_rooted_entropy_proof_r2/verification.json']:
 p=Path(path)
 if not p.exists(): continue
 q=S/'frozen'/path;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 inputs=[r for r in inputs if r['path']!=path]+[dict(path=path,frozen=str(q),sha256=sha(q.read_bytes()))]
out('inputs.json',inputs)
contracts=[];passages=[]
def passage(path,lo,hi,role):
 b=Path(path).read_bytes();lines=b.decode().splitlines(keepends=True);hi=min(hi,len(lines));t=''.join(lines[lo-1:hi]);passages.append(dict(path=str(path),file_sha256=sha(b),start_line=lo,end_line=hi,role=role,excerpt_sha256=sha(t.encode()),text=t))
for r in json.loads((S/'pinned-manifest.json').read_text()):
 p=Path(r['local_path']);t=p.read_text();lines=t.splitlines()
 if 'Entropy-and-Face' in r['path']: passage(p,1,len(lines),'Read full pinned entropy source, including proof, appendices, weighted results and examples')
 else:
  passage(p,1,180,'Companion introduction and theorem interfaces only')
  passage(p,307,362,'Companion weighted input contract; not a full algorithm audit')
 for m in re.finditer(r'\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}',t,re.S):
  a=1+t[:m.start()].count('\n');z=1+t[:m.end()].count('\n')
  if 'A-Fully' in r['path'] and a>362:continue
  contracts.append(dict(path=str(p),source_url=r['url'],start_line=a,end_line=z,kind=m[1],text=m[0],sha256=sha(m[0].encode())))
for r in inputs:
 if 'i25-matching-entropy-improvement-resumed.md' in r['path'] or 'i22-combinatorial-discovery.md' in r['path'] or 'i25-rooted-entropy-proof-r2.md' in r['path']:
  passage(r['frozen'],1,100000,'Full report read; R2 is a separate proof-review result, not a novelty premise')
ranges={
'gurvits-pdf':[(110,245)],'cube-ideal-pdf':[(38,83),(348,381),(520,540),(670,698),(830,988)],
'singh-vishnoi-pdf':[(474,633)],'dong-jain-girth-pdf':[(1,215),(325,382),(460,624)],
'dong-jain-permanent-pdf':[(1,130)],'bootstrap-pdf':[(175,315),(520,590)],
'anari-focs-pdf':[(274,306)],'anari-corrected-pdf':[(1,45)],'regular-expanding-pdf':[(1,175)],
'cubic-counts-pdf':[(1,90)],'uncrossing-pdf':[(525,579),(1837,1880)],'tight-cuts-pdf':[(1,220)],
'alternative-entropy-pdf':[(1,145)],'edmonds-pdf':[(1,180)],'brick-original-pdf':[(124,204),(662,780),(825,910)],
'klee-original-pdf':[(17,118)],'cuckler-kahn-published':[(1,145)],'cuckler-dirac-pdf':[(1,98),(164,215)]}
for k,rs in ranges.items():
 for a,z in rs:passage(S/'literature'/f'{k}.txt',a,z,'Read primary statement/proof passage; see report for precise scope and direction')
out('source-contracts.json',contracts);out('read-passages.json',passages)
versions=[]
for p in sorted((S/'literature').glob('*-abs.html')):
 t=p.read_text();start=t.find('Submission history');end=t.find('Full-text links:',start);history=html.unescape(re.sub('<[^>]+>','',t[start:end]));title=re.search(r'<title>(.*?)</title>',t,re.S)
 versions.append(dict(path=str(p),sha256=sha(p.read_bytes()),title=html.unescape(title[1]) if title else None,submission_history=history.strip()))
out('version-history.json',versions)
out('retrieval-assessment.json',dict(accepted_policy='Use successfully parsed primary PDFs with title and version checked; status ok in transport manifests means retrieval only, not scientific acceptance.',excluded=[dict(key='bootstrap',version='1306.1267v3',reason='Guessed version did not exist (404); replaced by verified v1.'),dict(key='anari-entropy',version='1806.05567v3',reason='Wrong identifier; v3 failed and current HTML is unrelated. Replaced by 1807.00929v2 and original FOCS PDF.'),dict(key='cuckler-kahn',version='author-preprint',reason='Citeseer response is HTML rather than PDF. Not read as a paper. Replaced by original Combinatorica 2009 published PDF.')],limitations='Current arXiv pages checked on retrieval date; journal bytes pinned by URL and hash, not a mutable-page priority guarantee. No search establishes exhaustive priority.'))
print(json.dumps(dict(inputs=len(inputs),contracts=len(contracts),passages=len(passages),version_histories=len(versions))))
