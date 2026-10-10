"""Package actual reading and comparison records; never refresh frozen inputs."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i41_rademacher_fair_start_warming'
C=R/'frontier/sources/i14_spectral_width_novelty_r3/corpus'
assert not (S/'artifact-seal.json').exists()
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_text())
def put(name,x):(S/name).write_text(json.dumps(x,indent=2)+'\n')
selected=read(S/'selected-pinned.json')
Q=next('/'.join(r['path'].split('/')[:2])+'/build/sections/' for r in selected if 'Universality-of-critical-quench' in r['path'])
F=next('/'.join(r['path'].split('/')[:2])+'/build/sections/' for r in selected if 'Functional-universality-of-critical-SK' in r['path'])
M=next('/'.join(r['path'].split('/')[:2])+'/build/sections/' for r in selected if 'Critical-mixing-in-the-Sherrington' in r['path'])
log=[]
def passage(p,ranges,note):
 b=p.read_bytes();ls=b.splitlines(keepends=True)
 rr=[]
 for a,z in ranges:
  z=min(z,len(ls));assert a<=z
  rr.append({'first':a,'last':z,'sha256':sha(b''.join(ls[a-1:z]))})
 log.append({'path':str(p.relative_to(R)),'sha256':sha(b),'ranges':rr,'read_scope':note})
for name,z in [('01-introduction.tex',155),('02-background.tex',219),('04-warming.tex',1623),('05-gaussian-limits.tex',1011),('07-history-cutoffs.tex',671),('08-clock-scores.tex',779),('09-replacement.tex',934)]:
 passage(C/(Q+name),[(1,z)],'Read actual statement and proof operations in this I41 turn; adjoining tool ranges consolidated. Entire file except introduction read through line 155.')
for name,spans in [('02-edge-law.tex',[(154,310)]),('03-observations.tex',[(140,275)]),('05-gradient.tex',[(1,627)]),('06-microscopic.tex',[(790,1070)])]:
 passage(C/(F+name),spans,'Actual conditioned law, replica/static transfer, closed form, recovery/positivity/divergence/relaxed-energy proof passages.')
for name,spans in [('introduction.tex',[(1,140)]),('cap-entropy.tex',[(1,160),(300,345),(654,700),(851,880)])]:
 passage(C/(M+name),spans,'Clock and exponent contracts; actual capacity minimum-observation threshold, product entropy, final LSI proof. Not a whole-paper read.')
for name,spans in [('pei-v1.pdf.txt',[(1,530)]),('asl-v1.pdf.txt',[(115,210),(2230,2370),(2916,3070)]),('diffusions-v2.pdf.txt',[(145,270),(1018,1090)]),('chatterjee-v3.pdf.txt',[(35,130),(227,300)]),('duhuang-v2.pdf.txt',[(55,145),(181,270),(517,560)])]:
 passage(S/'literature'/name,spans,'Actual current primary PDF text read; ranges refer to retained pdftotext bytes, not PDF page numbers.')
for name,z in [('AGENTS.md',11),('sources/upstream.json',6),('frontier/iterations/i39-quantum-spectral-discovery.md',276),('frontier/iterations/i40-critical-sk-waiting-relaxation.md',247)]:
 passage(S/'frozen'/name,[(1,z)],'Frozen original read in full; author bytes preserved.')
put('read-passages.json',log)
indexed={r['path']:r for r in selected}
contracts=[]
for row in read(R/'frontier/sources/i40_critical_sk_waiting_relaxation/contracts.json'):
 if row['source_path'] in indexed and any(x['path'].endswith('/'+row['source_path']) and any(y['first']<=row['label_line']<=y['last'] for y in x['ranges']) for x in log):
  row=dict(row);row['i41_role']='Independently reread; premises are accepted at the fixed pin. See I41 report for audit/extension scope.';contracts.append(row)
for name,labels in [('07-history-cutoffs.tex',['hist:static-support','hist:kernel-recursion','hist:tested-law','hist:bridge-definition']),('08-clock-scores.tex',['score:action-bounds','score:block-masses','score:raw-projection','prop:clock-scores','score:node-action-scale'])]:
 path=Q+name;m=indexed[path];lines=(C/path).read_bytes().splitlines(keepends=True)
 for label in labels:
  line=next(i for i,l in enumerate(lines,1) if ('\\label{'+label+'}').encode() in l);a=max(1,line-2);z=min(len(lines),line+35);b=b''.join(lines[a-1:z])
  contracts.append({'source_path':path,'raw_url':m['url'],'git_blob':m['git_blob'],'file_sha256':m['sha256'],'label':label,'label_line':line,'excerpt_first':a,'excerpt_last':z,'excerpt_sha256':sha(b),'excerpt':b.decode(),'contract_and_use':'Actual laminar-history, tested-law, conditional-copy and score operations. Printed source query class is one stationary leg/two quench legs. I41 explicitly checks the extension to three stationary legs; no arbitrary history theorem is assumed.'})
put('contracts.json',contracts)
# Correct a duplicated search row introduced by listing I40 both generally and explicitly.
# This changes no frozen bytes or input baseline, and the complete inventory stays the same.
project=read(S/'project-search.json');hits=[]
for path in project['files']:
 found=[{'line':i,'text':v} for i,v in enumerate((S/'frozen'/path).read_text().splitlines(),1) if re.search(project['pattern'],v,re.I)]
 if found:hits.append({'path':path,'matches':found})
project['matches']=hits;put('project-search.json',project)
put('queries.json',{'searches':[{'response':'web01.json','search_query':[{'q':'"Sherrington-Kirkpatrick" "critical" "quench" universality'},{'q':'"Sherrington-Kirkpatrick" dynamics warm start second moment density critical mixing'}]},{'response':'web02.json','search_query':[{'q':'"critical" "Sherrington-Kirkpatrick" "fair" dynamics density'},{'q':'"Sherrington-Kirkpatrick" "warm start" entropy universality'},{'q':'"multitime" "universality" spin dynamics'}]}],'scope':'Early current web searches retained. Primary identities and exact HTTP requests are in literature/*.response.json. Search hits are leads, not mathematical premises.'})
put('literature/retrieval-assessment.json',{'status':'All 17 fresh primary HTTP responses returned 200; seven pinned raw files and five current-version pages plus five versioned PDFs. No HTTP retrieval failures in I41.','identity_checks':'Titles and actual paper text inspected; Chatterjee is math/0508519v3. Prior wrong-identifier history remains frozen in I40 and is not used.','limitations':'Bounded primary search, not exhaustive priority certification. All current version records are as of retained retrieval timestamps.'})
print(json.dumps({'read_records':len(log),'contract_records':len(contracts),'project_hit_documents':len(hits)}))
