"""Development-only writer. NOT the final read-only verifier; refuses a sealed bundle."""
from pathlib import Path
import json, hashlib, re
S=Path('frontier/sources/i103_algebraic_complexity_discovery')
X=Path('frontier/experiments/i103_algebraic_complexity_discovery')
assert not (S/'seal.json').exists()
PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(name,x): (S/name).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
reads=[json.loads(s) for s in (S/'read-manifest.jsonl').read_text().splitlines()]
selected=json.loads((S/'selected-inventory.json').read_text())
contracts=[]
for d in selected:
    if not d['path'].endswith('.tex'):continue
    lines=Path(d['local']).read_text().splitlines()
    contracts.append({**d,'pinned_url':'https://raw.githubusercontent.com/openai/math/'+PIN+'/'+d['path'],
        'labels':[{'label':m.group(1),'line_splitlines':i} for i,l in enumerate(lines,1) for m in re.finditer(r'\\label\{([^}]+)\}',l)],
        'recorded_reads':[{'first':r['first'],'last':r['last']} for r in reads if r['source']==d['path']],
        'line_convention':'UTF-8 str.splitlines(), 1-based inclusive; label inventory is NOT a claim to have read every labelled proof'})
save('source-contracts.json',{'pin':PIN,'scope':'Exact labelled source locations and actual recorded reads; mathematical contracts are in report section 1.','sources':contracts})
ext=[]
for key,ranges in {'gk':[(370,424),(424,493),(490,560),(945,1016)],'hw':[(195,285)],'acm':[(160,208),(2335,2398)]}.items():
    p=S/'external'/f'{key}.txt'; b=p.read_bytes(); ls=b.decode().split('\n')
    for a,z in ranges:
        ext.append({'source':str(p),'sha256':sha(p),'first':a,'last':z,'convention':'UTF-8 split on literal LF, 1-based inclusive; form feed retained inside a line','passage_sha256':hashlib.sha256(('\n'.join(ls[a-1:z])+'\n').encode()).hexdigest()})
save('external-read-manifest.json',ext)
drift=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']
refs=[]
for p in ['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json',
          'frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json',
          'frontier/sources/i79_logarithmic_girth_spectra_novelty_r3/search-domain.json',
          'frontier/sources/i88_nonlinear_banach_discovery/search-domain.json']:
    refs.append({'path':p,'sha256':sha(p),'drift_allowed':False})
for p in drift:
    refs.append({'path':p,'sha256':sha(S/'snapshots'/p),'drift_allowed':True,'snapshot':str(S/'snapshots'/p)})
save('immutable-references.json',{'references':refs,'only_live_drift_allowlist':drift,'corpus_references':'Every local and original_local entry in sealed search-domain.json; all immutable. No I101/I102 working output bound.'})
save('preseal-events.json',{'preparation_events':[
 {'status':'failed_then_resolved','event':'E introduction initially requested with nonexistent 01-introduction.tex; exact introduction.tex subsequently read; no failed passage record.'},
 {'status':'failed_then_resolved','event':'Short An-explicit family selector matched five introductions; Complex-Matrix 01-introduction.tex matched none; exact family and filename reads succeeded.'},
 {'status':'failed_no_mutation','event':'Post-compaction initial pwd/wc/ls command ran from workspace parent, wc failed to locate report; rerun in repository root.'},
 {'status':'retained_limitation','event':'Initial combined console reads sometimes truncated. Complete-proof claims rely on later explicit complete passage ranges, not the missing console text.'},
 {'status':'failed_not_dependency','event':'Derksen-Makam PDF URL returned HTTP 403; exact request retained in external-requests.json, metadata only consulted.'},
 {'status':'passed_before_seal','event':'Exact finite diagnostics passed before writing provenance; no failed mathematical test to suppress.'},
 {'status':'corrected_before_seal','event':'Self-check corrected screen C layer notation from six symbols to the source five-layer Sigma-Pi-Sigma-Pi-Sigma model; corrected verification wording from both to one exact lexical multiset.'}
 ],'preseal_validation_failures':[],'seal_policy':'Validate first, create seal once, then run offline read-only verifier. No postseal repair or reseal.'})
print(json.dumps({'contracts':len(contracts),'read_records':len(reads),'external_passages':len(ext),'immutable_reference_entries':len(refs)}))
