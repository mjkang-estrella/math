"""Preparation only: never called by the read-only verifier; no corpus traversal."""
from pathlib import Path
import json,hashlib,re
R=Path(__file__).resolve().parents[3];S='frontier/sources/i137_crystalline_coherence';OLD='frontier/sources/i134_discrete_geometric_optimization'
def obj(p):return json.loads((R/p).read_text())
def put(n,d):(R/S/n).write_text(json.dumps(d,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
def rec(p):
 b=(R/p).read_bytes();return {'path':p,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
rs=[json.loads(x) for x in (R/S/'reads.jsonl').read_text().splitlines()]
# Broad geometry display 1-718 was truncated; its completed replacements cover all lines.
reads=[d for i,d in enumerate(rs) if i!=7]
put('read-manifest.json',{'passages':reads,'convention':'UTF-8 splitlines incl formfeeds; join LF without appended LF; actual completed displays only'})
ctx=obj(S+'/context-manifest.json')
put('context-reading.json',{'gate':'completed before mathematical audit','all_decoded_fields':True,'records':[{'decoded':d['decoded'],'start':1,'end':d['lines'],'sha256':rec(d['decoded'])['sha256']} for d in ctx],'recursive_content':'I134/I131/I128/I125/I122/I119 briefs, full reports, finalized receipts and objections; embedded I116/I113 originals; duplicate prefixes retained','method':'full decoded-field displays in bounded chunks; targeted rereads after truncated broad displays; no summary substituted'})
put('read-history.json',{'completed_manifest':'read-manifest.json','truncated_attempts':['Initial combined live-ledger and recursively decoded context displays exceeded output limits; all required decoded fields completed by subsequent bounded rereads before audit.','Initial combined C03 1-718 / C02 1-423 display truncated C03 middle; C03 reread as 1-289,290-550,551-718. C02 full text was visible.'], 'failed_requests':['C04 requested 197-439; 413 lines only, assertion failed before recording; completed 197-413.','U08 arithmetic requested 1240-1400;1399 lines only; completed1240-1399.','Discovery rg regexes containing unescaped TeX braces failed; corrected fixed-string scans.'], 'discovery_not_proof':['Search engine snippets and unused arXiv/publisher leads','rg results use LF line numbers; completed passages use Python splitlines, including PDF form feeds','File listing exposed active I135/I136 filenames only; no reads or dependencies'], 'rendered_and_seen':[{'pdf':S+'/external/fjm-2002.pdf','page_one_based':8,'image':S+'/external/fjm-theorem-page.png','command':'pdftoppm -f 8 -l 8 -scale-to 1600 -png -singlefile'},{'pdf':S+'/external/fkz-v5.pdf','page_one_based':7,'image':S+'/external/fkz-theorem-page.png','command':'pdftoppm -f 7 -l 7 -scale-to 1600 -png -singlefile'}], 'external_retrievals':'All six new recorded downloads succeeded; extraction commands and code in external-manifest.json. No unrecorded failed retrieval counted as proof.'})
put('original-audit-verdicts.json',{'original_I134':{k:'PASS without repairs at original scope and constants' for k in ['G134','P134 residual/deletion','P134 saturation/Euler/neighbors','P134 affine polygon deficit','P134 hexagon/cap/constants','P134 original-cell transfer/optimization','P134/B134 common displayed constant','W134 signed-measure square','B134 boundary/density/full-cell equality','B134 square subsequence','slow wave labelled scope','two grains Gaussian ordered energy']},'I131_I128':'scoped PASS retained; S128 unproved/unrefuted PARK','I125_literal_verifier':'FAIL: ValueError: canonical inventory; unchanged original seal','I125_ordering_adapter':'distinct ordering-only PASS; unchanged; not rerun','I122_original_general_Lambda_equality':'FAIL retained','new_results':'author-level technical A137/R1-R7; no nomination; no infinite-volume or interface theorem'})
flat={d['path']:d for d in obj(OLD+'/immutable-flat.json')['files']}
for d in obj(OLD+'/seal.json')['files']:flat[d['path']]=d
for p in [OLD+'/seal.json','frontier/iterations/iteration134-discrete-geometric-optimization-task.json','frontier/experiments/i134-parent-verification.json','frontier/experiments/i116-parent-verification.json']:
 flat[p]=rec(p)
for d in ctx:flat[d['path']]={k:d[k] for k in ('path','bytes','sha256')}
for d in reads:
 if not d['path'].startswith(S+'/'):flat[d['path']]={k:d[k] for k in ('path','bytes','sha256')}
for d in obj(S+'/snapshots.json'):
 if not d['drift']:flat[d['live']]=rec(d['live'])
for p in ['sources/preprints-tree.json','sources/CONTENTS.md']:flat[p]=rec(p)
for p in ['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']:flat.pop(p,None)
assert not any('/i135' in p or '/i136' in p or '/iteration135' in p or '/iteration136' in p for p in flat)
put('immutable-flat.json',{'corpus_map':'frontier/sources/i113_online_optimization_discovery/search-domain.json','files':[flat[p] for p in sorted(flat)],'note':'One flat traversal; immutable inherited receipts and diagnostics not executed; no corpus copy'})
put('inherited-references.json',[flat[p] for p in sorted(flat) if '/experiments/' in p and ('parent-' in p or p.endswith('/diagnostics.json'))])
put('original-bindings.json',[{'original':p,'snapshot':S+'/context/'+Path(p).name,**{k:v for k,v in rec(p).items() if k!='path'}} for p in ['frontier/iterations/i134-discrete-geometric-optimization.md','frontier/experiments/i134-parent-verification.json']])
domain=obj('frontier/sources/i113_online_optimization_discovery/search-domain.json');wanted={d['path'] for d in reads}
put('selected-inventory.json',[d for d in domain if d['local'] in wanted or d['original_local'] in wanted])
expr={'gap_and_contacts':r'deleted|0\.032|\.032|Q_1|Q1|duality','periodic_heat':r'heat|self|background|kappa|q_s','geometry_and_rigidity':r'Voronoi|Lipschitz|holonomy|rigidity|separation|six','screening_limits':r'screen|stationary|intensity|ergodic|cutoff|reflection'}
found={k:[] for k in expr};scope={}
for d in reads:scope.setdefault(d['path'],set()).update(range(d['start'],d['end']+1))
for p,ns in sorted(scope.items()):
 ls=(R/p).read_text().splitlines()
 for n in sorted(ns):
  for k,x in expr.items():
   for m in re.finditer(x,ls[n-1],re.I):found[k].append({'path':p,'line':n,'start':m.start(),'end':m.end(),'match':m.group(),'text':ls[n-1]})
put('focused-lexical.json',{'scope':'union of completed reading ranges, all path types; zero-based character offsets, Python re.I, all nonoverlapping occurrences per expression','expressions':expr,'occurrences':found,'counts':{k:len(v) for k,v in found.items()}})
print(json.dumps({'flat_references':len(flat),'completed_passages':len(reads),'lexical_occurrences':sum(map(len,found.values()))}))
