import json,sys,hashlib
from pathlib import Path
L=Path(sys.argv[1])
def rec(label):
    out=[]
    for d in sorted(L.glob(f'sources/{label}-*')):
        r=json.loads((d/'receipt.json').read_text()); out.append({'folder':d.name,'url':r['url'],'utc':r['utc'],'status':r.get('status'),'sha256':r['sha256']})
    return out
heads={}
for lab in ['pool-head','omega-head','openai-head']:
    d=sorted(L.glob(f'sources/{lab}-*'))[0]; b=json.loads((d/'body').read_text()); heads[lab]={'sha':b['sha'],'date':b['commit']['committer']['date'],'receipt':d.name}
out={'utc':'2026-11-05','candidate':'350452','heads':heads,
 'comparison_with_root_recorded_heads':{'lean_pool':'unchanged 01db1d7049cf9668bda1e9e106875ee1278b43e6','openai_math':'unchanged 4eaee87548250b2682affda7d05d947c05554bae','omega':'CHANGED: root f1c20718fca66e9ef0a4cb5f4f6a9a55badd1ab5 -> e0da8fcc80226febc4e7ea0836927bc71d158292 (2026-11-05T10:25:44Z); complete D5 (14062 entries), Problems (1758) and Library (2735) subtrees fetched fresh at the new head'},
 'tree_receipts':rec('omega-tree')+rec('omegaD5-tree')+rec('omegaProblems-tree')+rec('omegaLibrary-tree')+rec('pool-tree')+rec('openai-tree')+rec('pool-projects'),
 'path_regex':'irredund|mynhardt|IR_?graph|IRset|Irr(ed)?Graph|1812\\.03382|2104\\.09004|350452|UpperIrr|Roux',
 'path_hits':{'omega':['Library/GraphInvariants/mynhardtroux2021irredundance.md (READ: cites Mynhardt-Roux only for the classical fact that a dominating set is minimal iff irredundant; strata TrapezohedralMinimalDomination; no IR-graph statement)','CommonReservoirGraph.* (false positive: substring reservoIRGraph)'],'lean_pool':[],'openai_math_truncated_tree':[],
   'openai_preprints_cached_listing':'fresh-corpus-r10/sources/registry-preprints.json sha256 6ac178a0ebcece8f2c2c9aa1c22022068110bbdae4bb3d1ffa9f1b693b9e0305 (OpenAI HEAD unchanged): no hits for irredund|mynhardt|IR-graph|1812.03382'},
 'omega_note_receipt':rec('omega-mynhardt'),
 'lean_pool_projects_yml':'404 at the HEAD sha (no projects.yml at root); complete untruncated tree (25038 paths) screened instead',
 'github_repository_search':rec('gh-search'),'github_search_queries':['irredundance graph','irredundance lean','Mynhardt Roux','IR-graph irredundant','upper irredundance'],'github_total_counts':[0,0,0,0,0],
 'limits':'Path/keyword screens only (no proof bodies exist to read for these registries). GitHub code search requires authentication and was not used. ScienceDirect (journal versions DAM 2022 and DM 2022) denied by campaign rule; arXiv versions read instead.'}
(L/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2)); print('ok', {k:v['sha'][:10] for k,v in heads.items()})
