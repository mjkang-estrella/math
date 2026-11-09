import json,hashlib,glob,os
lane='/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/flat-balance-independent-audit-pi-r6'
def sha(p): return hashlib.sha256(open(p,'rb').read()).hexdigest()
envaudit=json.load(open(lane+'/results/352972-env-audit.json'))
srcx=json.load(open(lane+'/results/source-crosscheck.json'))
rec={
 'mathdb_id':352972,
 'audit_lane':lane,
 'auditor':'independent pi audit r6 (this lane; no children)',
 'pins':{
  'lean':'4.34.1','lean_commit':'5045d0056413266e57c625dcd7c365b10e377c52',
  'lean_binary_sha256':sha('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean'),
  'checker_binary_sha256':sha('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker'),
  'mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612'},
 'production_sources':{
  'FlatBalance.lean':sha(lane+'/src/FlatBalance.lean'),
  'FlatBalanceBridges.lean':sha(lane+'/src/FlatBalanceBridges.lean')},
 'replay':{
  'primary_build_oleans':{os.path.basename(p):sha(p) for p in sorted(glob.glob(lane+'/build/*.olean'))},
  'cleanroom_build_oleans':{os.path.basename(p):sha(p) for p in sorted(glob.glob(lane+'/cleanroom/build/*.olean'))},
  'byte_identical_replay':True,
  'strict_flags':'-j1 -M3500 -DwarningAsError=true, module-name kernel recheck via leanchecker, all under provided runner'},
 'environment_audit':{
  'declCount':envaudit['summary']['declCount'],
  'kindCounts':envaudit['summary']['kindCounts'],
  'unsafe':envaudit['summary']['unsafe'],'partial':envaudit['summary']['partial'],'opaque':envaudit['summary']['opaque'],
  'axiomUnion':envaudit['summary']['axiomUnion'],
  'endpointClosures':[{'endpoint':c['endpoint'],'closureSize':c['closureSize'],
                       'localClosureSize':c['localClosureSize'],
                       'axioms':c['axiomClosureCollectAxioms'],
                       'independentBFSAgrees':True} for c in envaudit['endpointClosures']],
  'inventory':'results/352972-env-audit.json'},
 'source_crosscheck':'results/source-crosscheck.json',
 'controls':{
  'author_positive_file':'audit/CtrlAuthorPos.lean (copy of input/author-Controls352972Bridges.lean)','author_positive_exit':0,
  'author_negative_shape_file':'audit/CtrlAuthorNeg.lean (copy of input/author-Controls352972.lean)','author_negative_shape_exit':0,
  'independent_positive':'audit/ControlsIndPos.lean (P1-P11 incl EMPTY graph, second cutoff, convention values)','independent_positive_exit':0,
  'independent_expected_failures':'audit/ControlsIndNeg.lean (N1-N6)','independent_neg_exit':1,
  'independent_neg_residuals':['9 = 8','10 = 9','4 <= 1','6 = 7','4 = 3','0 = 9'],
  'C9_uses_no_Flat':True},
 'manuscript_qa':'receipt/pdf-qa.json',
 'flags_for_root':[
  'author manuscript R2: "14 local constants" per endpoint contradicted by full closure 75/77 (author value? without allowOpaque stops at theorems)',
  'author manuscript R2: endpoint axiom split claim wrong; both endpoints carry {propext, Classical.choice, Quot.sound}',
  'author results manifest entry stale (root already recorded actual binding); preserved untouched',
  'author "TEN positive proofs" = 11 example blocks under C3a/C3b single-control labeling'],
 'credit':0,'accepted':52,'self_acceptance_claimed':False
}
open(lane+'/results/352972.json','w').write(json.dumps(rec,indent=2)+'\n')
print('wrote results/352972.json',sha(lane+'/results/352972.json'))
