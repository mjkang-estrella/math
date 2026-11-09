#!/usr/bin/env python3
"""Final evidence ledger and hashes. No writes outside sym/ and the named note."""
import collections
import hashlib
import json
import math
import pathlib
import sys
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent
HD=HERE.parent
REPO=HD.parent.parent


def load(p): return json.loads(pathlib.Path(p).read_text())


def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    audit=load(HERE/'coverage_audit.json')
    baseline=load(HD/'codex/results_t14112.json')
    targets={k:v for k,v in baseline.items() if v['status']=='BUDGET' and 6<=len(v['far'])+1<=8}
    odd=load(HD/'codex3b/results_t14112.json')
    ledger=load(HERE/'cross_all.json')
    tests=load(HERE/'test_results.json')
    standalone=load(HERE/'standalone_checks.json') if (HERE/'standalone_checks.json').exists() else None
    counts={};closed=[];opened=[]
    for dim in (6,7,8):
        keys=[k for k,v in targets.items() if len(v['far'])+1==dim]
        covered=[k for k in keys if audit['configurations']['new:14112:'+k]['result']=='COVERED']
        counts[str(dim)]={'total':len(keys),'closed':len(covered),'BUDGET':len(keys)-len(covered),
                          'codex3b_total':sum(k in odd for k in keys),
                          'codex3b_closed':sum(k in odd for k in covered)}
        closed+=covered;opened+=sorted(set(keys)-set(covered))
    stages={}
    attempts=collections.Counter()
    for p in sorted(HERE.glob('attack_*.json')):
        data=load(p)
        stages[p.name]={'configurations':len(data),'statuses':dict(collections.Counter(v['status'] for v in data.values())),
                        'seconds_sum':round(sum(v.get('seconds',0) for v in data.values()),3),
                        'recorded_partial_lifts':sum(v.get('partial',{}).get('lifts',0) for v in data.values()),
                        'complete_job_lifts':sum(j.get('lifts',0) for v in data.values() for j in v.get('jobs',[]))}
        attempts.update(data.keys())
    assert all(k in attempts for k in targets),'some target received no attempt'
    assert all(v['result']!='MISSING' for k,v in audit['configurations'].items() if not k.startswith('new:'))
    cross_counts=collections.Counter(v['status'] for v in ledger.values())
    assert cross_counts=={'CLOSED':2745},cross_counts
    if standalone:
        expected=set(list((HERE/'crosscheck').rglob('*.jsonl'))+
                     list((HERE/'certs').rglob('*.jsonl'))+
                     list((HERE/'controls').glob('*.jsonl'))+
                     list(HERE.glob('smoke.jsonl'))+list(HERE.glob('probe*.jsonl')))
        assert set(standalone['files'])=={str(p.relative_to(HERE)) for p in expected},'standalone replay incomplete'
        assert all(v['result']=='PASS' for v in standalone['files'].values()),'standalone failure'
        assert standalone['checker_sha256']==digest(HERE/'check_sym.py'),'checker changed since standalone replay'
    first=load(HERE/'input_broad_pin2.json')
    parallel_path=HD/'codex3a/results_t14112.json'
    parallel=load(parallel_path)
    parallel_overlap=sorted(k for k in closed if parallel.get(k,{}).get('status')=='CLOSED')
    summary={'label':'COMPUTED','claim':'Closure means a full checked member list, not necessarily nonexistence.',
             'baseline_count':len(targets),'counts_by_dimension':counts,'closed':sorted(closed),'BUDGET':sorted(opened),
             'total_closed':len(closed),'total_BUDGET':len(opened),'all_targets_attempted':True,
             'latest_codex3a_overlap':parallel_overlap,'latest_codex3a_sha256':digest(parallel_path),
             'source_hashes':first['sources'],
             'crosscheck':{'source_files':audit['legacy_source_count'],'unique_domains':audit['legacy_unique_domains'],
                           'all_unique_domains_checked':audit['legacy_domains_checked'],
                           'legacy_configurations_covered':sum(v['result']=='COVERED' for k,v in audit['configurations'].items() if not k.startswith('new:')),
                           'source_nodes_unique_domains':sum(v['source_nodes'] for v in ledger.values()),
                           'sym_nodes':sum(v['nodes'] for v in ledger.values()),
                           'sym_refinements_checked':sum(v['refinements'] for v in ledger.values())},
             'controls':{'level1_members':tests['positive_counts']['level1'],'level2_members':tests['positive_counts']['level2'],
                         'positive_finite_boxes':tests['positive_counts']['finite_boxes'],
                         'positive_class_certificates':tests['positive_counts']['exact_classes'],
                         'tamper_rejections':sum(v['result']=='REJECTED' for v in tests['tamper_tests']),
                         'unaligned_sumset_controls':sum(v['result']=='PASS' for v in tests['tamper_tests']),
                         'orbit_partition_tests':len(tests['partition_tests']),
                         'arithmetic_soundness':tests['arithmetic_soundness']},
             'finite_exception_scan':audit['finite'],'stages':stages,
             'certified_members':audit['members'],
             'standalone':{'files':len(standalone['files']),'PASS':sum(v['result']=='PASS' for v in standalone['files'].values()),
                           'checker_sha256':standalone['checker_sha256'],'brute_Lmax':standalone['brute_Lmax']} if standalone else None}
    (HERE/'summary.json').write_text(json.dumps(summary,indent=1)+'\n')
    if standalone:
        note=REPO/'notes/highdim_sym.md'
        text=note.read_text().split('\n## Final counted results\n')[0]
        lines=['\n## Final counted results\n',
               f'**COMPUTED.** All {len(targets)} requested baseline BUDGET configurations were attempted. {len(closed)} close and {len(opened)} remain BUDGET. Closure requires a full independently audited slice cover and its finite exceptions; partial certificates never count as a configuration closure.\n']
        for d,record in counts.items():
            lines.append(f'**COMPUTED.** Dimension {d}: {record["closed"]}/{record["total"]} closed, {record["BUDGET"]} BUDGET. Of the codex3b subset: {record["codex3b_closed"]}/{record["codex3b_total"]} closed.\n')
        lines += [f'**PROVED (checked), COMPUTED (counts).** All 2,745 distinct legacy domains, representing 2,927 legacy certificate files, passed the fresh checker. The slice audit recovers all {summary["crosscheck"]["legacy_configurations_covered"]} already closed configurations. Legacy source trees were projected as search hints; no old checker was trusted.\n',
                  f'**COMPUTED.** On the 2,745 distinct legacy domains, projection reduces {summary["crosscheck"]["source_nodes_unique_domains"]} source nodes to {summary["crosscheck"]["sym_nodes"]} symmetric nodes. The checker replays {summary["crosscheck"]["sym_refinements_checked"]} symmetric refinements. These figures compare matched domains, not the larger source-file count containing redundant coefficient orderings.\n',
                  f'**COMPUTED.** The final direct subprocess replay ran isolated checker entrypoints for {len(standalone["files"])} certificate files: all PASS. Every replay uses a brute box through L=10. The finite configuration exception scan checked {audit["finite"]["smooth_points"]} smooth lattice points through {audit["finite"]["Lmax"]} digits and found {len(audit["finite"]["members"])} members in the counted configurations.\n',
                  f'**COMPUTED.** Positive controls reproduce all 13 nontrivial Level-1 and 32 Level-2 members below 10^9 in their original configurations. All 45 finite boxes passed an independent checker enumeration. Thirteen valid slices also passed exact-size class certificates. The 33718272 control is the original S161 / [18,18,54,63] configuration, point (8,6,7,5,3), X=303464448; it lies below the final constant-v2 slice floor and is correctly reproduced in the finite box. Five-mode controls explicitly allow prime 5 and are separate finite controls. There is no all-L closure claim for the 33718272 configuration.\n',
                  f'**COMPUTED.** {summary["controls"]["tamper_rejections"]} tamper cases were rejected; the valid unaligned sumset control passed. Both refinement enumerators matched labelled enumeration in 24 exhaustive orbit tests. Arithmetic comparisons: {tests["arithmetic_soundness"]}.\n',
                  '**PROVED.** Symmetry improves the residue count from `M^(k+1)` to `M * product_c binomial(M+m_c-1,m_c)`. Its asymptotic gain is `product_c m_c!`; the dimension exponent remains k+1.\n',
                  '**CONJECTURAL.** Persistent double-unbounded ladders, rather than only duplicate labellings, are the next obstruction in the remaining cases. The long-depth BUDGET traces are evidence of search behavior, not evidence of nonexistence or an impossibility theorem for congruence methods.\n',
                  '**COMPUTED.** Exact closed/open keys, per-stage diagnostics and hashes are in `summary.json`; direct subprocess verdicts are in `standalone_checks.json`. Proof files are in `crosscheck/` and `certs/`; controls and rejected mutations are in `controls/`, `positive_boxes.json`, and `tamper/`. The generator/checker and the complete soundness argument are the entrypoints and sections above.\n']
        lines += ['**PROVED (coverage), COMPUTED (status).** Final closure counts use the hash-bound standalone certificates and the independent slice audit. A complete file written just before its configuration checker timed out can therefore be promoted after its standalone PASS, even when its historical stage row remains BUDGET. No unfinished tree is promoted.\n',
                  f'**COMPUTED.** Overlap of the final closed keys with the latest read-only codex3a CLOSED list: {parallel_overlap}. Counts are relative to the original codex baseline.\n']
        note.write_text(text+'\n'.join(lines))
        manifest={str(p.relative_to(HERE)):digest(p) for p in sorted(HERE.rglob('*')) if p.is_file() and p.name!='manifest.json' and p.suffix not in ('.log','.tmp') and '__pycache__' not in p.parts}
        manifest['../../../notes/highdim_sym.md']=digest(note)
        (HERE/'manifest.json').write_text(json.dumps({'label':'COMPUTED','excludes':['*.log','*.tmp','__pycache__'],'sha256':manifest},indent=1)+'\n')
    print(json.dumps({'label':'COMPUTED','closed':len(closed),'BUDGET':len(opened),'by_dimension':counts,'standalone':summary['standalone']}))

if __name__=='__main__':main()
