import pathlib,json,hashlib,datetime
p=pathlib.Path(__file__).parent
http=json.loads((p/'http.json').read_text());checks=json.loads((p/'checks.json').read_text());cov=json.loads((p/'coverage.json').read_text())['coverage']
print('r83 compare file count',cov['r83_compare_files'])
assert cov['r83_compare_files']==122
assert checks['motzkin_root_pass']
assert len(checks['ranks'])==68
assert not (p/'PROOF.md').exists()
for n in ['SUMMARY.md','discovery.md','progress.md','run.sh']:assert (p/n).is_file()
excluded=['provenance.json','finalize.log','finalize-guard.json']
hashes={str(f.relative_to(p)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(p.rglob('*')) if f.is_file() and str(f.relative_to(p)) not in excluded}
r={'lane':'sol-fresh-source-discovery-r87','finalized_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'ZERO_UNRESOLVED','proposed_credit':0,'counts_unchanged':{'additional':8,'total':38},'http_attempts':http,'access_failures':[x for x in http if 'error' in x or x.get('status',200)>=400],'resource_policy':{'address_space_bytes':512*1024*1024,'sampled_process_group_rss_bytes':512*1024*1024,'cpu_seconds':210,'wall_seconds':230,'nominal_sampling_ms':40,'blas_threads':1,'guard_origin':'../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','improvement':'Kill child process group on parent termination/alarm; no cap increase','initial_diagnostic':'Voluntarily stopped after64.23sec, exit143; final reduced n50 passes','caveat':'sampled RSS does not exclude unsampled transients'},'registry_coverage':cov,'source_scope':'Three full primary statements screened; no full ordinary resolution','strongest_objection':'The only complete easy LCM-GCD direction is already public; universal converse has not been proved. No helper or bounded check can count.','falsifier':'An exact nonzero rational null vector of A_n at any n>=6 with binary prefix11 refutes Conjecture5.','hash_policy':'All listed artifacts hashed after their writes completed; provenance excludes itself and finalizer streams because those are still written during finalization. These streams are ephemeral operational logs, not evidence used to establish a result. No recursive/self/stdout hash.','hash_exclusions':excluded,'sha256':hashes,'external_mutations':False,'children':False,'shared_edits':False}
(p/'provenance.json').write_text(json.dumps(r,indent=2)+'\n')
print('Validated ZERO packet,',len(hashes),'final artifact hashes;',len(http),'HTTP attempts;',len(r['access_failures']),'access failures')
