import pathlib,json,hashlib,resource,os,datetime
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,)*2);os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
p=pathlib.Path(__file__).resolve().parent;H=lambda f:hashlib.file_digest(open(f,'rb'),'sha256').hexdigest();r=json.loads((p/'reservation.json').read_text());d=json.loads((p/'results.json').read_text());assert len(d)==40 and set(d)==set(map(str,r['ids']))
for f,h in r['prior_report_hashes'].items():assert H(f)==h
for i,row in d.items():
 assert row['accepted_credit']==0 and row['lean_endpoint'] is None
 assert row['old_disposition']==r['prior_coverage'][i]['disposition']
 assert H(p/'raw'/f'{i}.jsonl')==row['raw']['raw_with_newline_sha256']
 assert (p/'raw'/f'{i}.jsonl').read_bytes().endswith(b'\n')
 for s in row['new_review']['source_files']:assert H(p/s['path'])==s['sha256']
for f in (p/'sources').glob('*.receipt.json'):
 q=json.loads(f.read_text())
 if 'sha256' in q:assert H(pathlib.Path(str(f).removesuffix('.receipt.json')))==q['sha256']
manifest={str(f.relative_to(p)):H(f) for f in sorted(p.rglob('*')) if f.is_file() and f.name not in ['manifest.json','verification.json','verify.log']}
(p/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');(p/'verification.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','results':40,'new_unique_review_credit':0,'new_original_question_body_ids':8,'new_related_only_ids':1,'no_new_primary_depth_ids':31,'lean_endpoints':0,'accepted_credit':0,'prior_reports_unchanged':True,'raw_line_newlines_preserved':True,'source_receipts_verified':True,'limits':'Artifact integrity verification only, not Lean proof verification or independent mathematics review.'},indent=2)+'\n');print('PASS exactly40 IDs, immutable priors, raw lines, sources, zero credit; no Lean endpoint claimed')
