# Verify immutable inputs and actual payload hashes before final handback.
reservation();rs=json.loads((L/'results.json').read_text());assert len(rs)==20 and set(rs)==set(map(str,R['ids']))
m=json.loads((L/'ACTUAL-HASH-MANIFEST.json').read_text());errors=[]
for n,h in m['sha256'].items():
 if H((L/n).read_bytes())!=h:errors.append(n)
assert not errors,errors
checks=[]
for r in json.loads((L/'HTTP-INVENTORY.json').read_text()):
 if 'sha256' not in r:continue
 if 'id' in r:
  p=L/f"source-{r['id']}-bytes.json"
 elif r['receipt'].startswith('http-abs-'):
  p=L/('abs-'+r['receipt'].removeprefix('http-abs-').removesuffix('.json')+'.html')
 else:
  name=re.sub(r'-[0-9]+\.json$','',r['receipt'].removeprefix('http-'));p=L/(name+'-bytes.json')
 if p.suffix=='.html':b=p.read_bytes()
 else:b=base64.b64decode(json.loads(p.read_text())['base64'])
 assert H(b)==r['sha256'],r['receipt'];checks.append({'receipt':r['receipt'],'payload_sha256':H(b),'bytes':len(b)})
raw=json.loads((L/'raw-provenance.json').read_text())
for k,v in raw.items():
 b=(L/f'raw/{k}.jsonl').read_bytes();assert b==base64.b64decode(v['raw_base64_including_newline']);assert json.loads(b)==v['full_parsed_JSON'];assert H(b)==v['raw_sha256'];assert H(json.loads(b)['statement'].encode())==v['statement_UTF8_sha256']
reg=json.loads((L/'registry-heads.json').read_text())
possible={k:[p for p in v.get('paths',[]) if re.search('Prime|Gauss|Matroid|Poset|Wilf|Divis|Partition|Stable|FPT|Goldbach',p,re.I)] for k,v in reg.items() if 'paths' in v}
wj('FINAL-VERIFY.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reservation_sha256':H((L/'reservation.json').read_bytes()),'reservation_unchanged':True,'exact20_keys':True,'all20_original_newline_raw_parsed_statement_hashes':True,'manifest_sha256':H((L/'ACTUAL-HASH-MANIFEST.json').read_bytes()),'covered_actual_file_count':len(m['sha256']),'hash_mismatches':errors,'payload_checks':checks,'directory_only_possible_registry_routes_NOT_read':possible,'scope':'manifest snapshot excludes self and later-created verify script/resource receipts; no self-hash claim','jobs':'all direct child calls completed and reaped; no async jobs remaining','credit':0,'accepted':'52/60 unchanged'})
print('VERIFIED',len(m['sha256']),'manifest hashes;',len(checks),'original HTTP payload hashes; exact20 raw/statement bindings; immutable reservation unchanged.')
print('Directory-name-only possible routes (NOT mathematical body clearance):',json.dumps(possible,ensure_ascii=False)[:4000])
