import pathlib,hashlib,json,datetime,subprocess
R=pathlib.Path(__file__).resolve().parent
B=R.parent.parent
def digest(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
ex=[]
for name in ('kazemi','prisms'):
 dest=R/(name+'-independently-extracted.txt')
 p=subprocess.run(['pdftotext','-layout',str(R/'frozen/sources'/ (name+'.pdf')),str(dest)],capture_output=True,text=True)
 ex.append({'source':name,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
 assert p.returncode==0
 assert dest.read_bytes()==(R/'frozen/sources'/(name+'.txt')).read_bytes()
 ex[-1]['identical_to_frozen_text']=True
(R/'pdf-extraction.json').write_text(json.dumps(ex,indent=2)+'\n')
p=subprocess.run(['python',str(R/'prepare.py'),'after'],capture_output=True,text=True)
assert p.returncode==0,p.stderr
print(p.stdout,end='')
guard=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert digest(guard)['sha256']=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
ctx=[B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[3]/'AGENTS.md']
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'Independent solo preliminary review; root adjudicates','recommendation':'EXCLUDE routine source bridge; ordinary proof survives; no formal PASS','original_frozen_root':str(R.parent/'sol-fresh-source-discovery-r152'),'freeze_paths_verified_before_and_after':34,'private_copy_byte_identical':True,'verification_receipts':['freeze-before.json','freeze-after.json'],'source_extraction':'Both actual frozen PDFs re-extracted using pdftotext -layout; byte-identical to frozen text','new_retrievals':[],'public_actions':False,'git_actions':False,'children':False,'Lean_run':False,'paper_created':False,'count_changes':False,'guard':digest(guard),'limits':{'AS_bytes':536870912,'group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'nominal_sampling_ms':40,'raised':False,'RSS_caveat':'Sampling can miss transients and actual scheduling intervals were not instrumented'},'execution_environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'failures':[],'context_hashes':[digest(p) for p in ctx if p.exists()],'registry':{'Omega':'490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c','OpenAI':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','inherited_capped_intervals':['aa026->a19a (300 paths)','a19a->490f (300 paths)'],'fresh_registry_audit':False,'worldwide_novelty_clearance':False},'read_scope_and_limits':'Actual primary extracted bodies, candidate proof/discovery/provenance/checks and logs, bounded history/registry receipts. No re-audit of all original history bodies. Closest unread source bodies explicitly listed in review.md. No 403/429 retries.','evidence_files':[digest(p) for p in sorted(R.rglob('*')) if p.is_file() and p.name not in ('provenance.json','finish-run.log')]}
(R/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
print('PDF extraction, after verification, provenance complete')
