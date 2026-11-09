import pathlib,json,re,subprocess,hashlib,resource
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
o=pathlib.Path(__file__).resolve().parent;c=o.parent;b=c.parent;x=json.loads((o/'intake.json').read_text());h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ctx={}
for p in [b/'ledger.json',b/'prior-campaign-context.json',c/'ledger.json']:
 j=json.loads(p.read_text());ctx[str(p)]={'sha256':h(p),'administrative_context_mutable':True,'accepted_count':j.get('accepted_count'),'accepted':j.get('accepted'),'rejected':j.get('rejected'),'excluded':j.get('excluded'),'held':j.get('held')}
(o/'ledger-context.json').write_text(json.dumps(ctx,indent=2)+'\n')
pat=r'\b(?:'+'|'.join(x)+r')\b';q=subprocess.run(['rg','-n','--max-columns','900','-e',pat,str(b),'--glob','*.md','--glob','*results.json','--glob','*review.json','--glob','!expanded-corpus-r53/**'],capture_output=True,text=True,timeout=45)
lines=[z for z in q.stdout.splitlines() if '/expanded-corpus-r53/' not in z]; (o/'history-id-matches.txt').write_text('\n'.join(lines)+'\n')
titles=[]
for i,v in x.items():
 q=subprocess.run(['rg','-n','-F','--max-count','3','--max-columns','700',v['record']['title'],str(b),'--glob','*.md','--glob','*results.json','--glob','*review.json'],capture_output=True,text=True,timeout=30)
 titles.extend(z for z in q.stdout.splitlines() if '/expanded-corpus-r53/' not in z)
(o/'history-title-matches.txt').write_text('\n'.join(titles)+'\n')
print('id hits',len(lines),'title hits',len(titles)); print('\n'.join(lines)[:10000]);print('\n'.join(titles)[:10000])
reg={}
paths=[c/'fresh-corpus-r10/sources/registry-preprints.json',c/'staller-parent-final-r1/omega-D5-correct.json',c/'staller-parent-final-r1/omega-Problems-correct.json']
for p in paths:
 j=json.loads(p.read_text());terms=['algebraic','segmentation','trapezoid','supernorm','triangle','girth']+list(x); hits=[a['path'] for a in j['tree'] if any(t.lower() in a['path'].lower() for t in terms)]
 reg[str(p)]={'sha256':h(p),'tree_sha':j.get('sha'),'truncated':j.get('truncated'),'hits':hits,'scope':'path names only; no all-body/history clearance'}
(o/'registry-screen.json').write_text(json.dumps(reg,indent=2)+'\n');print('registry hits',json.dumps(reg)[:7000])
