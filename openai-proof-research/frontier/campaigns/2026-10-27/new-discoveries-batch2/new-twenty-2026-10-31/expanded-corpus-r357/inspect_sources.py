exec(compile(open('investigate.py').read().split("mode=sys.argv[1]")[0],'caps','exec'))
for n in ['1606.06248','1610.05290','1610.09587','1606.04029','2611.01172']:
 q=subprocess.run(['pdftotext','-layout',str(L/'sources'/ (n+'.pdf')),'-'],capture_output=True,timeout=30);put('sources/'+n+'.txt',q.stdout);js('receipts/convert-'+n+'-'+str(time.time_ns())+'.json',{'true_exit':q.returncode,'reaped':True,'stderr':q.stderr.decode()});assert q.returncode==0
 s=q.stdout.decode().splitlines();hits=[i for i,x in enumerate(s) if re.search('Conjecture|conjecture|functional digraph|lower interval|simple polytope|shifted-balanced',x)];seen=set();print('SOURCE',n)
 for i in hits:
  for j in range(max(0,i-2),min(len(s),i+7)):
   if j not in seen:print(str(j+1)+': '+s[j]);seen.add(j)
receipt('inspect-sources',{'true_exit':0})
