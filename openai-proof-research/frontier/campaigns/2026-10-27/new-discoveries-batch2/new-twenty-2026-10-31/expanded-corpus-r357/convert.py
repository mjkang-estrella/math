exec(compile(open('investigate.py').read().split("mode=sys.argv[1]")[0],'caps','exec'))
for name in sys.argv[1:]:
 p=(L/'sources'/name).resolve();assert p.is_relative_to(L)
 q=subprocess.run(['pdftotext','-layout',str(p),'-'],capture_output=True,timeout=50)
 put('sources/'+p.stem+'.txt',q.stdout);js('receipts/convert-'+p.stem+'.json',{'returncode':q.returncode,'stderr':q.stderr.decode(errors='replace'),'text_sha256':sha(q.stdout),'child_reaped':True})
 assert q.returncode==0
receipt('convert-'+str(time.time_ns()),{'true_exit':0})
