exec(read(L/'fetch.py').decode().split("r=json.loads(read(L/'reservation.json'))")[0])
jobs=[('2604.15138-pdf','https://arxiv.org/pdf/2604.15138'),('2501.07098v1-html','https://arxiv.org/html/2501.07098v1'),('2309.00989v1-html','https://arxiv.org/html/2309.00989v1')]
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for x in ex.map(fetch,jobs): print(x)
import subprocess
p=L/'sources/2604.15138-pdf.raw'
if p.exists():
 c=subprocess.run(['pdftotext','-layout',str(p),str(L/'sources/2604.15138-pdf.txt')],timeout=20,capture_output=True);save('receipts/pdftotext-'+str(time.time_ns())+'.json',{'exit':c.returncode,'stderr':c.stderr.decode(),'caps':'inherited runner affinity/CPU/AS; subprocess timeout20'})
