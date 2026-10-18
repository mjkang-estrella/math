#!/usr/bin/env python3
"""Reason-checked identity controls on disposable copies only; MIT."""
import argparse,hashlib,json,shutil,tempfile,subprocess,os
from pathlib import Path
def main():
 p=argparse.ArgumentParser();p.add_argument('--anchor',required=True);p.add_argument('--repository-campaign',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=Path(__file__).resolve().parent
 a.output.mkdir(parents=True,exist_ok=False);results=[]
 cases=[('positive',None),('wrong-anchor','external manifest mismatch'),('changed','file inventory mismatch'),('missing','file inventory mismatch'),('extra','file inventory mismatch'),('directory','directory inventory mismatch'),('symlink','symlink entry'),('hardlink','hardlink entry'),('fifo','nonregular entry'),('forged-status','status claim'),('changed-upstream','upstream evidence mismatch'),('malformed-anchor','malformed anchor')]
 for name,reason in cases:
  dst=a.output/name;shutil.copytree(src,dst);anchor=a.anchor;campaign=a.repository_campaign
  if name=='wrong-anchor':anchor='0'*64
  elif name=='malformed-anchor':anchor='x'
  elif name=='changed':(dst/'README.md').write_text('changed')
  elif name=='missing':(dst/'README.md').unlink()
  elif name=='extra':(dst/'extra.txt').write_text('extra')
  elif name=='directory':(dst/'extra-dir').mkdir()
  elif name=='symlink':(dst/'link').symlink_to('README.md')
  elif name=='hardlink':os.link(dst/'README.md',dst/'linked')
  elif name=='fifo':os.mkfifo(dst/'fifo')
  elif name in ('forged-status','changed-upstream'):
   q=json.loads((dst/'provenance.json').read_text())
   if name=='forged-status':q['accepted']=True
   else:
    campaign=a.output/'fake-campaign';campaign.mkdir()
    for r in q['evidence']:
     f=campaign/r['source'];f.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(a.repository_campaign/r['source'],f)
    (campaign/q['evidence'][0]['source']).write_text('changed')
   (dst/'provenance.json').write_text(json.dumps(q));m=json.loads((dst/'manifest.json').read_text());m['files']['provenance.json']=hashlib.sha256((dst/'provenance.json').read_bytes()).hexdigest();(dst/'manifest.json').write_text(json.dumps(m));anchor=hashlib.sha256((dst/'manifest.json').read_bytes()).hexdigest()
  r=subprocess.run(['python3','-B',str(src/'verify.py'),'--root',str(dst),'--anchor',anchor,'--repository-campaign',str(campaign)],text=True,capture_output=True)
  ok=(r.returncode==0) if reason is None else (r.returncode!=0 and reason in r.stderr+r.stdout)
  results.append({'case':name,'passed':ok,'expected_reason':reason,'stdout':r.stdout,'stderr':r.stderr});assert ok,(name,r.stdout,r.stderr)
 (a.output/'receipt.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps({'controls':len(results),'all_expected':True,'receipt':str(a.output/'receipt.json')}))
if __name__=='__main__':main()
