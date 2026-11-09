from pathlib import Path
import json,subprocess,sys
D=Path(__file__).resolve().parents[1]
w=json.loads((D/'downloads/openalex-source/body').read_text());h=json.loads((D/'downloads/pool-head/body').read_text())['sha'];print('OPENALEX',w['id'],w['cited_by_count'],'POOL',h)
args=[f'pool-tree|https://api.github.com/repos/Vilin97/lean-pool/git/trees/{h}?recursive=1',f'citing|https://api.openalex.org/works?filter=cites:{w["id"].split("/")[-1]}&per-page=200','approaches|https://arxiv.org/pdf/2009.01996','join-II|https://arxiv.org/pdf/2112.04142','arxiv-v1|https://arxiv.org/pdf/1805.04888v1']
subprocess.run([sys.executable,'-I','-B',str(D/'scripts/fetch.py'),*args],check=True)
