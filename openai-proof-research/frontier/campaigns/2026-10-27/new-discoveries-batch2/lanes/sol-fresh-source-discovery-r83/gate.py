import subprocess,json
from pathlib import Path
p=Path(__file__).resolve().parent
pat=r"2501[.]18656|Lin.{0,12}Zhou|Hansen|Vuki|2305[.]07301|Arvind|commuting.graph|distance.spectral"
a=subprocess.run(["rg","-l","-i",pat,"openai-proof-research/frontier/campaigns","-g","*.md","-g","*.json","-g","*.txt"],capture_output=True,text=True)
p.joinpath("duplicate-filenames.txt").write_text(a.stdout)
paths=a.stdout.splitlines(); print("files",len(paths))
for f in paths:
 if any(x in Path(f).name.lower() for x in ["finding","discovery","summary","provenance","progress"]):
  z=subprocess.run(["rg","-n","-i","-m","5",pat,f],capture_output=True,text=True)
  print(f);print(z.stdout[:4000])
