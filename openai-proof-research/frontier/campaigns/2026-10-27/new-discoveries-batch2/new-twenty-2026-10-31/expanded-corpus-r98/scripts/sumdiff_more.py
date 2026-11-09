import subprocess
for e in list(range(41,65))+[72,81,96,100,120,128,144,150,160,180,192,200,210,240,256]:
 for mode in ['zero','asym']:subprocess.run(['python','scripts/sumdiff.py',str(e),mode],check=True)
