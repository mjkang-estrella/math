#!/usr/bin/env python3
"""Replay selected PDF or original scoped Lean support from a clean stage; MIT."""
import argparse,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
from prepare import authenticate,validate

def main():
 p=argparse.ArgumentParser();p.add_argument('--anchor',required=True);p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--tectonic',type=Path);p.add_argument('--lean',type=Path);p.add_argument('--cache',type=Path);a=p.parse_args()
 validate(a.stage,authenticate(a.anchor))
 if a.tectonic and not a.lean:
  cmd=['python3','-B',str(a.stage/'t212m-manuscript-v1/build.py'),'--tectonic',str(a.tectonic),'--output',str(a.output)]
 elif a.lean and a.cache and not a.tectonic:
  cmd=['python3','-B',str(a.stage/'t212m-formal-v1/rebuild.py'),'--lean',str(a.lean),'--cache',str(a.cache),'--output',str(a.output)]
 else:raise ValueError('choose --tectonic OR both --lean and --cache')
 subprocess.run(cmd,check=True)
if __name__=='__main__':main()
