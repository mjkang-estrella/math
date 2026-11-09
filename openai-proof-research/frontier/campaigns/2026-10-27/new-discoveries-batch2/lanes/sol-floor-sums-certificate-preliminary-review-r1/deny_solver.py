import sys,runpy
class Deny:
 def find_spec(self,name,*args):
  if name.split(".")[0] in {"z3","pysmt","cvc5"}: raise ImportError("solver unavailable")
sys.meta_path.insert(0,Deny())
def audit(event,args):
 if event in {"subprocess.Popen","os.system","os.posix_spawn"}:raise RuntimeError("external process unavailable")
sys.addaudithook(audit)
runpy.run_path(sys.argv[1],run_name="__main__")
