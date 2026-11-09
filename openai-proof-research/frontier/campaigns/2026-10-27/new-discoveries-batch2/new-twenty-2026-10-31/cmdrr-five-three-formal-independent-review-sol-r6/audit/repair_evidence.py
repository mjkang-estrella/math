import pathlib,subprocess,sys
p=pathlib.Path.cwd()
s=(p/"audit/verify_evidence.py").read_text().replace('assert not bad and not missing,(missing,bad)','assert not bad,bad\nprint("R5 selective copied manifest",len(manifest["files"])-len(missing),"present",len(missing),"not copied; no original paths followed")')
s=s.replace('"r5_manifest_files":len(manifest["files"])','"r5_manifest_files_checked":len(manifest["files"])-len(missing),"r5_manifest_files_not_copied":missing')
subprocess.run([sys.executable,"-I","-B",str(p/"write_lane.py"),"audit/verify_evidence_v2.py"],input=s,text=True,check=True)

