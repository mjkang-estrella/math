import pathlib,subprocess,hashlib,json
D=pathlib.Path(__file__).resolve().parent
subprocess.run(['pdftoppm','-f','51','-l','51','-scale-to','1400','-singlefile','-png',str(D/'ems4086.pdf'),str(D/'jet-primary-page')],check=True)
p=D/'jet-primary-page.png';b=p.read_bytes();r={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'pdf_page':51,'source':'ems4086.pdf'};(D/'image-binding.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
