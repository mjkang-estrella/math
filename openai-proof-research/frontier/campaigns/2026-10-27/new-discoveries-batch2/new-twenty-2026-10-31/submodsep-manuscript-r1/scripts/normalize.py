from pathlib import Path
L=Path(__file__).resolve().parents[1]
p=L/'scripts/build_pdf.py';s=p.read_text().replace("['ps2pdf','-sPAPERSIZE=letter',str(L/'paper.ps'),str(L/'paper.pdf')]","['gs','-q','-dBATCH','-dNOPAUSE','-sDEVICE=pdfwrite','-sPAPERSIZE=letter','-sOutputFile='+str(L/'paper.pdf'),'-c','<</BeginPage {pop 0.90 0.90 scale 34 44 translate}>> setpagedevice','-f',str(L/'paper.ps')]").replace("str(L/'qa/page')","str(L/'qa/approved-page')")
p.write_text(s)
