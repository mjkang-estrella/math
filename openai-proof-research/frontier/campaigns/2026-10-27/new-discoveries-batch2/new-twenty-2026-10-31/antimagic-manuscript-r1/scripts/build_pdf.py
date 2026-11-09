import os, pathlib, html, subprocess
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
O=pathlib.Path(__file__).resolve().parents[1]
T=O/'tmp';T.mkdir(exist_ok=True)
for key in ['XDG_CACHE_HOME','XDG_CONFIG_HOME']:
 os.environ[key]=str(T/key);pathlib.Path(os.environ[key]).mkdir(exist_ok=True)
os.environ['HOME']=str(T)
config='<fontconfig><dir>'+str(O/'fonts')+'</dir><cachedir>'+str(T/'fontcache')+'</cachedir></fontconfig>'
(T/'fonts.conf').write_text(config);os.environ['FONTCONFIG_FILE']=str(T/'fonts.conf')
files=[]
for idx,page in enumerate((O/'paper.md').read_text().split('---PAGE---'),1):
 paras=[]
 for p in page.strip().split('\n\n'):
  p=p.strip()
  if p.startswith('# '):p='<span size="20000" weight="bold">'+html.escape(p[2:])+'</span>'
  elif p.startswith('## '):p='<span size="15000" weight="bold">'+html.escape(p[3:])+'</span>'
  else:p=html.escape(p)
  paras.append(p)
 paras.append('<span size="9000">DRAFT • AI-assisted • MathDB 354228 • '+str(idx)+'</span>')
 text=T/('page-'+str(idx)+'.pango');text.write_text('\n\n'.join(paras))
 pdf=T/('page-'+str(idx)+'.pdf');files.append(str(pdf))
 subprocess.run(['pango-view','--no-display','--markup',('--font=Liberation Serif 10' if idx==8 else '--font=Liberation Serif 11'),'--dpi=72','--width=516','--height=696','--margin=48','--line-spacing=1.06','--output='+str(pdf),str(text)],check=True)
subprocess.run(['gs','-q','-dBATCH','-dNOPAUSE','-dSAFER','-sDEVICE=pdfwrite','-dFIXEDMEDIA','-dAutoRotatePages=/None','-sPAPERSIZE=letter','-dPDFFitPage','-sOutputFile='+str(O/'paper.pdf')]+files,check=True)
print('Built eight-page manuscript using Pango/Cairo and Ghostscript')
