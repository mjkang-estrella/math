#!/usr/bin/env python3
"""Copyright 2026 Myeongjin Kang. SPDX-License-Identifier: MIT.
Deterministic reading views; originals and views retain source-text rights.
"""
from html.parser import HTMLParser
from pathlib import Path
import re
import sys
class View(HTMLParser):
 def __init__(self):
  super().__init__(convert_charrefs=True);self.parts=[];self.skip=0;self.math=0
 def handle_starttag(self,tag,attrs):
  attrs=dict(attrs)
  if self.skip:
   self.skip+=1;return
  if self.math:
   self.math+=1;return
  if tag in ('script','style'):
   self.skip=1;return
  if tag=='math':
   self.parts.append(' '+attrs.get('alttext','[MATH WITHOUT ALTTEXT]')+' ');self.math=1;return
  if tag in ('p','div','section','article','h1','h2','h3','h4','h5','tr','li','blockquote','br'):self.parts.append('\n')
 def handle_startendtag(self,tag,attrs):
  if not self.math and not self.skip and tag=='br':self.parts.append('\n')
 def handle_endtag(self,tag):
  if self.skip:self.skip-=1;return
  if self.math:self.math-=1;return
  if tag in ('p','div','section','article','h1','h2','h3','h4','h5','tr','li','blockquote'):self.parts.append('\n')
 def handle_data(self,s):
  if not self.math and not self.skip:self.parts.append(s)
def render(raw):
 v=View();v.feed(raw);lines=[re.sub(r'\s+',' ',line).strip() for line in ''.join(v.parts).splitlines()];lines=[x for x in lines if x]
 return '\n'.join(lines)+'\n'

if __name__ == '__main__':
 assert sys.argv[1:] in ([], ['--record'])
 for p in sorted((Path(__file__).resolve().parents[1]/'inputs/literature').glob('*.html')):
  body=render(p.read_text())
  if sys.argv[1:] == ['--record']:
   p.with_suffix('.txt').write_text(body)
  else:
   assert p.with_suffix('.txt').read_text()==body, str(p)
  print(p.name,len(body.splitlines()))
