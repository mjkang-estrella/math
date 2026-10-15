#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Exact finite checks of the integral local projection; not an all-m proof."""
from collections import Counter
from itertools import permutations,product
from math import factorial
from pathlib import Path
import json

def sign(p):return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
def board(m):return [(i,j) for i in range(1,m+1) for j in range(1,m+2-i)]
def alternations(m,kind):
 B=board(m);blocks=[[k for k,(i,j) in enumerate(B) if (i if kind=='R' else j)==r] for r in range(1,m+1)]
 out={}
 for choices in product(*(list(permutations(range(1,len(block)+1))) for block in blocks)):
  word=[0]*len(B);coefficient=1
  for block,p in zip(blocks,choices):
   coefficient*=sign(p)
   for k,a in zip(block,p):word[k]=a
  word=tuple(word);assert word not in out;out[word]=coefficient
 return out

def target(m):return tuple((m+1-i,m+2-i-j) for i,j in board(m))
def project(a,b,c,m,mutation=None):
 if mutation not in ['no-filter','old-factorial']:
  if mutation=='wrong-filter':
   if a!=b:return None
  elif a!=c:return None
 out=tuple((x+y-(0 if mutation=='wrong-sum' else 1),z if mutation=='old-factorial' else x) for x,y,z in zip(a,b,c))
 D={(r,x) for r in range(1,m+1) for x in range(1,r+1)}
 return out if len(set(out))==len(out) and set(out)==D else None

def expand(m,R,C,mutation=None):
 out=Counter();survivors=0
 for a,b,c in product(R,R,C):
  v=project(a,b,c,m,mutation)
  if v is not None:
   survivors+=1;out[v]+=R[a]*R[b]*C[c]
 return {k:v for k,v in out.items() if v},survivors

def act(g,w):
 out=[None]*len(w)
 for k,x in enumerate(w):out[g[k]]=x
 return tuple(out)

def main():
 baseline=[]
 for m in range(1,4):
  R=alternations(m,'R');C=alternations(m,'C');out,count=expand(m,R,C)
  assert out=={target(m):1} and count==1
  orbit=0
  for g in permutations(range(len(board(m)))):
   # Independent full monomial expansion after the position action.
   RR={act(g,w):s for w,s in R.items()};CC={act(g,w):s for w,s in C.items()}
   image,survivors=expand(m,RR,CC)
   assert image=={act(g,target(m)):1} and survivors==1
   orbit+=1
  assert orbit==factorial(len(board(m)))
  baseline.append({'m':m,'N':len(board(m)),'single_layer_terms':len(R),'triple_terms_per_orbit_vector':len(R)**3,'orbit_vectors_expanded':orbit,'surviving_terms_each':1,'coefficient':1})
 # Larger finite controls prune only the local a=c condition, without using
 # either palette uniqueness or the square-deficit proof as a premise.
 larger=[]
 for m in [4,5]:
  R=alternations(m,'R');C=alternations(m,'C');intersection=set(R)&set(C)
  out=Counter();count=0
  for a in intersection:
   for b in R:
    v=project(a,b,a,m)
    if v is not None:out[v]+=R[a]*R[b]*C[a];count+=1
  out={k:v for k,v in out.items() if v}
  assert out=={target(m):1} and count==1
  larger.append({'m':m,'single_layer_terms':len(R),'matching_word_count':len(intersection),'post_matching_terms_checked':len(intersection)*len(R),'surviving_terms':count,'coefficient':1})
 R=alternations(2,'R');C=alternations(2,'C');mutations=[]
 for mutation in ['no-filter','old-factorial','wrong-filter','wrong-sum','replace-C-by-R']:
  out,count=expand(2,R,R if mutation=='replace-C-by-R' else C,mutation)
  assert out!={target(2):1}
  row={'mutation':mutation,'target_identity_rejected':True,'surviving_terms':count,'nonzero_output_words':len(out),'target_coefficient':out.get(target(2),0)}
  if mutation=='no-filter':assert not out;row['unmatched_third_layer_cancels']=True
  if mutation=='old-factorial':assert out=={target(2):2};row['reduction_mod_2_is_zero']=True
  mutations.append(row)
 result={'status':'all finite exact controls pass; general proof is candidate.md','full_expansion':baseline,'larger_matching_pruned_expansion':larger,'mutations':mutations,'arithmetic':'integer coefficients; no floating point or character multiplicity inference','all_m_proved_by_computation':False}
 Path('projection-checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
