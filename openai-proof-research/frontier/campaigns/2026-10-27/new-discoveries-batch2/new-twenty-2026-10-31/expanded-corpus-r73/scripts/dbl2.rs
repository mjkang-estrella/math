// 378740 projective pool screen. Args: t r dh(ref first difference, comma list) poolfile
// poolfile: one projective point per line "x y z" (integers). Enumerates all N=C(t,2)+r subsets of
// the pool; keeps X with generic Hilbert function (rank of degree t-2 evaluation == C(t,2) and of
// degree t-1 == N, full rank mod either of two primes => full rank over Q); computes modular
// h_{2X}(d) (d>=1: conditions dF/dx,dF/dy,dF/dz at each point, equivalent to F and its first
// derivatives by Euler, p not dividing d; d=0: h=1). Modular rank <= rational rank, so any X with
// all modular values >= ref is certified to satisfy the inequality; others are CANDIDATES.
use std::env; use std::collections::HashMap; use std::fs;
const P1:u64=2147483647; const P2:u64=2147483629;
fn pw(mut b:u64,mut e:u64,p:u64)->u64{let mut r=1;b%=p;while e>0{if e&1==1{r=r*b%p;}b=b*b%p;e>>=1;}r}
fn rank(mut a:Vec<Vec<u64>>,p:u64)->usize{
 let rows=a.len(); if rows==0{return 0;} let cols=a[0].len(); let mut r=0;
 for c in 0..cols{ let mut piv=None; for i in r..rows{ if a[i][c]!=0{piv=Some(i);break;} }
  let Some(pi)=piv else {continue}; a.swap(r,pi); let inv=pw(a[r][c],p-2,p);
  for j in c..cols{a[r][j]=a[r][j]*inv%p;}
  for i in 0..rows{ if i!=r && a[i][c]!=0{ let f=a[i][c]; for j in c..cols{ a[i][j]=(a[i][j]+p-f*a[r][j]%p)%p; } } }
  r+=1; if r==rows{break;} }
 r}
fn monos(d:usize)->Vec<[usize;3]>{let mut v=vec![];for i in 0..=d{for j in 0..=d-i{v.push([i,j,d-i-j]);}}v}
fn md(x:i64,p:u64)->u64{x.rem_euclid(p as i64) as u64}
fn mon(pt:&[u64;3],e:[usize;3],p:u64)->u64{ pw(pt[0],e[0] as u64,p)*pw(pt[1],e[1] as u64,p)%p*pw(pt[2],e[2] as u64,p)%p }
fn ev(pts:&[[u64;3]],d:usize,p:u64)->Vec<Vec<u64>>{ let ms=monos(d); pts.iter().map(|q| ms.iter().map(|&e| mon(q,e,p)).collect()).collect() }
fn dbl(pts:&[[u64;3]],d:usize,p:u64)->usize{ if d==0{return 1;} let ms=monos(d); let mut m=vec![];
 for q in pts{ for v in 0..3{ m.push(ms.iter().map(|&e| if e[v]==0{0}else{ let mut f=e; f[v]-=1; (e[v] as u64)*mon(q,f,p)%p }).collect()); } }
 rank(m,p)}
fn main(){
 let a:Vec<String>=env::args().skip(1).collect(); let t:usize=a[0].parse().unwrap(); let r:usize=a[1].parse().unwrap();
 let dh:Vec<usize>=a[2].split(',').map(|x|x.parse().unwrap()).collect();
 let mut href=vec![]; let mut s=0; for &x in &dh{s+=x;href.push(s);} let n=t*(t-1)/2+r; let top=href.len()+1;
 let pool:Vec<[i64;3]>=fs::read_to_string(&a[3]).unwrap().lines().filter(|l|!l.trim().is_empty()).map(|l|{let v:Vec<i64>=l.split_whitespace().map(|x|x.parse().unwrap()).collect();[v[0],v[1],v[2]]}).collect();
 let g=pool.len(); if g<n{println!("pool {} smaller than N={}",g,n);return;}
 let m1:Vec<[u64;3]>=pool.iter().map(|q|[md(q[0],P1),md(q[1],P1),md(q[2],P1)]).collect();
 let m2:Vec<[u64;3]>=pool.iter().map(|q|[md(q[0],P2),md(q[1],P2),md(q[2],P2)]).collect();
 let mut idx:Vec<usize>=(0..n).collect(); let (mut total,mut generic,mut cands)=(0u64,0u64,0u64);
 let mut hist:HashMap<Vec<usize>,u64>=HashMap::new();
 loop{ total+=1;
  let x1:Vec<[u64;3]>=idx.iter().map(|&i|m1[i]).collect(); let x2:Vec<[u64;3]>=idx.iter().map(|&i|m2[i]).collect();
  let gen=|x:&Vec<[u64;3]>,p|{ rank(ev(x,t-2,p),p)==t*(t-1)/2 && rank(ev(x,t-1,p),p)==n };
  if gen(&x1,P1)||gen(&x2,P2){ generic+=1;
   let h:Vec<usize>=(0..top).map(|d| dbl(&x1,d,P1)).collect();
   if (0..top).any(|d| h[d] < if d<href.len(){href[d]}else{3*n}){ cands+=1; if cands<=10{ let pts:Vec<[i64;3]>=idx.iter().map(|&i|pool[i]).collect(); println!("CANDIDATE {:?} h={:?}",pts,h);} }
   *hist.entry(h).or_insert(0)+=1; }
  let mut i=n; let mut done=true; while i>0{ i-=1; if idx[i]!=i+g-n{ idx[i]+=1; for j in i+1..n{idx[j]=idx[j-1]+1;} done=false; break;} }
  if done{break;}
 }
 println!("t={} r={} pool={} N={} subsets={} generic={} candidates={} ref_h={:?}",t,r,g,n,total,generic,cands,href);
 let mut hv:Vec<_>=hist.into_iter().collect(); hv.sort(); for (h,c) in hv{ println!("  h2X={:?} count={}",h,c);} }
