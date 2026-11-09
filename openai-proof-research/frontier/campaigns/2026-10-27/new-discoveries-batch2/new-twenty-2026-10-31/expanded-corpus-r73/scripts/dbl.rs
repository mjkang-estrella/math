// 378740 screen. For t,r (0<r<t) enumerate all N=C(t,2)+r subsets X of the affine grid {0..m-1}^2
// (chart z=1 of P^2 over Q). Keep X with generic Hilbert function (1,2,...,t-1,r):
//   rank(eval, deg t-2) == C(t,2) and rank(eval, deg t-1) == N   (checked modulo two primes; a
//   full rank mod p implies full rank over Q; X rejected only if deficient mod both primes).
// For kept X compute h_{2X}(d) = rank of {F(P), dF/dx(P), dF/dy(P) : P in X} on polynomials of
// degree <= d (dehomogenised forms of degree d), modulo P1. Since rank mod p <= rank over Q, any
// X with modular h_{2X}(d) >= ref(d) for all d certainly satisfies the conjectured inequality over Q;
// X with some modular value < ref(d) is printed as a CANDIDATE for exact rational re-verification.
use std::env; use std::collections::HashMap;
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
fn monos(d:usize)->Vec<(usize,usize)>{let mut v=vec![];for i in 0..=d{for j in 0..=d-i{v.push((i,j));}}v}
fn ev(pts:&[(i64,i64)],d:usize,p:u64)->Vec<Vec<u64>>{ let ms=monos(d); pts.iter().map(|&(a,b)| ms.iter().map(|&(i,j)| pw(a.rem_euclid(p as i64) as u64,i as u64,p)*pw(b.rem_euclid(p as i64) as u64,j as u64,p)%p).collect()).collect() }
fn dbl(pts:&[(i64,i64)],d:usize,p:u64)->usize{ let ms=monos(d); let mut m=vec![];
 for &(a,b) in pts{ let a=a.rem_euclid(p as i64) as u64; let b=b.rem_euclid(p as i64) as u64;
  m.push(ms.iter().map(|&(i,j)| pw(a,i as u64,p)*pw(b,j as u64,p)%p).collect());
  m.push(ms.iter().map(|&(i,j)| if i==0{0}else{(i as u64)*pw(a,(i-1) as u64,p)%p*pw(b,j as u64,p)%p}).collect());
  m.push(ms.iter().map(|&(i,j)| if j==0{0}else{(j as u64)*pw(a,i as u64,p)%p*pw(b,(j-1) as u64,p)%p}).collect()); }
 rank(m,p)}
fn main(){
 let a:Vec<String>=env::args().skip(1).collect(); let t:usize=a[0].parse().unwrap(); let r:usize=a[1].parse().unwrap(); let m:i64=a[2].parse().unwrap();
 let dh:Vec<usize>=a[3].split(',').map(|x|x.parse().unwrap()).collect(); // reference first difference
 let mut href=vec![]; let mut s=0; for &x in &dh{s+=x;href.push(s);} let n=t*(t-1)/2+r; let top=href.len()+1;
 let grid:Vec<(i64,i64)>=(0..m).flat_map(|x|(0..m).map(move|y|(x,y))).collect(); let g=grid.len();
 let mut idx:Vec<usize>=(0..n).collect(); let mut total=0u64; let mut generic=0u64; let mut cands=0u64;
 let mut hist:HashMap<Vec<usize>,u64>=HashMap::new();
 loop{ total+=1; let pts:Vec<(i64,i64)>=idx.iter().map(|&i|grid[i]).collect();
  let gen=|p|{ rank(ev(&pts,t-2,p),p)==t*(t-1)/2 && rank(ev(&pts,t-1,p),p)==n };
  if gen(P1) || gen(P2){ generic+=1;
   let h:Vec<usize>=(0..top).map(|d| dbl(&pts,d,P1)).collect();
   let bad=(0..top).any(|d| h[d] < if d<href.len(){href[d]}else{3*n});
   if bad{cands+=1; if cands<=20{println!("CANDIDATE {:?} h={:?}",pts,h);} }
   *hist.entry(h).or_insert(0)+=1; }
  // next combination
  let mut i=n; loop{ if i==0{break;} i-=1; if idx[i]!=i+g-n{ idx[i]+=1; for j in i+1..n{idx[j]=idx[j-1]+1;} break;} if i==0{i=usize::MAX;break;} }
  if i==usize::MAX{break;} if n==0{break;}
 }
 println!("t={} r={} grid={}x{} N={} subsets={} generic={} candidates={} ref_h={:?}",t,r,m,m,n,total,generic,cands,href);
 let mut hv:Vec<_>=hist.into_iter().collect(); hv.sort(); for (h,c) in hv{ println!("  h2X={:?} count={}",h,c);} }
