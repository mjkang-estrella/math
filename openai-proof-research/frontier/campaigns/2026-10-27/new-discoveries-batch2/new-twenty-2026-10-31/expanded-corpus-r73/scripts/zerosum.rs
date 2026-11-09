// 378902: search for sequences S over Z_n, |S|=n+k, with 0 not in Sigma_n(S) and h(S)<=k
// (a counterexample to h(n,k)>=k+1). Since |S|=n+k, an n-term zero sum exists iff
// sigma(S) in Sigma_k(S) (complement of a k-subsequence). Translation S->S+t preserves Sigma_n
// membership of 0 (adds n*t=0), so WLOG 0 has maximal multiplicity h0=h(S); we enumerate
// h0 in 1..=k and multiplicity vectors v_1..v_{n-1} in [0,h0] with total n+k.
// DP: reach[j] = bitmask of sums of j-term subsequences (j<=k).
use std::env;
struct St{n:usize,k:usize,v:Vec<usize>,found:u64,checked:u64,first:Option<Vec<usize>>}
fn sigk(n:usize,k:usize,v:&[usize])->Vec<u64>{ // returns bitmask per j of Sigma_j
 let mut r=vec![0u64;k+1]; r[0]=1;
 for g in 0..n{ let m=v[g].min(k); if m==0{continue;}
  let old=r.clone();
  for j in 1..=k{ let mut acc=r[j]; for c in 1..=m.min(j){ let src=old[j-c]; let sh=(g*c)%n; acc|=rot(src,sh,n);} r[j]=acc; }
 }
 r}
fn rot(x:u64,s:usize,n:usize)->u64{ if s==0{return x;} let mask=if n==64{u64::MAX}else{(1u64<<n)-1}; ((x<<s)|(x>>(n-s)))&mask }
impl St{
 fn rec(&mut self,g:usize,left:usize,h0:usize){
  let n=self.n;
  if g==n{ if left!=0{return;} self.checked+=1;
    let tot:usize=(0..n).map(|x| x*self.v[x]).sum::<usize>()%n;
    let r=sigk(n,self.k,&self.v);
    if (r[self.k]>>tot)&1==0 { self.found+=1; if self.first.is_none(){self.first=Some(self.v.clone());} }
    return;}
  if left > h0*(n-g) {return;}
  for m in 0..=h0.min(left){ self.v[g]=m; self.rec(g+1,left-m,h0); }
  self.v[g]=0;
 }
}
fn main(){
 let a:Vec<usize>=env::args().skip(1).map(|x|x.parse().unwrap()).collect(); let (n,k)=(a[0],a[1]);
 let cap=if a.len()>2{a[2]}else{k}; // optional multiplicity cap (default k = the conjecture's test)
 let mut s=St{n,k,v:vec![0;n],found:0,checked:0,first:None};
 for h0 in 1..=cap{ if h0>n+k{break;} s.v=vec![0;n]; s.v[0]=h0; s.rec(1,n+k-h0,h0); }
 println!("n={} k={} cap={} multisets_checked={} counterexamples(h<=k, 0 notin Sigma_n)={} first={:?}",n,k,cap,s.checked,s.found,s.first);
}
