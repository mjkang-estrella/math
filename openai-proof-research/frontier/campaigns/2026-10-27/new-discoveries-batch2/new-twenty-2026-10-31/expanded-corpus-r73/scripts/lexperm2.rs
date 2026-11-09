// 378584 faster search. Same semantics as lexperm.rs: lexicographically least permutation sigma of Z_n
// (n prime) whose graph has exactly T=(n-1)/2 collinear triples. New point k is collinear with
// previous points i<j<k iff slope(i,k)==slope(j,k) where slope(i,k)=(sigma(k)-sigma(i))/(k-i) mod n
// (abscissae are distinct, so slopes are defined). New triples = sum_s C(m_s,2), m_s = #previous
// points at slope s from k. Optional args: a fixed prefix sigma(0..m-1) given as further arguments;
// then the search covers exactly the permutations with that prefix (in lex order).
use std::env;
struct S{n:usize,t:usize,sig:Vec<usize>,used:Vec<bool>,nodes:u64,inv:Vec<usize>,cnt:Vec<u32>}
impl S{
 fn add(&mut self,k:usize)->usize{ // number of new collinear triples formed by point k with earlier points
  let n=self.n; let mut c=0usize;
  for i in 0..k{ let s=((self.sig[k]+n-self.sig[i])%n)*self.inv[k-i]%n; c+=self.cnt[s] as usize; self.cnt[s]+=1; }
  for i in 0..k{ let s=((self.sig[k]+n-self.sig[i])%n)*self.inv[k-i]%n; self.cnt[s]=0; }
  c}
 fn dfs(&mut self,k:usize,cnt:usize,lo:usize)->bool{
  self.nodes+=1;
  if k==self.n{return cnt==self.t;}
  for v in 0..self.n{ if self.used[v]{continue;}
   self.sig[k]=v; let c=cnt+self.add(k);
   if c<=self.t{self.used[v]=true; if self.dfs(k+1,c,lo){return true;} self.used[v]=false;}
  }
  false}
}
fn main(){
 let a:Vec<usize>=env::args().skip(1).map(|x|x.parse().unwrap()).collect();
 let n=a[0]; let pre=&a[1..];
 let mut inv=vec![0;n]; for x in 1..n{ for y in 1..n{ if x*y%n==1{inv[x]=y;} } }
 let mut s=S{n,t:(n-1)/2,sig:vec![0;n],used:vec![false;n],nodes:0,inv,cnt:vec![0;n]};
 let mut c=0; for (k,&v) in pre.iter().enumerate(){ assert!(!s.used[v]); s.sig[k]=v; s.used[v]=true; c+=s.add(k);}
 let ok= if c<=s.t { s.dfs(pre.len(),c,0) } else {false};
 let g:Vec<usize>=(0..n).map(|x| if x==1{1}else{ x*s.inv[(x+n-1)%n]%n }).collect();
 println!("n={} T={} prefix={:?} found={} nodes={}",n,s.t,pre,ok,s.nodes);
 if ok { println!("lexmin: {:?}\ng     : {:?}\nlexmin_equals_g={}",s.sig,g,s.sig==g); } else { println!("g     : {:?}",g); }
}
