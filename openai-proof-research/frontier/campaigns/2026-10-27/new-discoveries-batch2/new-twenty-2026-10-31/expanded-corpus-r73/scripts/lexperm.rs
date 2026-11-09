// 378584: lexicographically least permutation sigma of Z_n (n prime) whose graph {(x,sigma(x))} has
// exactly T=(n-1)/2 collinear triples. For prime n, three points are collinear (lie on some line
// ax+by=c, (a,b)!=(0,0)) iff det((x2-x1,y2-y1),(x3-x1,y3-y1)) == 0 mod n.
// DFS assigns sigma(0),sigma(1),... trying values in increasing order and prunes when the number of
// collinear triples among assigned points exceeds T (it never decreases as points are added).
// The first complete permutation reached with count == T is therefore the lexicographic minimum.
use std::env;
struct S{n:usize,t:usize,sig:Vec<i64>,used:Vec<bool>,nodes:u64}
impl S{
 fn col(&self,a:usize,b:usize,c:usize)->bool{let n=self.n as i64;let d=(b as i64-a as i64)*(self.sig[c]-self.sig[a])-(self.sig[b]-self.sig[a])*(c as i64-a as i64);d.rem_euclid(n)==0}
 fn dfs(&mut self,k:usize,cnt:usize)->bool{
  self.nodes+=1;
  if k==self.n{return cnt==self.t;}
  for v in 0..self.n{ if self.used[v]{continue;}
   self.sig[k]=v as i64; let mut c=cnt; 'o: for i in 0..k{for j in i+1..k{ if self.col(i,j,k){c+=1; if c>self.t{break 'o;}}}}
   if c<=self.t{self.used[v]=true; if self.dfs(k+1,c){return true;} self.used[v]=false;}
  }
  false}
}
fn main(){
 let n:usize=env::args().nth(1).unwrap().parse().unwrap();
 let mut s=S{n,t:(n-1)/2,sig:vec![0;n],used:vec![false;n],nodes:0};
 let ok=s.dfs(0,0);
 let lex=s.sig.clone();
 let ni=n as i64;
 let g:Vec<i64>=(0..ni).map(|x| if x==1{1}else{let d=(x-1).rem_euclid(ni);let inv=(1..ni).find(|t| (d*t)%ni==1).unwrap();(x*inv)%ni}).collect();
 s.sig=g.clone(); let mut cg=0; for a in 0..n{for b in a+1..n{for c in b+1..n{ if s.col(a,b,c){cg+=1;}}}}
 println!("n={} T={} found={} nodes={}\nlexmin: {:?}\ng     : {:?}\ng_triples={} lexmin_equals_g={}",n,s.t,ok,s.nodes,lex,g,cg,lex==g);
}
