// gen: generic Game-of-Arrows solver for arbitrary trees, written independently of the spider/H code.
// A component is a status-labelled tree (Def. 3.3) stored in thread-compressed form: nodes are the vertices
// that are not "status N of degree 2"; threads are maximal paths through status-N degree-2 vertices, with length.
// Moves, legality and splitting follow Lemma 3.2 / Lemma 3.5 / Prop. 3.6 literally; NO run formulas are used.
// Memo on a canonical AHU string, also canonical under global reversal (I<->O).
// Usage: ./gen tree "<description>" ...   description: centres and threads, e.g.
//   H a1 a2 l b1 b2        caterpillar3 a1 a2 l1 b l2 c1 c2      spider x1 x2 ...
#include <bits/stdc++.h>
using namespace std;
enum {N_=0,I_=1,O_=2,F_=3};
struct Comp { vector<int> st; vector<array<int,3>> th; };
static inline int outAfter(int s){ return s==N_?O_: s==I_?F_: s==O_?O_:F_; }
static inline int inAfter(int s){ return s==N_?I_: s==I_?I_: s==O_?F_:F_; }
unordered_map<string,int> memo;
string canon(const Comp& c){
  int n=c.st.size(); vector<vector<pair<int,int>>> adj(n);
  for(auto& t:c.th){ adj[t[0]].push_back({t[1],t[2]}); adj[t[1]].push_back({t[0],t[2]}); }
  vector<int> deg(n); for(int i=0;i<n;i++) deg[i]=adj[i].size();
  vector<int> rem(n,0); int left=n; vector<int> layer; for(int i=0;i<n;i++) if(deg[i]<=1) layer.push_back(i);
  while(left>2){ vector<int> nx; for(int x:layer){ rem[x]=1; left--; for(auto& e:adj[x]) if(!rem[e.first]){ if(--deg[e.first]==1) nx.push_back(e.first);} } layer=nx; }
  vector<int> cen; for(int i=0;i<n;i++) if(!rem[i]) cen.push_back(i);
  string best;
  for(int fl=0;fl<2;fl++){
    function<string(int,int)> rec=[&](int x,int p)->string{ vector<string> ch;
      for(auto& e:adj[x]) if(e.first!=p) ch.push_back(to_string(e.second)+rec(e.first,x));
      sort(ch.begin(),ch.end()); int s=c.st[x]; if(fl&&(s==I_||s==O_)) s=3-s;
      string r="("; r+=char('a'+s); for(auto& z:ch) r+=z; r+=")"; return r; };
    for(int x:cen){ string s=rec(x,-1); if(best.empty()||s<best) best=s; }
  }
  return best;
}
// normalise an arbitrary (not nec. connected) structure into connected components
void normalise(Comp c, vector<Comp>& out){
  int n=c.st.size();
  // split F nodes: give every thread end at an F node its own F node
  vector<int> cnt(n,0);
  for(auto& t:c.th) for(int k=0;k<2;k++){ int x=t[k]; if(c.st[x]==F_){ if(cnt[x]++>0){ c.st.push_back(F_); t[k]=c.st.size()-1; } } }
  n=c.st.size();
  vector<int> par(n); iota(par.begin(),par.end(),0);
  function<int(int)> f=[&](int x){ return par[x]==x?x:par[x]=f(par[x]); };
  for(auto& t:c.th) par[f(t[0])]=f(t[1]);
  map<int,int> root2comp; vector<int> newid(n,-1);
  for(auto& t:c.th){ int r=f(t[0]); if(!root2comp.count(r)){ root2comp[r]=out.size(); out.push_back(Comp()); } }
  for(int x=0;x<n;x++){ bool used=false; for(auto& t:c.th) if(t[0]==x||t[1]==x){used=true;break;} if(!used) continue;
    Comp& C=out[root2comp[f(x)]]; newid[x]=C.st.size(); C.st.push_back(c.st[x]); }
  for(auto& t:c.th){ Comp& C=out[root2comp[f(t[0])]]; C.th.push_back({newid[t[0]],newid[t[1]],t[2]}); }
  // merge status-N degree-2 nodes (cannot arise from legal play from a tree, but keep normal form)
  for(auto& C:out){ bool ch=true; while(ch){ ch=false; int m=C.st.size(); vector<int> d(m,0); for(auto& t:C.th){d[t[0]]++;d[t[1]]++;}
      for(int x=0;x<m&&!ch;x++) if(C.st[x]==N_&&d[x]==2){ int i1=-1,i2=-1; for(int i=0;i<(int)C.th.size();i++) if(C.th[i][0]==x||C.th[i][1]==x){ if(i1<0)i1=i; else i2=i; }
          auto A=C.th[i1],B=C.th[i2]; int a=A[0]==x?A[1]:A[0], b=B[0]==x?B[1]:B[0];
          C.th.erase(C.th.begin()+max(i1,i2)); C.th.erase(C.th.begin()+min(i1,i2)); C.th.push_back({a,b,A[2]+B[2]});
          // remove node x
          C.st.erase(C.st.begin()+x); for(auto& t:C.th){ if(t[0]>x)t[0]--; if(t[1]>x)t[1]--; } ch=true; } } }
}
int value(const Comp& c);
int valueOf(const Comp& c){ vector<Comp> cs; normalise(c,cs); int x=0; for(auto& C:cs) x^=value(C); return x; }
int value(const Comp& c){
  string key=canon(c); auto it=memo.find(key); if(it!=memo.end()) return it->second;
  int n=c.st.size(); vector<int> deg(n,0); for(auto& t:c.th){deg[t[0]]++;deg[t[1]]++;}
  vector<char> seen(64,0);
  auto okTail=[&](int x){ return deg[x]>=2 || c.st[x]==I_ || c.st[x]==F_; };
  auto okHead=[&](int x){ return deg[x]>=2 || c.st[x]==O_ || c.st[x]==F_; };
  for(int ti=0;ti<(int)c.th.size();ti++){ int a=c.th[ti][0], b=c.th[ti][1], L=c.th[ti][2];
    for(int j=1;j<=L;j++) for(int dir=0;dir<2;dir++){ // dir0: w_{j-1} -> w_j (toward b)
      bool leftIsTail = (dir==0);
      if(j-1==0){ if(leftIsTail? !okTail(a) : !okHead(a)) continue; }
      if(j==L){ if(leftIsTail? !okHead(b) : !okTail(b)) continue; }
      Comp d=c; d.th.erase(d.th.begin()+ti);
      if(j-1==0) d.st[a]= leftIsTail? outAfter(d.st[a]) : inAfter(d.st[a]);
      else { d.st.push_back(leftIsTail?O_:I_); d.th.push_back({a,(int)d.st.size()-1,j-1}); }
      if(j==L) d.st[b]= leftIsTail? inAfter(d.st[b]) : outAfter(d.st[b]);
      else { d.st.push_back(leftIsTail?I_:O_); d.th.push_back({(int)d.st.size()-1,b,L-j}); }
      int v=valueOf(d); if(v>=(int)seen.size()) seen.resize(v+1,0); seen[v]=1; } }
  int g=0; while(g<(int)seen.size()&&seen[g]) g++;
  memo[key]=g; return g;
}
// builders: centre nodes N, legs = threads to an F leaf
struct Builder { Comp c; int node(int s){ c.st.push_back(s); return c.st.size()-1; }
  void leg(int x,int len){ int f=node(F_); c.th.push_back({x,f,len}); } void bridge(int x,int y,int len){ c.th.push_back({x,y,len}); } };
int main(int argc,char**argv){
  int i=1;
  while(i<argc){ string t=argv[i++]; Builder B; string desc=t;
    if(t=="H"){ int a1=atoi(argv[i]),a2=atoi(argv[i+1]),l=atoi(argv[i+2]),b1=atoi(argv[i+3]),b2=atoi(argv[i+4]); i+=5;
      int u=B.node(N_),v=B.node(N_); B.leg(u,a1); B.leg(u,a2); B.bridge(u,v,l); B.leg(v,b1); B.leg(v,b2); desc+=" "+to_string(a1)+" "+to_string(a2)+" "+to_string(l)+" "+to_string(b1)+" "+to_string(b2);}
    else if(t=="C3"){ int a1=atoi(argv[i]),a2=atoi(argv[i+1]),l1=atoi(argv[i+2]),b=atoi(argv[i+3]),l2=atoi(argv[i+4]),c1=atoi(argv[i+5]),c2=atoi(argv[i+6]); i+=7;
      int u=B.node(N_),v=B.node(N_),w=B.node(N_); B.leg(u,a1); B.leg(u,a2); B.bridge(u,v,l1); B.leg(v,b); B.bridge(v,w,l2); B.leg(w,c1); B.leg(w,c2);
      for(int k=-7;k<0;k++) desc+=" "+string(argv[i+k]); }
    else if(t=="S"){ int k=atoi(argv[i++]); int c=B.node(N_); for(int q=0;q<k;q++){ B.leg(c,atoi(argv[i])); desc+=" "+string(argv[i]); i++; } }
    else { fprintf(stderr,"unknown %s\n",t.c_str()); return 1; }
    int g=valueOf(B.c); printf("%s g=%d memo=%zu\n",desc.c_str(),g,memo.size()); fflush(stdout);
  }
}
