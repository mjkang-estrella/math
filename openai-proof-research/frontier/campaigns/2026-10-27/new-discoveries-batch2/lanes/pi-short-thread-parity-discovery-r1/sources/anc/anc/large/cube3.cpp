// cube3: Grundy values of ALL 3-legged spiders S(x,y,z), 1<=x<=y<=z<=M, via the spider recursion
// (Prop 6.1) on sorted leg-code triples (colex index), iterative bottom-up, uint16 values.
// Output: per z: max over x<=y<=z, argmax; global records; all spiders with g>=thr to a file.
#include <bits/stdc++.h>
using namespace std;
typedef uint16_t u16;
static inline int runv(int k,int a,int b){ if(k<=0) return 0; if(a==0&&b==0) return k&1; if(a==0||b==0) return k; if(a==b) return k&1; return (k>=2&&!(k&1))?1:0;}
static inline int flipf(int f){return f==0?0:3-f;}
int M, NC; vector<uint64_t> C3, C2; vector<u16> NV, IV;
static inline int rr(int c){return c/3+1;} static inline int ff(int c){return c%3;}
static inline int cc(int r,int f){return 3*(r-1)+f;}
static inline int flc(int c){return cc(rr(c),flipf(ff(c)));}
static inline uint64_t idx3(int a,int b,int c){ // any order
  if(a>b) swap(a,b); if(b>c) swap(b,c); if(a>b) swap(a,b); return C3[c]+C2[b]+a; }
static inline uint64_t idx2(int a,int b){ if(a>b) swap(a,b); return C2[b]+a; }
static uint32_t stA[1<<14]; static uint32_t stC=0;
int main(int argc,char**argv){
  M=atoi(argv[1]); int thr=argc>2?atoi(argv[2]):1000; NC=3*M;
  C3.resize(NC+1); C2.resize(NC+1); for(uint64_t c=0;c<=(uint64_t)NC;c++){ C3[c]=(c+2)*(c+1)*c/6; C2[c]=(c+1)*c/2; }
  IV.assign(C2[NC],0); NV.assign(C3[NC],0);
  fprintf(stderr,"N states %llu (%.1f MB)\n",(unsigned long long)C3[NC],C3[NC]*2/1e6);
  // I-states: centre status i, two legs
  for(int b=0;b<NC;b++) for(int a=0;a<=b;a++){
    stC++; int L[2]={a,b};
    for(int i=0;i<2;i++){ int r=rr(L[i]),f=ff(L[i]),o=L[1-i],ro=rr(o),fo=ff(o);
      for(int j=1;j<=r;j++) for(int d=1;d<=2;d++){ if(j==r&&f&&d!=f) continue; int det=runv(r-j,d,f),v;
        if(j>=2) v=IV[idx2(cc(j-1,d),o)]; else v=(d==1)?runv(ro,2,fo):runv(ro,0,fo);
        stA[det^v]=stC; } }
    int g=0; while(stA[g]==stC) g++; IV[idx2(a,b)]=g; }
  auto Ival=[&](int a,int b){return (int)IV[idx2(a,b)];};
  auto Oval=[&](int a,int b){return (int)IV[idx2(flc(a),flc(b))];};
  vector<int> zmax(M+1,-1); vector<array<int,3>> zarg(M+1); vector<long long> hist(4096,0);
  FILE* big=fopen(argc>3?argv[3]:"cube3_big.txt","w");
  for(int c=0;c<NC;c++){
    for(int b=0;b<=c;b++) for(int a=0;a<=b;a++){
      stC++; int L[3]={a,b,c};
      for(int i=0;i<3;i++){ if(i>0&&L[i]==L[i-1]) continue; int r=rr(L[i]),f=ff(L[i]); int o1=L[(i+1)%3],o2=L[(i+2)%3];
        for(int j=1;j<=r;j++) for(int d=1;d<=2;d++){ if(j==r&&f&&d!=f) continue; int det=runv(r-j,d,f),v;
          if(j>=2) v=NV[idx3(cc(j-1,d),o1,o2)]; else v=(d==1)?Ival(o1,o2):Oval(o1,o2);
          stA[det^v]=stC; } }
      int g=0; while(stA[g]==stC) g++; NV[C3[c]+C2[b]+a]=g;
      if(ff(a)==0&&ff(b)==0&&ff(c)==0){ int x=rr(a),y=rr(b),z=rr(c); hist[g]++;
        if(g>zmax[z]){zmax[z]=g; zarg[z]={x,y,z};}
        if(g>=thr) fprintf(big,"%d %d %d %d\n",x,y,z,g); }
    }
    if(ff(c)==0){ int z=rr(c); fprintf(stderr,"z=%d done\n",z); }
  }
  fclose(big);
  int run=-1; for(int z=1;z<=M;z++){ if(zmax[z]>run) run=zmax[z]; printf("L=%d maxg_z=%d at S(%d,%d,%d) maxg_upto_L=%d\n",z,zmax[z],zarg[z][0],zarg[z][1],zarg[z][2],run); }
  printf("hist:"); for(int g=0;g<4096;g++) if(hist[g]) printf(" %d:%lld",g,hist[g]); printf("\n");
}
