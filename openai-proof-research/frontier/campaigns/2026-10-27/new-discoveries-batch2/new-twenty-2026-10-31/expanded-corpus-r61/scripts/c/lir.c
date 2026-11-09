/* Diagnostic: does every digraph (n<=4, 2-cycles allowed) and every oriented graph (n=5) admit an
   arc 2-colouring in which each colour class is weakly locally irregular (adjacent endpoints of every
   arc have different (outdeg, indeg) pairs inside that class)? */
int printf(const char*, ...);
static int n, m, au[20], av[20];
static int ok_class(unsigned sel){
  int out[5]={0},in[5]={0};
  for(int e=0;e<m;e++) if(sel>>e&1){out[au[e]]++;in[av[e]]++;}
  for(int e=0;e<m;e++) if(sel>>e&1){int u=au[e],v=av[e]; if(out[u]==out[v]&&in[u]==in[v]) return 0;}
  return 1;
}
static int colourable(void){
  unsigned full=(m==32)?0xffffffffu:((1u<<m)-1);
  for(unsigned c=0;c<=full;c++){ if(ok_class(c)&&ok_class(full&~c)) return 1; if(c==full)break; }
  return 0;
}
int main(void){
  long long total=0,bad=0;
  for(n=1;n<=4;n++){
    int pu[12],pv[12],np=0; for(int a=0;a<n;a++)for(int b=0;b<n;b++) if(a!=b){pu[np]=a;pv[np]=b;np++;}
    long long t=0,b=0;
    for(unsigned mask=0;mask<(1u<<np);mask++){ m=0; for(int k=0;k<np;k++) if(mask>>k&1){au[m]=pu[k];av[m]=pv[k];m++;}
      t++; if(!colourable()){ b++; if(b<=5) printf("FAIL digraph n=%d mask=%u\n",n,mask);} }
    printf("digraphs n=%d labeled=%lld non2colourable=%lld\n",n,t,b); total+=t; bad+=b;
  }
  n=5; { int pu[10],pv[10],np=0; for(int a=0;a<5;a++)for(int b=a+1;b<5;b++){pu[np]=a;pv[np]=b;np++;}
    long long t=0,b=0; int pow3=59049;
    for(int code=0;code<pow3;code++){ int c=code; m=0;
      for(int k=0;k<np;k++){int d=c%3;c/=3; if(d==1){au[m]=pu[k];av[m]=pv[k];m++;} else if(d==2){au[m]=pv[k];av[m]=pu[k];m++;}}
      t++; if(!colourable()){b++; if(b<=5) printf("FAIL oriented n=5 code=%d\n",code);} }
    printf("oriented n=5 labeled=%lld non2colourable=%lld\n",t,b); total+=t; bad+=b; }
  printf("TOTAL %lld BAD %lld\n",total,bad); return 0;
}
