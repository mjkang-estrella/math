extern int puts(const char*); extern int printf(const char*,...);extern int fflush(void*);extern void*stdout;extern double exp(double);extern int atoi(const char*);
unsigned long long st=106364527;unsigned rnd(){st^=st<<13;st^=st>>7;st^=st<<17;return st;}
int a[2][100],corr[51];int energy(){int e=0;for(int s=1;s<=50;s++)e+=corr[s]*corr[s];return e;}
void flip(int z,int i){for(int s=1;s<=50;s++)corr[s]-=2*a[z][i]*(a[z][(i+s)%100]+a[z][(i+100-s)%100]);a[z][i]*=-1;}
int main(int argc,char**argv){int restarts=argc>1?atoi(argv[1]):100,steps=argc>2?atoi(argv[2]):100000,best=999999;for(int r=0;r<restarts;r++){// compression ([6,4],[12,-2]); row sums10,10; alternating2,14
int target[2][2]={{6,4},{12,-2}};
for(int z=0;z<2;z++)for(int p=0;p<2;p++){int plus=(50+target[z][p])/2;for(int j=0;j<50;j++)a[z][2*j+p]=j<plus?1:-1;for(int j=49;j>0;j--){int t=rnd()%(j+1),v=a[z][2*j+p];a[z][2*j+p]=a[z][2*t+p];a[z][2*t+p]=v;}}
for(int s=1;s<=50;s++){corr[s]=0;for(int z=0;z<2;z++)for(int i=0;i<100;i++)corr[s]+=a[z][i]*a[z][(i+s)%100];}
int e=energy();for(int k=0;k<steps;k++){int z=rnd()%2,p=rnd()%2,i=2*(rnd()%50)+p,j=2*(rnd()%50)+p;if(a[z][i]==a[z][j])continue;flip(z,i);flip(z,j);int ne=energy();double T=10.+250.*(steps-k)/steps;if(ne<=e||(double)rnd()/4294967296.<exp((e-ne)/T))e=ne;else{flip(z,j);flip(z,i);}if(e<best){best=e;printf("best %d restart %d step %d\n",best,r,k);fflush(stdout);}if(e==0){printf("FOUND\n");for(int z=0;z<2;z++){for(int i=0;i<100;i++)printf("%d,",a[z][i]);puts("");}return 0;}}
}printf("DONE restarts %d steps %d best %d\n",restarts,steps,best);}
