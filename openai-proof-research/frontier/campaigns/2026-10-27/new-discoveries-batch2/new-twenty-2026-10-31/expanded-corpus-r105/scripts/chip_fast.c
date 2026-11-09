extern void *calloc(unsigned long,unsigned long);extern void free(void*);extern int printf(const char*,...);extern int atoi(const char*);
int main(int argc,char**argv){int n=atoi(argv[1]);unsigned long long *a=calloc(200000,8),*b=calloc(200000,8);a[0]=1ULL<<n;int len=1,mx=1,t=1;long rows=0;
while(len){rows++;int z=len+1;b[0]=a[0]/2;for(int i=1;i<len;i++)b[i]=a[i-1]/2+a[i]/2;b[len]=a[len-1]/2;int off=0;while(off<z && b[off]==0)off++;if(off==z)break;if(off){z-=2*off;for(int i=0;i<z;i++)b[i]=b[i+off];}if(z<=0)break;t=z==len-1?t+1:1;len=z;if(len>mx)mx=len;unsigned long long *c=a;a=b;b=c;}
printf("n %d rows %ld max_width %d bottom_triangle_rows %d holds %d\n",n,rows,mx,t,t==mx-1);free(a);free(b);return 0;}
