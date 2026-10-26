/* The workspace has Lean's C compiler but no system development headers.
These are the standard C-library declarations used by this standalone check. */
typedef unsigned long long uint64_t;
extern int printf(const char *, ...);
extern int fflush(void *);

/* Independent literal RREF enumeration over F_3. No run classification. */
static unsigned char allowed[27][27][27];
static int vectors[27][3], columns[20], options[20][8], lengths[20], dimension;

static uint64_t search(int position) {
  if(position==dimension)return 1;
  uint64_t count=0;
  for(int z=0;z<lengths[position];++z) {
    int v=options[position][z],good=1;
    for(int a=0;a<position&&good;++a)
      for(int b=a+1;b<position;++b)
        if(!allowed[columns[a]][columns[b]][v]){good=0;break;}
    if(good){columns[position]=v;count+=search(position+1);}
  }
  return count;
}

int main(void) {
  for(int i=0;i<27;++i){vectors[i][0]=i%3;vectors[i][1]=(i/3)%3;vectors[i][2]=(i/9)%3;}
  for(int i=0;i<27;++i)for(int j=0;j<27;++j)for(int k=0;k<27;++k) {
    int *a=vectors[i],*b=vectors[j],*c=vectors[k];
    int d=a[0]*(b[1]*c[2]-b[2]*c[1])-b[0]*(a[1]*c[2]-a[2]*c[1])+c[0]*(a[1]*b[2]-a[2]*b[1]);
    allowed[i][j][k]=((d%3+3)%3)!=2;
  }
  for(dimension=3;dimension<=12;++dimension) {
    uint64_t total=0;
    for(int a=0;a<dimension;++a)for(int b=a+1;b<dimension;++b)for(int c=b+1;c<dimension;++c) {
      int pivots[3]={a,b,c};
      for(int j=0;j<dimension;++j) {
        lengths[j]=0;int pivot=-1,seen=0;
        for(int r=0;r<3;++r){if(pivots[r]==j)pivot=r;if(pivots[r]<j)++seen;}
        if(pivot>=0){options[j][lengths[j]++]=(pivot==0?1:(pivot==1?3:9));continue;}
        for(int mask=0;mask<(1<<seen);++mask) {
          int v[3]={0,0,0};
          for(int r=0;r<seen;++r)if(mask>>r&1)v[r]=((r+seen-1)%2==0)?1:2;
          options[j][lengths[j]++]=v[0]+3*v[1]+9*v[2];
        }
      }
      total+=search(0);
    }
    printf("%d %llu\n",dimension,(unsigned long long)total);fflush((void *)0);
  }
  return 0;
}
