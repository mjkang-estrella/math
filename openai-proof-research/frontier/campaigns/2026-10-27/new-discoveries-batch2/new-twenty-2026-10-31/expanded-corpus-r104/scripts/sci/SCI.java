import java.util.*;
// Random maximal graphs with maximum edge weight W(G) <= 7; test whether the strong chromatic index exceeds 13.
public class SCI {
  static int n; static boolean[][] adj; static int[] deg;
  static boolean ok(int u,int v){ if(adj[u][v]||u==v) return false; if(deg[u]+1+deg[v]+1>7) return false;
    for(int w=0;w<n;w++){ if(adj[u][w] && deg[u]+1+deg[w]>7) return false; if(adj[v][w] && deg[v]+1+deg[w]>7) return false; } return true; }
  static int[][] edges; static boolean[][] conf; static int m;
  static boolean color(int[] col,int k,int idx,int[] order){ if(idx==m) return true; int e=order[idx];
    boolean[] used=new boolean[k]; for(int f=0;f<m;f++) if(conf[e][f]&&col[f]>=0) used[col[f]]=true;
    int maxc=0; for(int f=0;f<m;f++) maxc=Math.max(maxc,col[f]+1);
    for(int c=0;c<Math.min(k,maxc+1);c++) if(!used[c]){ col[e]=c; if(color(col,k,idx+1,order)) return true; col[e]=-1; }
    return false; }
  public static void main(String[] a){
    Random R=new Random(Long.parseLong(a[0])); long t0=System.currentTimeMillis(); long tried=0; int best=0; int[] hist=new int[40];
    while(System.currentTimeMillis()-t0<Long.parseLong(a[1])*1000){
      n=6+R.nextInt(12); adj=new boolean[n][n]; deg=new int[n];
      List<int[]> pairs=new ArrayList<>(); for(int u=0;u<n;u++)for(int v=u+1;v<n;v++) pairs.add(new int[]{u,v}); Collections.shuffle(pairs,R);
      for(int[] p:pairs) if(ok(p[0],p[1])){adj[p[0]][p[1]]=adj[p[1]][p[0]]=true;deg[p[0]]++;deg[p[1]]++;}
      List<int[]> E=new ArrayList<>(); for(int u=0;u<n;u++)for(int v=u+1;v<n;v++) if(adj[u][v]) E.add(new int[]{u,v});
      m=E.size(); if(m<14){tried++;continue;} edges=E.toArray(new int[0][]); conf=new boolean[m][m];
      for(int i=0;i<m;i++)for(int j=0;j<m;j++){ if(i==j) continue; int[] e=edges[i],f=edges[j];
        boolean c= e[0]==f[0]||e[0]==f[1]||e[1]==f[0]||e[1]==f[1]|| adj[e[0]][f[0]]||adj[e[0]][f[1]]||adj[e[1]][f[0]]||adj[e[1]][f[1]]; conf[i][j]=c; }
      // order by conflict degree
      Integer[] ord=new Integer[m]; for(int i=0;i<m;i++) ord[i]=i; final boolean[][] C=conf;
      Arrays.sort(ord,(x,y)->{int dx=0,dy=0; for(int z=0;z<m;z++){ if(C[x][z])dx++; if(C[y][z])dy++;} return dy-dx;});
      int[] order=new int[m]; for(int i=0;i<m;i++) order[i]=ord[i];
      int[] col=new int[m]; Arrays.fill(col,-1);
      boolean c13=color(col,13,0,order);
      tried++;
      if(!c13){ System.out.println("CANDIDATE n="+n+" m="+m+" edges="+Arrays.deepToString(edges)); }
      // record chi_s' lower info cheaply: smallest k found greedily
      int k=13; while(k>1){ int[] c2=new int[m]; Arrays.fill(c2,-1); if(color(c2,k-1,0,order)) k--; else break; }
      hist[Math.min(k,39)]++; best=Math.max(best,k);
    }
    System.out.println("tried="+tried+" max_chi_s_found="+best+" hist="+Arrays.toString(hist));
  }
}
