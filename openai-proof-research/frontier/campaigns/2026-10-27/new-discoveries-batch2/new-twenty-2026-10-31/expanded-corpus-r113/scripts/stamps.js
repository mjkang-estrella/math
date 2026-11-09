const N=Number(process.argv[2]||15),cnt=Array.from({length:N+1},(_,n)=>new Float64Array(2**Math.max(0,n-1))),p=[0];let visited=0;
function dfs(mask){let n=p.length;cnt[n][mask]++;if(n===N)return;let pos=new Int8Array(n);for(let j=0;j<n;j++)pos[p[j]]=j;
for(let at=0;at<=n;at++){let a=pos[n-1]+(pos[n-1]>=at),b=at;if(a>b)[a,b]=[b,a];let ok=true;
for(let i=(n-1)%2;i+1<n;i+=2){let c=pos[i]+(pos[i]>=at),d=pos[i+1]+(pos[i+1]>=at);if(c>d)[c,d]=[d,c];if((a<c&&c<b&&b<d)||(c<a&&a<d&&d<b)){ok=false;break;}}
if(ok){let m=(pos[n-1]>=at)===((n-1)%2===0);p.splice(at,0,n);dfs(mask|(Number(m)<<(n-1)));p.splice(at,1);}}}
dfs(0);for(let n=2;n<=N;n++){let mx=0,total=0;for(let v of cnt[n]){total+=v;mx=Math.max(mx,v);}let winners=[],bad=[];for(let i=0;i<cnt[n].length;i++)if(cnt[n][i]===mx){let runs=[],r=1;for(let j=1;j<n-1;j++){if(((i>>j)&1)===((i>>(j-1))&1))r++;else{runs.push(r);r=1;}}runs.push(r);winners.push(runs);if(runs.some((v,j)=>v>3||(j&&v===3&&runs[j-1]===3)))bad.push(runs);}
console.log(JSON.stringify({n,total,max:mx,winners,violations:n>=8?bad:[]}));}
