const fs=require('fs');let seed=95001;function rand(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n}
function* perms(a,l=0){if(l===a.length){yield a.slice();return}for(let i=l;i<a.length;i++){[a[i],a[l]]=[a[l],a[i]];yield*perms(a,l+1);[a[i],a[l]]=[a[l],a[i]]}}
function pattern(v){return v.map(x=>v.filter(y=>y<x).length).join('')}
function sc(v,p){let s=[],o=[],i=0,k=p.length;while(i<v.length||s.length){let bad=i<v.length&&s.length>=k-1&&pattern([v[i],...s.slice(-(k-1)).reverse()])===p;if(i<v.length&&!bad)s.push(v[i++]);else o.push(s.pop())}return o}
function avoids(v,p){let q=p.split('').reverse().join('');for(let i=0;i<=v.length-p.length;i++){let t=pattern(v.slice(i,i+p.length));if(t===p||t===q)return false}return true}
function lcs(a,b){let dp=new Int16Array(b.length+1);for(let x of a){let prev=0;for(let j=1;j<=b.length;j++){let old=dp[j];dp[j]=x===b[j-1]?prev+1:Math.max(dp[j],dp[j-1]);prev=old}}return dp[b.length]}
function score(w){let n=w.length,m=n/2,best=0;let ww=w.concat(w);for(let i=0;i<m;i++){let a=ww.slice(i,i+m),b=ww.slice(i+m,i+n).reverse().map(x=>1-x);best=Math.max(best,lcs(a,b))}return best}

for(let i of [6,7,8,9,10,12,15,18,20,24]){let n=6*i,w=[...Array(i).fill(0),...Array(i).fill(1),...Array.from({length:2*i},(_,j)=>j%2),...Array(i).fill(1),...Array(i).fill(0)],s=score(w),best=s,bw=w.slice(),tested=0;for(let step=0;step<1800;step++){let a=rand(n),b=rand(n);if(w[a]===w[b])continue;[w[a],w[b]]=[w[b],w[a]];let t=score(w);tested++;if(t<=s||rand(1000)<3)s=t;else [w[a],w[b]]=[w[b],w[a]];if(s<best){best=s;bw=w.slice()}}console.log(JSON.stringify({n,tested,min_max_lcs:best,target:n/3,word:bw.join(''),seed:'0^i1^i(01)^i1^i0^i'}))}
