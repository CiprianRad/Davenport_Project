// Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
// SPDX-License-Identifier: Apache-2.0
// Read lines of N codes (optionally prefixed by a tag letter), compute canonical form = lex-min sorted image
// over all ordered support bases (odd det) mapped to (e1,e2,e3). Print number of distinct canonical forms.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N;
static int dig(int x,int i){return (x>>(2*i))&3;}
static int enc(int a,int b,int c){return (a&3)|((b&3)<<2)|((c&3)<<4);}
static int det3(int r0,int r1,int r2){ int m[3][3]; int rs[3]={r0,r1,r2}; for(int i=0;i<3;i++)for(int j=0;j<3;j++)m[i][j]=dig(rs[i],j);
  int d = m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1]) - m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0]) + m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]);
  return ((d%4)+4)%4; }
// inverse of matrix with rows r0,r1,r2 (row vectors: v -> v*M). Want phi with phi(r_i)=e_i: phi(v) = v * M^{-1}.
static void inv3(int r0,int r1,int r2,int inv[3][3]){ int m[3][3]; int rs[3]={r0,r1,r2}; for(int i=0;i<3;i++)for(int j=0;j<3;j++)m[i][j]=dig(rs[i],j);
  int d=det3(r0,r1,r2); int di = d==1?1:3; // inverse of odd unit mod 4
  int adj[3][3];
  adj[0][0]= m[1][1]*m[2][2]-m[1][2]*m[2][1]; adj[0][1]=-(m[0][1]*m[2][2]-m[0][2]*m[2][1]); adj[0][2]= m[0][1]*m[1][2]-m[0][2]*m[1][1];
  adj[1][0]=-(m[1][0]*m[2][2]-m[1][2]*m[2][0]); adj[1][1]= m[0][0]*m[2][2]-m[0][2]*m[2][0]; adj[1][2]=-(m[0][0]*m[1][2]-m[0][2]*m[1][0]);
  adj[2][0]= m[1][0]*m[2][1]-m[1][1]*m[2][0]; adj[2][1]=-(m[0][0]*m[2][1]-m[0][1]*m[2][0]); adj[2][2]= m[0][0]*m[1][1]-m[0][1]*m[1][0];
  for(int i=0;i<3;i++)for(int j=0;j<3;j++){ inv[i][j]=(((adj[i][j]*di)%4)+4)%4; } }
static int apply(int v,int inv[3][3]){ int r[3]={0,0,0}; for(int j=0;j<3;j++){ int s=0; for(int i=0;i<3;i++) s+=dig(v,i)*inv[i][j]; r[j]=s&3;} return enc(r[0],r[1],r[2]); }
static int cmpint(const void*a,const void*b){return *(int*)a-*(int*)b;}
typedef struct { int c[24]; } Seq;
static int cmpseq(const void*a,const void*b){ return memcmp(a,b,sizeof(Seq)); }
int main(int argc,char**argv){
  N=atoi(argv[1]); FILE *f=fopen(argv[2],"r"); char tagfilter = (argc>3 && argv[3][0]!='-')? argv[3][0]:0;
  Seq *all=malloc(sizeof(Seq)*3000000); int n=0; char line[1000];
  while(fgets(line,sizeof line,f)){ char *p=line; char tag=0; if(line[0]>='A'&&line[0]<='Z'){tag=line[0]; p=line+2;} if(tagfilter && tag!=tagfilter) continue;
    int c[24]; for(int i=0;i<N;i++){ c[i]=strtol(p,&p,10);} 
    int sup[64],ns=0; int seen[64]={0}; for(int i=0;i<N;i++) if(!seen[c[i]]){seen[c[i]]=1; sup[ns++]=c[i];}
    Seq best; int have=0;
    for(int a=0;a<ns;a++)for(int b=0;b<ns;b++)for(int d=0;d<ns;d++){ if(a==b||a==d||b==d) continue; if(!(det3(sup[a],sup[b],sup[d])&1)) continue;
      int inv[3][3]; inv3(sup[a],sup[b],sup[d],inv); Seq s; memset(&s,0,sizeof s); for(int i=0;i<N;i++) s.c[i]=apply(c[i],inv); qsort(s.c,N,sizeof(int),cmpint);
      if(!have||memcmp(&s,&best,sizeof s)<0){best=s;have=1;} }
    if(!have){ fprintf(stderr,"no basis!\n"); continue; }
    all[n++]=best; }
  qsort(all,n,sizeof(Seq),cmpseq); int d=0; for(int i=0;i<n;i++) if(i==0||memcmp(&all[i],&all[i-1],sizeof(Seq))) d++;
  printf("read %d sequences, %d distinct orbits\n",n,d);
  if(argc>4){ FILE *o=fopen(argv[4],"w"); for(int i=0;i<n;i++) if(i==0||memcmp(&all[i],&all[i-1],sizeof(Seq))){ for(int j=0;j<N;j++) fprintf(o,"%d ",all[i].c[j]); fprintf(o,"\n"); } fclose(o);} 
}
