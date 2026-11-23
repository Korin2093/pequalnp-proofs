#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <cstdio>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <cassert>
using Bits=std::array<uint64_t,2>;
struct BHash{ size_t operator()(Bits x)const{return x[0]*157823711ULL+x[1];}};
std::unordered_map<Bits,int,BHash> lookup;
std::vector<Bits> bits;
int get(Bits v){auto f=lookup.find(v);if(f!=lookup.end())return f->second;int id=bits.size();bits.push_back(v);lookup.emplace(v,id);return id;}
int target;int cv[128];
using State=std::array<int,10>;
struct Hash{size_t operator()(State const&s)const{size_t x=137;for(auto w:s)x=x*100003^unsigned(w);return x;}};
std::unordered_set<State,Hash> failed;
std::array<int,128> ord{};
bool compatible(std::vector<int>const& live){
  std::array<unsigned char,1024> labels{};
  for(unsigned k=0;k<128;k++){unsigned p=ord[k],m=0,i=0;for(auto v:live)m|=unsigned((bits[v][p/64]>>(p%64))&1)<<i++;unsigned char z=cv[p]+1;if(labels[m]&&labels[m]!=z){if(k>1)std::swap(ord[k],ord[k/2]);return false;}labels[m]=z;}
  return true;
}
struct Gate{int op,l,r,z;};
std::vector<Gate> trace;
bool solve(std::vector<int>const& live,int spare){
 if(std::find(live.begin(),live.end(),target)!=live.end())return true;
 if(spare<0 || (live.size()==1 && spare==0))return false;
 State state{};for(size_t i=0;i<live.size();i++)state[i]=live[i]+1;state[9]=spare;
 if(failed.count(state))return false;
 for(unsigned i=0;i<live.size();i++)for(unsigned j=i;j<live.size();j++){
   int a=live[i],b=live[j];bool unary=i==j;if(unary&&spare==0)continue;
   for(int op=unary?2:0;op<(unary?3:2);op++){
    Bits v{};for(int q=0;q<2;q++)v[q]=(op==0?bits[a][q]&bits[b][q]:op==1?bits[a][q]|bits[b][q]:~bits[a][q]);
    if(v==Bits{0,0}||v==Bits{~0ULL,~0ULL})continue;
    int z=get(v);if(std::find(live.begin(),live.end(),z)!=live.end())continue;
    for(int keep=0;keep<(unary?2:4);keep++){
     int cost=int(unary)+__builtin_popcount(unsigned(keep));if(cost>spare)continue;
     std::vector<int> nxt;
     for(unsigned ix=0;ix<live.size();ix++)if((ix!=i||(keep&1))&&(unary||ix!=j||(keep&2)))nxt.push_back(live[ix]);
     nxt.insert(std::lower_bound(nxt.begin(),nxt.end(),z),z);
     if(!unary && keep!=3 && !compatible(nxt))continue;
     trace.push_back({op,a,b,z});if(solve(nxt,spare-cost))return true;trace.pop_back();
    }
   }
 }
 failed.insert(state);return false;
}
int main(int argc,char**argv){
 int maxk=argc>1?atoi(argv[1]):4;
 const std::pair<int,int> edges[]={{0,1},{0,2},{2,1},{0,3},{3,4},{4,5},{5,6},{6,1}};
 std::vector<int> in;Bits f{};
 for(int x=0;x<128;x++){ord[x]=x;for(auto [u,v]:edges)cv[x]|=(x>>u)&(x>>v)&1;if(cv[x])f[x/64]|=1ULL<<(x%64);}
 for(int i=0;i<7;i++){Bits v{};for(int x=0;x<128;x++)if(x>>i&1)v[x/64]|=1ULL<<(x%64);in.push_back(get(v));}
 target=get(f);
 for(int k=0;k<=maxk;k++){bool yes=solve(in,k);printf("at most %d gates: %d, cumulative states %zu, signals %zu\n",6+k,yes,failed.size(),bits.size());fflush(stdout);if(yes){for(auto g:trace)printf("op %d, signals %d and %d -> %d\n",g.op,g.l,g.r,g.z);return 0;}}
}
