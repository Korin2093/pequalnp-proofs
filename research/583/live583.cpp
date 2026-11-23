// Exhaustive monotone circuit size search on the once-subdivided K4.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <unordered_set>
#include <vector>

using Word = uint32_t;
constexpr unsigned n = 10;
constexpr unsigned points = 12;
constexpr Word target = (1u << points) - 1;
using Frontier = std::vector<Word>;

struct Key {
  Frontier signals;
  unsigned budget;
  bool operator==(const Key& rhs) const {
    return signals == rhs.signals && budget == rhs.budget;
  }
};
struct Hash {
  size_t operator()(const Key& k) const {
    size_t h = 1099511628211ULL * (k.budget + 1);
    for (Word x : k.signals) h = (h ^ x) * 1099511628211ULL;
    return h;
  }
};

struct Gate { bool conjunction; Word first, second, value; };
std::unordered_set<Key,Hash> impossible;
std::vector<Gate> solution;
uint64_t states=0;

// For each positive point collect the negative points separated by a live
// wire; downstream monotone gates can never create a separator from nothing.
bool covers(const Frontier& live) {
  std::array<Word,points> seen{};
  for (auto s : live) {
    Word neg_false = target ^ (s >> points);
    Word pos_true = s & target;
    while (pos_true) {
      const unsigned bit = __builtin_ctz(pos_true);
      seen[bit] |= neg_false;
      pos_true &= pos_true-1;
    }
  }
  return std::all_of(seen.begin(),seen.end(),[](Word x){return x==target;});
}

bool feasible(const Frontier& live, unsigned budget) {
  if (live.size()==1) return live[0]==target;
  Key key{live,budget};
  if (impossible.count(key)) return false;
  ++states;
  for (size_t i=0; i<live.size(); ++i) for (size_t j=0;j<i;++j) {
    const Word x=live[i], y=live[j];
    for (bool is_and: {false,true}) {
      Word z=is_and?(x&y):(x|y);
      if (std::find(live.begin(),live.end(),z)!=live.end()) continue;
      if (!(z&target) || (z>>points)==target) continue;
      for (unsigned retain=0;retain<4;++retain) {
        const unsigned extra=(retain&1)+(retain>>1);
        if (extra>budget) continue;
        Frontier next;
        for(size_t k=0;k<live.size();++k){
          if(k==i && !(retain&1))continue;
          if(k==j && !(retain&2))continue;
          next.push_back(live[k]);
        }
        next.insert(std::lower_bound(next.begin(),next.end(),z), z);
        if (!covers(next)) continue;
        if (feasible(next,budget-extra)) {
          solution.push_back({is_and,x,y,z});
          return true;
        }
      }
    }
  }
  impossible.insert(std::move(key));
  return false;
}

int main(){
  unsigned idx=4;
  std::vector<Word> edges,nonedges;
  for(unsigned a=0;a<4;++a)for(unsigned b=a+1;b<4;++b,++idx){
    edges.push_back((1u<<a)|(1u<<idx));edges.push_back((1u<<b)|(1u<<idx));
  }
  auto F=[&](Word w){return std::any_of(edges.begin(),edges.end(),[=](Word e){return (e&w)==e;});};
  for(Word w=0;w<(1u<<n);++w)if(!F(w)){
    bool maximal=true;
    for(unsigned i=0;i<n;++i)if(!(w&(1u<<i))&&!F(w|(1u<<i)))maximal=false;
    if(maximal)nonedges.push_back(w);
  }
  if(edges.size()!=points||nonedges.size()!=points)return 2;
  std::vector<Word> patterns=edges;
  patterns.insert(patterns.end(),nonedges.begin(),nonedges.end());
  Frontier initial;
  for(unsigned i=0;i<n;++i){
    Word values=0;
    for(unsigned t=0;t<patterns.size();++t) values|=((patterns[t]>>i)&1u)<<t;
    initial.push_back(values);
  }
  std::sort(initial.begin(),initial.end());
  for(unsigned budget=0;budget<=5;++budget){
    bool possible=feasible(initial,budget);
    std::cout << "bound " << n-1+budget << " feasible " << possible << " cumulative states " << states << '\n' << std::flush;
    if(possible){
      std::reverse(solution.begin(),solution.end());
      for(auto [op,a,b,z]:solution)std::cout<<(op?"AND":"OR")<<"("<<a<<","<<b<<")="<<z<<'\n';
      return 0;
    }
  }
}
