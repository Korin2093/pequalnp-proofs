#include <algorithm>
#include <array>
#include <bitset>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <map>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {
using Signature = std::uint16_t;
using TruthTable = std::bitset<256>;
using Coverage = std::bitset<56>;
using State = std::vector<Signature>;
constexpr int inputs = 8;
constexpr int gates = 11;
constexpr int output = 18;
constexpr int assignments = 256;
constexpr std::array<std::pair<int, int>, 8> edges{{
    {0,1}, {1,2}, {2,3}, {3,4}, {4,5}, {0,5}, {0,6}, {1,7}
}};

void require(bool condition, const std::string& explanation) {
    if (!condition) throw std::logic_error(explanation);
}

struct Gate {
    bool isAnd;
    int left, right;
};

struct Move {
    int first, second;
    bool keepFirst, keepSecond;
    bool isAnd;
    Signature result;
};

struct Search {
    std::vector<int> positive, negative;
    TruthTable target;
    std::array<TruthTable, inputs> raw;
    std::vector<Coverage> coverage;
    Signature goal = 0;
    std::map<std::pair<State, int>, bool> memo;
    std::array<Gate, gates> trace{};
    std::uint64_t successfulOrders = 0;
    std::array<std::array<std::set<std::string>, 2>, 2> classes;
    unsigned maxShared = 0;
    bool found = false;
    std::ostream* records;

    explicit Search(std::ostream* table = nullptr) : records(table) {
        if (records) *records << "output_expression\tgates_in_order\tlift_gate_index\tp_wire\th_wire\tbefore_pairs\tafter_pairs\n";
        for (int x = 0; x < assignments; ++x) {
            for (int i = 0; i < inputs; ++i) raw[i][x] = ((x >> i) & 1) == 1;
            for (auto [a,b] : edges) if (raw[a][x] && raw[b][x]) target[x] = true;
        }
        for (int x = 0; x < assignments; ++x) {
            bool extremal = true;
            for (int i = 0; i < inputs; ++i) {
                const int other = x ^ (1 << i);
                if (target[x] && raw[i][x] && target[other]) extremal = false;
                if (!target[x] && !raw[i][x] && !target[other]) extremal = false;
            }
            if (extremal) (target[x] ? positive : negative).push_back(x);
        }
        require(positive.size() == 8 && negative.size() == 7, "unexpected boundary");
        for (int i = 0; i < inputs; ++i) {
            bool essential = false;
            for (int x = 0; x < assignments; ++x)
                if (target[x] != target[x ^ (1 << i)]) essential = true;
            require(essential, "unused input in target function");
        }
        goal = signature(target);
        coverage.resize(1u << (positive.size() + negative.size()));
        for (unsigned s = 0; s < coverage.size(); ++s) {
            for (unsigned p = 0; p < positive.size(); ++p) {
                for (unsigned n = 0; n < negative.size(); ++n) {
                    const bool pTrue = (s & (1u << p)) != 0;
                    const bool nFalse = (s & (1u << (positive.size()+n))) == 0;
                    coverage[s][p*negative.size()+n] = pTrue && nFalse;
                }
            }
        }
    }

    Signature signature(const TruthTable& t) const {
        Signature s = 0;
        unsigned bit = 0;
        for (int x : positive) { if (t[x]) s |= (1u << bit); ++bit; }
        for (int x : negative) { if (t[x]) s |= (1u << bit); ++bit; }
        return s;
    }

    // Visit every valid choice of two different live wire slots, operator and retention.
    // Equal-valued but physically distinct wires remain separate slots.
    template <class Visitor>
    void moves(const State& state, int budget, Visitor visit) const {
        const int count = static_cast<int>(state.size());
        for (int a = 0; a < count; ++a) for (int b = a+1; b < count; ++b) {
            Coverage other;
            for (int i = 0; i < count; ++i)
                if (i != a && i != b) other |= coverage[state[i]];
            for (bool isAnd : {false,true}) {
                const Signature s = isAnd ? (state[a] & state[b]) : (state[a] | state[b]);
                for (bool keepA : {false,true}) for (bool keepB : {false,true}) {
                    const int remaining = budget - int(keepA) - int(keepB);
                    if (remaining < 0) continue;
                    Coverage possible = other | coverage[s];
                    if (keepA) possible |= coverage[state[a]];
                    if (keepB) possible |= coverage[state[b]];
                    if (!possible.all()) continue;
                    State next;
                    for (int i = 0; i < count; ++i)
                        if ((i != a || keepA) && (i != b || keepB)) next.push_back(state[i]);
                    auto pos = std::lower_bound(next.begin(), next.end(), s);
                    const int inserted = static_cast<int>(pos-next.begin());
                    next.insert(pos, s);
                    if (visit(next, remaining, Move{a,b,keepA,keepB,isAnd,s}, inserted)) return;
                }
            }
        }
    }

    bool canFinish(const State& state, int remaining) {
        if (state.size() == 1) return state.front() == goal;
        const auto key = std::make_pair(state, remaining);
        auto hit = memo.find(key);
        if (hit != memo.end()) return hit->second;
        bool result = false;
        moves(state, remaining, [&](const State& next, int left, const Move&, int) {
            result = canFinish(next,left);
            return result;
        });
        memo.emplace(key, result);
        return result;
    }

    struct Evaluation {
        std::array<TruthTable, inputs+gates+1> wire;
        int nestedPairs = 0;
    };

    template <class Circuit>
    Evaluation evaluate(const Circuit& circuit) const {
        Evaluation e;
        std::copy(raw.begin(),raw.end(),e.wire.begin());
        std::array<std::bitset<gates+1>, inputs+gates+1> ancestors{};
        int w = inputs;
        for (const Gate& g : circuit) {
            require(g.left >= 0 && g.left < w && g.right >= 0 && g.right < w, "invalid wire");
            auto below = ancestors[g.left] | ancestors[g.right];
            if (g.isAnd) {
                e.wire[w] = e.wire[g.left] & e.wire[g.right];
                e.nestedPairs += static_cast<int>(below.count());
                below.set(w-inputs);
            } else {
                e.wire[w] = e.wire[g.left] | e.wire[g.right];
            }
            ancestors[w++] = below;
        }
        return e;
    }

    // The key preserves labeled raw inputs and unordered AND/OR operands. Every emitted gate
    // must lie in the output cone. Equal expanded subtrees from two gates would contradict
    // minimum size. We explicitly test both facts before using this key to group circuits.
    std::pair<std::string,unsigned> keyAndSharing() const {
        std::array<std::string, inputs+gates> name;
        std::array<int, inputs+gates> reads{};
        std::set<std::string> distinct;
        for (int i = 0; i < inputs; ++i) name[i] = std::to_string(i);
        int w = inputs;
        for (const Gate& g : trace) {
            ++reads[g.left];
            ++reads[g.right];
            auto [l,r] = std::minmax(name[g.left],name[g.right]);
            name[w] = "(" + l + (g.isAnd ? "&" : "|") + r + ")";
            require(distinct.insert(name[w]).second,"redundant equal subtrees");
            ++w;
        }
        unsigned shared = 0;
        for (int i = 0; i < output; ++i) {
            require(reads[i] > 0,"dead wire in completed circuit");
            if (i >= inputs && reads[i] > 1) ++shared;
        }
        return {name.back(),shared};
    }

    void checkCircuit() {
        ++successfulOrders;
        const auto [key, shared] = keyAndSharing();
        maxShared = std::max(maxShared,shared);
        const Evaluation e = evaluate(trace);
        require(e.wire[output] == target,"wrong truth table on the 256 assignments");
        const bool nested = e.nestedPairs > 0;
        if (!classes[nested][shared != 0].insert(key).second || !nested) return;
        for (int j = 0; j+1 < gates; ++j) {
            const Gate& g = trace[j];
            if (g.isAnd) continue;
            for (bool swap : {false,true}) {
                const int h = swap ? g.left : g.right;
                const int p = swap ? g.right : g.left;
                if ((e.wire[h] & ~target).any()) continue;
                std::vector<Gate> changed(trace.begin(),trace.end());
                changed[j] = {false,p,p};
                changed.push_back({false,output,h});
                const Evaluation f = evaluate(changed);
                if (f.wire[output+1] == target && f.nestedPairs < e.nestedPairs) {
                    if (records) {
                        *records << key << '\t';
                        for (int i = 0; i < gates; ++i) {
                            if (i) *records << ' ';
                            const Gate& v = trace[i];
                            *records << (v.isAnd ? "and" : "or") << '('
                                     << v.left << ',' << v.right << ')';
                        }
                        *records << '\t' << j << '\t' << p << '\t' << h << '\t'
                                 << e.nestedPairs << '\t' << f.nestedPairs << '\n';
                    }
                    return;
                }
            }
        }
        found = true;
        std::cout << "Unflattenable circuit: " << key << '\n';
    }

    void enumerate(const State& state, int left, const std::vector<int>& ids, int depth) {
        if (state.size() == 1) {
            require(state[0] == goal && depth == gates, "unexpected successful size");
            checkCircuit();
            return;
        }
        moves(state,left,[&](const State& next, int remaining, const Move& move, int at) {
            if (!canFinish(next,remaining)) return false;
            require(depth < gates, "gate budget exceeded");
            const int a = move.first, b = move.second;
            trace[depth] = {move.isAnd,ids[a],ids[b]};
            std::vector<int> nextIds;
            for (int i = 0; i < int(ids.size()); ++i)
                if ((i != a || move.keepFirst) && (i != b || move.keepSecond))
                    nextIds.push_back(ids[i]);
            nextIds.insert(nextIds.begin()+at,inputs+depth);
            enumerate(next,remaining,nextIds,depth+1);
            return false;
        });
    }

    void run() {
        std::vector<std::pair<Signature,int>> sorted;
        for (int i = 0; i < inputs; ++i) sorted.emplace_back(signature(raw[i]),i);
        std::sort(sorted.begin(),sorted.end());
        State start;
        std::vector<int> ids;
        for (auto [s,i] : sorted) { start.push_back(s); ids.push_back(i); }
        require(!canFinish(start,3),"a circuit with at most 10 gates was found");
        std::cout << "No circuit of size at most 10.\n";
        require(canFinish(start,4),"no 11-gate circuits found");
        enumerate(start,4,ids,0);
        std::cout << "Successful topological orders (commutative inputs): " << successfulOrders
                  << "\nFlat formulas: " << classes[0][0].size()
                  << "\nFlat circuits sharing an internal gate: " << classes[0][1].size()
                  << "\nNested formulas: " << classes[1][0].size()
                  << "\nNested circuits sharing an internal gate: " << classes[1][1].size()
                  << "\nMaximum number of shared internal gates: " << maxShared
                  << "\nUnflattenable circuit found: " << (found ? "yes" : "no") << '\n';
    }
};
}

int main(int argc, char** argv) {
    if (argc > 2) {
        std::cerr << "Usage: check523 [lift-results.tsv]\n";
        return EXIT_FAILURE;
    }
    std::ofstream table;
    if (argc == 2) {
        table.open(argv[1]);
        if (!table) {
            std::cerr << "Cannot open output table.\n";
            return EXIT_FAILURE;
        }
    }
    Search search(argc == 2 ? &table : nullptr);
    search.run();
    return search.found ? EXIT_FAILURE : EXIT_SUCCESS;
}
