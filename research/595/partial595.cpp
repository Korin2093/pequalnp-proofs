// Seven-vertex theta-graph search, with one gate per AND and free wire complements.
// Build with c++ -O3 -std=c++17 partial595.cpp -o partial595, then run ./partial595.
#include <array>
#include <cstdint>
#include <cstdio>
#include <unordered_set>
#include <utility>
#include <vector>

using Rows = std::vector<uint16_t>;  // A row is (wire_pattern << 1) | target.

struct State {
    Rows rows;
    int width;
    int budget;

    bool operator==(const State &other) const {
        return width == other.width && budget == other.budget && rows == other.rows;
    }
};

struct StateHash {
    std::size_t operator()(const State &state) const {
        std::size_t hash = 13 * state.width + state.budget;
        for (auto row : state.rows) hash = (hash ^ row) * 1099511628211ULL;
        return hash;
    }
};

std::unordered_set<State, StateHash> losing;
uint64_t compatibleTransitions = 0;

int deleteBit(int value, int index) {
    const int lowerMask = (1 << index) - 1;
    return (value & lowerMask) | ((value >> (index + 1)) << index);
}

bool targetIsWire(int width, const Rows &rows) {
    int equal = (1 << width) - 1;
    int inverse = equal;
    for (auto row : rows) {
        int inputs = row >> 1;
        bool target = row & 1;
        equal &= target ? inputs : ~inputs;
        inverse &= target ? ~inputs : inputs;
    }
    return equal || inverse;
}

struct ProjectedRow {
    uint16_t surviving;
    uint16_t pair;
    uint16_t target;
};

bool realizable(int width, int budget, const Rows &rows) {
    if (width > budget + 1) return false;
    if (targetIsWire(width, rows)) return true;
    if (width < 2 || budget == 0) return false;

    State state{rows, width, budget};
    if (losing.count(state)) return false;
    for (int left = 0; left < width; ++left) {
        for (int right = left + 1; right < width; ++right) {
            for (int retain = 0; retain < 4; ++retain) {
                const bool keepLeft = retain & 1;
                const bool keepRight = retain & 2;
                const int nextWidth = width - 1 + keepLeft + keepRight;
                if (nextWidth > budget) continue;

                std::array<ProjectedRow, 128> projection;
                for (std::size_t i = 0; i < rows.size(); ++i) {
                    int inputs = rows[i] >> 1;
                    int pair = ((inputs >> left) & 1) | (((inputs >> right) & 1) << 1);
                    int surviving = inputs;
                    if (!keepRight) surviving = deleteBit(surviving, right);
                    if (!keepLeft) surviving = deleteBit(surviving, left);
                    projection[i] = {uint16_t(surviving), uint16_t(pair), uint16_t(rows[i] & 1)};
                }

                // The four choices are all conjunctions of signed operands.
                for (int trueOn = 0; trueOn < 4; ++trueOn) {
                    // The initial excess is 10 - (7 - 1) = 4. Each additional
                    // live wire costs two units of excess, so width <= 9.
                    std::array<uint8_t, 512> labels{};
                    bool conflict = false;
                    int seenOutputs = 0;
                    int equal = (1 << width) - 1;
                    int inverse = equal;
                    for (std::size_t i = 0; i < rows.size(); ++i) {
                        auto entry = projection[i];
                        int gate = entry.pair == trueOn;
                        int nextInputs = entry.surviving | (gate << (nextWidth - 1));
                        auto &label = labels[nextInputs];
                        if (label && label != entry.target + 1) {
                            conflict = true;
                            break;
                        }
                        label = entry.target + 1;
                        seenOutputs |= 1 << gate;
                        int inputs = rows[i] >> 1;
                        equal &= gate ? inputs : ~inputs;
                        inverse &= gate ? ~inputs : inputs;
                    }
                    if (conflict || seenOutputs != 3 || equal || inverse) continue;

                    Rows nextRows;
                    for (int p = 0; p < (1 << nextWidth); ++p) {
                        if (labels[p]) nextRows.push_back(2 * p + labels[p] - 1);
                    }
                    ++compatibleTransitions;
                    if (realizable(nextWidth, budget - 1, nextRows)) return true;
                }
            }
        }
    }
    losing.insert(std::move(state));
    return false;
}

int main() {
    const int edges[][2] = {{0, 1}, {0, 2}, {2, 1}, {0, 3}, {3, 4}, {4, 5}, {5, 6}, {6, 1}};
    Rows rows;
    for (int inputs = 0; inputs < 128; ++inputs) {
        int target = 0;
        for (auto &edge : edges) target |= (inputs >> edge[0]) & (inputs >> edge[1]) & 1;
        rows.push_back(2 * inputs + target);
    }
    for (int budget = 6; budget <= 10; ++budget) {
        bool found = realizable(7, budget, rows);
        std::printf("budget %d result %d cumulative losing states %zu cumulative compatible transitions %llu\n",
                    budget, int(found), losing.size(), static_cast<unsigned long long>(compatibleTransitions));
        std::fflush(stdout);
        if (found) return 1;
    }
}
