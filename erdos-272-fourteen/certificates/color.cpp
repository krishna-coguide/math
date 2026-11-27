// Untrusted witness generator: color by saturation degree, then try recolorings
// with a short tabu list. Only a coloring accepted by Lean is used.
#include <algorithm>
#include <bitset>
#include <numeric>
#include <random>
#include <vector>
using namespace std;
extern "C" int color_api(const int *vs, int n, int K, int iters, int seed,
                         unsigned char *out) {
  static bool ap[16384];
  static bool init = false;
  if (!init) {
    for (int i = 0; i < 14; i++)
      for (int d = 1; d <= 14; d++) {
        int p = 0;
        for (int j = i; j < 14; j += d) {
          p |= 1 << j;
          ap[p] = true;
        }
      }
    init = true;
  }
  vector<vector<int>> adj(n);
  vector<int> sat(n), rem(n), col(n, -1);
  vector<bitset<512>> used(n);
  for (int i = 0; i < n; i++)
    for (int j = 0; j < i; j++)
      if (ap[vs[i] & vs[j]]) {
        adj[i].push_back(j);
        adj[j].push_back(i);
        rem[i]++;
        rem[j]++;
      }
  mt19937 rng(seed);
  int nc = 0;
  for (int i = 0; i < n; i++) {
    int v = -1;
    for (int u = 0; u < n; u++)
      if (col[u] < 0 &&
          (v < 0 || sat[u] > sat[v] || (sat[u] == sat[v] && rem[u] > rem[v])))
        v = u;
    int c = 0;
    while (c < 512 && used[v][c])
      c++;
    if (c == 512)
      return 0;
    col[v] = c;
    nc = max(nc, c + 1);
    for (int u : adj[v])
      if (col[u] < 0) {
        if (!used[u][c]) {
          used[u].set(c);
          sat[u]++;
        }
        rem[u]--;
      }
  }
  if (nc <= K) {
    copy(col.begin(), col.end(), out);
    return nc;
  }
  if (iters == 0)
    return 0;
  vector<int> hits(n * K), tab(n * K);
  int cost = 0;
  for (int i = 0; i < n; i++)
    if (col[i] < K)
      for (int u : adj[i])
        hits[u * K + col[i]]++;
  for (int i = 0; i < n; i++)
    if (col[i] >= K) {
      auto r = hits.data() + i * K;
      int c = min_element(r, r + K) - r;
      col[i] = c;
      for (int u : adj[i])
        hits[u * K + c]++;
    }
  for (int i = 0; i < n; i++)
    cost += hits[i * K + col[i]];
  cost /= 2;
  int best = cost;
  vector<int> best_colors = col;
  for (int t = 1; t <= iters && cost; t++) {
    int bv = -1, bc = -1, bd = 100000, conf = 0, ties = 0;
    for (int v = 0; v < n; v++) {
      int *r = &hits[v * K], old = col[v], val = r[old];
      if (val == 0)
        continue;
      conf++;
      for (int c = 0; c < K; c++) {
        if (c == old)
          continue;
        int d = r[c] - val;
        if (d > bd || (tab[v * K + c] >= t && cost + d >= best))
          continue;
        if (d < bd) {
          ties = 0;
          bd = d;
        }
        if (++ties == 1 || rng() % ties == 0) {
          bv = v;
          bc = c;
        }
      }
    }
    if (bv < 0)
      break;
    int old = col[bv];
    col[bv] = bc;
    tab[bv * K + old] = t + 3 + conf / 2 + rng() % 9;
    for (int u : adj[bv]) {
      hits[u * K + old]--;
      hits[u * K + bc]++;
    }
    cost += bd;
    if (cost < best) {
      best = cost;
      best_colors = col;
    }
  }
  if (cost == 0) {
    copy(col.begin(), col.end(), out);
    return K;
  }
  // Start from a proper partial coloring by expelling one endpoint of
  // each remaining monochromatic edge. Prefer to branch on low-degree
  // vertices: their yes-branches have fewer possible members.
  col = best_colors;
  vector<int> weight(n), drop(n);
  for (int v = 0; v < n; ++v)
    weight[v] = 1 + (1 << (16 * int(adj[v].size()) / n));
  for (int v = 0; v < n; ++v)
    for (int u : adj[v])
      if (v < u && col[v] == col[u] && !drop[v] && !drop[u])
        drop[adj[v].size() < adj[u].size() ? v : u] = 1;

  // hits[v,c] now counts the total weight of v's neighbors colored c.
  // Insert an uncolored vertex v into c, expelling all such neighbors.
  fill(hits.begin(), hits.end(), 0);
  fill(tab.begin(), tab.end(), 0);
  int left = 0;
  for (int v = 0; v < n; ++v) {
    if (drop[v]) {
      col[v] = -1;
      left += weight[v];
    } else {
      for (int u : adj[v])
        hits[u * K + col[v]] += weight[v];
    }
  }
  int best_left = left;
  best_colors = col;
  for (int t = 1; t <= 3 * iters && left; ++t) {
    int v = -1, c = 0, delta = 100000000, ties = 0, uncolored = 0;
    for (int i = 0; i < n; ++i) {
      if (col[i] >= 0)
        continue;
      ++uncolored;
      for (int j = 0; j < K; ++j) {
        const int change = hits[i * K + j] - weight[i];
        if (change > delta ||
            (tab[i * K + j] >= t && left + change >= best_left))
          continue;
        if (change < delta) {
          delta = change;
          ties = 0;
        }
        if (++ties == 1 || rng() % ties == 0) {
          v = i;
          c = j;
        }
      }
    }
    if (v < 0)
      break;
    col[v] = c;
    const int until = t + 3 + rng() % 8 + uncolored / 2;
    for (int u : adj[v]) {
      hits[u * K + c] += weight[v];
      if (col[u] == c) {
        col[u] = -1;
        tab[u * K + c] = until;
        for (int w : adj[u])
          hits[w * K + c] -= weight[u];
      }
    }
    left += delta;
    if (left < best_left) {
      best_left = left;
      best_colors = col;
    }
  }
  int uncolored = 0;
  for (int i = 0; i < n; ++i) {
    if (best_colors[i] < 0) {
      out[i] = 255;
      ++uncolored;
    } else
      out[i] = static_cast<unsigned char>(best_colors[i]);
  }
  return uncolored ? -uncolored : K;
}
