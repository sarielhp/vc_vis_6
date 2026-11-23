#include <algorithm>
#include <fstream>
#include <iostream>
#include <map>
#include <string>
#include <tuple>
#include <vector>

struct CNF {
  int n_pts;
  int next_var = 1;
  std::vector<std::vector<std::vector<int>>> o;
  std::vector<std::vector<int>> clauses;
  std::map<std::pair<int, int>, int> eq_cache;
  std::map<std::tuple<int, int, int, int>, int> cross_cache;

  CNF(int n) : n_pts(n) {
    o.assign(n, std::vector<std::vector<int>>(n, std::vector<int>(n, 0)));
    for (int i = 0; i < n; ++i)
      for (int j = i + 1; j < n; ++j)
        for (int k = j + 1; k < n; ++k)
          o[i][j][k] = next_var++;
  }

  int new_var() { return next_var++; }

  int pos(int a, int b, int c) const {
    int lst[3] = {a, b, c};
    int inv = 0;
    if (lst[0] > lst[1]) { std::swap(lst[0], lst[1]); inv++; }
    if (lst[1] > lst[2]) { std::swap(lst[1], lst[2]); inv++; }
    if (lst[0] > lst[1]) { std::swap(lst[0], lst[1]); inv++; }
    int v = o[lst[0]][lst[1]][lst[2]];
    return (inv % 2 == 0) ? v : -v;
  }

  void add(std::initializer_list<int> lits) { clauses.emplace_back(lits); }
  void add_vec(const std::vector<int>& lits) { clauses.push_back(lits); }

  int mk_eq(int a, int b) {
    int flip = 0;
    if (a < 0) { a = -a; flip ^= 1; }
    if (b < 0) { b = -b; flip ^= 1; }
    if (a > b) std::swap(a, b);
    auto it = eq_cache.find({a, b});
    int x;
    if (it != eq_cache.end()) {
      x = it->second;
    } else {
      x = new_var();
      add({-a, -b, x});
      add({a, b, x});
      add({-x, -a, b});
      add({-x, a, -b});
      eq_cache[{a, b}] = x;
    }
    return flip ? -x : x;
  }
  int mk_same_side(int u, int v, int p, int q) {
    return mk_eq(pos(u, v, p), pos(u, v, q));
  }
  int mk_and(const std::vector<int>& ls) {
    int x = new_var();
    std::vector<int> big = {x};
    for (int l : ls) {
      add({-x, l});
      big.push_back(-l);
    }
    add_vec(big);
    return x;
  }
  int mk_or(const std::vector<int>& ls) {
    int x = new_var();
    std::vector<int> big = {-x};
    for (int l : ls) {
      add({x, -l});
      big.push_back(l);
    }
    add_vec(big);
    return x;
  }

  int mk_segs_cross(int a, int b, int c, int d) {
    if (a > b) std::swap(a, b);
    if (c > d) std::swap(c, d);
    if (std::make_pair(a, b) > std::make_pair(c, d)) { std::swap(a, c); std::swap(b, d); }
    auto key = std::make_tuple(a, b, c, d);
    auto it = cross_cache.find(key);
    if (it != cross_cache.end()) return it->second;
    int opp1 = mk_eq(pos(a, b, c), -pos(a, b, d));
    int opp2 = mk_eq(pos(c, d, a), -pos(c, d, b));
    int res = mk_and({opp1, opp2});
    cross_cache[key] = res;
    return res;
  }

  void add_gp(int max_w, int n_s) {
    for (int i = 0; i < n_pts; ++i)
      for (int j = i + 1; j < n_pts; ++j)
        for (int k = j + 1; k < n_pts; ++k)
          for (int l = k + 1; l < n_pts; ++l)
            for (int m = l + 1; m < n_pts; ++m) {
              int pts[5] = {i, j, k, l, m};
              if (max_w >= 0) {
                int wc = 0;
                for (int x : pts) if (x >= n_s) wc++;
                if (wc > max_w) continue;
              }
              for (int pi = 0; pi < 5; ++pi) {
                int p = pts[pi], r[4], ri = 0;
                for (int q = 0; q < 5; ++q) if (q != pi) r[ri++] = pts[q];
                int a = r[0], b = r[1], c = r[2], d = r[3];
                int l1 = pos(p, a, b), l2 = pos(p, c, d);
                int l3 = pos(p, a, c), l4 = -pos(p, b, d);
                int l5 = pos(p, a, d), l6 = pos(p, b, c);
                for (int s1 : {-1, 1})
                  for (int s2 : {-1, 1})
                    for (int s3 : {-1, 1}) {
                      add({-s1 * l1, -s1 * l2, -s2 * l3, -s2 * l4, -s3 * l5, -s3 * l6});
                      add({-s1 * l1,  s1 * l2, -s2 * l3,  s2 * l4, -s3 * l5,  s3 * l6});
                    }
              }
            }
  }

  int mk_in_int_tri_any(int p, int a, int b, int c) {
    int l1 = pos(a, b, p), l2 = pos(b, c, p), l3 = pos(c, a, p);
    int ccw = mk_and({l1, l2, l3});
    int cw = mk_and({-l1, -l2, -l3});
    return mk_or({ccw, cw});
  }

  void add_in_int_tri_any(int p, int a, int b, int c, bool negate) {
    int l1 = pos(a, b, p), l2 = pos(b, c, p), l3 = pos(c, a, p);
    if (negate) {
      add({-l1, -l2, -l3});
      add({l1, l2, l3});
    } else {
      int ccw = mk_and({l1, l2, l3});
      int cw = mk_and({-l1, -l2, -l3});
      add({ccw, cw});
    }
  }

  void add_wedge_sep(int y, const std::vector<int>& pos_w, const std::vector<int>& neg_w) {
    for (size_t i = 0; i < pos_w.size(); ++i) {
      int w1 = pos_w[i];
      for (size_t j = i + 1; j < pos_w.size(); ++j) {
        int w2 = pos_w[j];
        for (int z : neg_w) {
          add({-pos(y, w1, w2), -pos(y, w1, z), -pos(y, z, w2)});
          add({-pos(y, w2, w1), -pos(y, w2, z), -pos(y, z, w1)});
        }
      }
    }
  }

  void add_sound_4cycle(int w1, int a, int w2, int b, int fw, int fj) {
    int c_ccw = mk_and({pos(w1, a, w2), pos(a, w2, b), pos(w2, b, w1), pos(b, w1, a)});
    int c_cw  = mk_and({-pos(w1, a, w2), -pos(a, w2, b), -pos(w2, b, w1), -pos(b, w1, a)});
    int fw_ccw = mk_and({pos(w1, a, fw), pos(a, w2, fw), pos(w2, b, fw), pos(b, w1, fw)});
    int fj_ccw = mk_and({pos(w1, a, fj), pos(a, w2, fj), pos(w2, b, fj), pos(b, w1, fj)});
    add({-c_ccw, -fw_ccw, -fj_ccw});
    int fw_cw = mk_and({-pos(w1, a, fw), -pos(a, w2, fw), -pos(w2, b, fw), -pos(b, w1, fw)});
    int fj_cw = mk_and({-pos(w1, a, fj), -pos(a, w2, fj), -pos(w2, b, fj), -pos(b, w1, fj)});
    add({-c_cw, -fw_cw, -fj_cw});

    int pts[4] = {w1, a, w2, b};
    for (int r = 0; r < 4; ++r) {
      int vr = pts[r], vp = pts[(r + 1) % 4], vq = pts[(r + 2) % 4], vs = pts[(r + 3) % 4];
      int is_dart = mk_in_int_tri_any(vr, vp, vq, vs);
      int fw_out = mk_in_int_tri_any(fw, vp, vq, vs);
      int fj_out = mk_in_int_tri_any(fj, vp, vq, vs);
      int sp_fw = mk_same_side(vr, vp, fw, vq), sp_fj = mk_same_side(vr, vp, fj, vq);
      int ss_fw = mk_same_side(vr, vs, fw, vq), ss_fj = mk_same_side(vr, vs, fj, vq);
      add({-is_dart, -fw_out, -fj_out, -sp_fw, -sp_fj});
      add({-is_dart, -fw_out, -fj_out, -ss_fw, -ss_fj});
    }
  }

  void add_vertex_4cycle(int w1, int a, int w2, int b, int fw) {
    int c_ccw = mk_and({pos(w1, a, w2), pos(a, w2, b), pos(w2, b, w1), pos(b, w1, a)});
    int c_cw  = mk_and({-pos(w1, a, w2), -pos(a, w2, b), -pos(w2, b, w1), -pos(b, w1, a)});
    int fw_ccw = mk_and({pos(w1, a, fw), pos(a, w2, fw), pos(w2, b, fw), pos(b, w1, fw)});
    int fw_cw  = mk_and({-pos(w1, a, fw), -pos(a, w2, fw), -pos(w2, b, fw), -pos(b, w1, fw)});
    add({-c_ccw, -fw_ccw});
    add({-c_cw, -fw_cw});

    int pts[4] = {w1, a, w2, b};
    for (int r = 0; r < 4; ++r) {
      int i0 = r, i1 = (r + 1) % 4, i2 = (r + 2) % 4, i3 = (r + 3) % 4;
      int vr = pts[i0], vp = pts[i1], vq = pts[i2], vs = pts[i3];
      int is_dart = mk_in_int_tri_any(vr, vp, vq, vs);
      if (i0 == 1 || i2 == 1) {
        int fw1 = mk_in_int_tri_any(fw, vr, vp, vq);
        add({-is_dart, -fw1});
        int fw2 = mk_in_int_tri_any(fw, vr, vq, vs);
        add({-is_dart, -fw2});
      } else if (i1 == 1) {
        int fw_out = mk_in_int_tri_any(fw, vp, vq, vs);
        int sp_fw = mk_same_side(vr, vp, fw, vq);
        add({-is_dart, -fw_out, -sp_fw});
      } else if (i3 == 1) {
        int fw_out = mk_in_int_tri_any(fw, vp, vq, vs);
        int ss_fw = mk_same_side(vr, vs, fw, vq);
        add({-is_dart, -fw_out, -ss_fw});
      }
    }
  }
};

int main(int argc, char** argv) {
  if (argc < 14) {
    std::cerr << "Usage: gen_chiro_u3_h1 <n_s> <n_d> <h_size> <lr_l> <edge_str> <regB2_tri012> "
              << "<use_no_c7> <use_4cyc> <use_n1_t1> <use_wedge> <use_vis_ss> <max_w> <out.cnf> <m1> ...\n";
    std::cerr << "  edge_str: length (n_s - n_d), chars '0'=(0,1), ..., '4'=(4,0) [or (3,0) if n_d=4], 'x'=skip\n";
    std::cerr << "  use_n1_t1: bitmask 1=N1, 2=T1_b, 4=T1_both, 8=T2, 16=T3_b, 32=T3_both\n";
    return 1;
  }
  int n_s = std::stoi(argv[1]);
  int n_d = std::stoi(argv[2]);
  int h_size = std::stoi(argv[3]);
  int lr_l = std::stoi(argv[4]);
  std::string edge_str = argv[5];
  int regB2_tri012 = std::stoi(argv[6]);
  int use_no_c7 = std::stoi(argv[7]);
  int use_4cyc = std::stoi(argv[8]);
  int use_n1_t1 = std::stoi(argv[9]);
  int use_wedge = std::stoi(argv[10]);
  int use_vis_ss = std::stoi(argv[11]);
  int max_w = std::stoi(argv[12]);
  std::string out_path = argv[13];

  std::vector<int> masks;
  for (int i = 14; i < argc; ++i) masks.push_back(std::stoi(argv[i]));

  int full_mask = (1 << n_s) - 1;
  CNF cnf(n_s + (int)masks.size());

  // 1. D = (0..n_d-1) CCW strictly convex
  for (int i = 0; i < n_d; ++i)
    for (int j = i + 1; j < n_d; ++j)
      for (int k = j + 1; k < n_d; ++k) cnf.add({cnf.pos(i, j, k)});

  // B_ccw = D with H = {n_d .. n_d + h_size - 1} inserted after lr_l
  std::vector<int> B_ccw;
  for (int d = 0; d < n_d; ++d) {
    B_ccw.push_back(d);
    if (h_size > 0 && d == lr_l) {
      for (int h = 0; h < h_size; ++h) B_ccw.push_back(n_d + h);
    }
  }
  int b_sz = (int)B_ccw.size();
  for (int i = 0; i < b_sz; ++i)
    for (int j = i + 1; j < b_sz; ++j)
      for (int k = j + 1; k < b_sz; ++k) cnf.add({cnf.pos(B_ccw[i], B_ccw[j], B_ccw[k])});

  // A = {n_d + h_size .. n_s - 1} strictly inside int conv(B)
  // (NOTE: when h_size > 0, a in A MAY lie in the cap int tri(lr_l, h, lr_r), i.e., orient(lr_l, lr_r, a) < 0!)
  int a_start = n_d + h_size;
  for (int a = a_start; a < n_s; ++a) {
    for (int r = 0; r < b_sz; ++r) cnf.add({cnf.pos(B_ccw[r], B_ccw[(r + 1) % b_sz], a)});
  }

  // Regime B2: M cap int tri(0, 1, 2) != empty
  if (regB2_tri012 && n_d == 4) {
    std::vector<int> in_tri012;
    for (int a = a_start; a < n_s; ++a) in_tri012.push_back(-cnf.pos(0, 2, a));
    cnf.add_vec(in_tri012);
  }

  // Optional: No 7-subset of S in strictly convex position (|B| <= 6 Theorem)
  if (use_no_c7 && n_s >= 7) {
    std::map<int, int> not_conv4;
    for (int a = 0; a < n_s; ++a)
      for (int b = a + 1; b < n_s; ++b)
        for (int c = b + 1; c < n_s; ++c)
          for (int d = c + 1; d < n_s; ++d) {
            int pts[4] = {a, b, c, d};
            std::vector<int> ins;
            for (int p = 0; p < 4; ++p) {
              int r[3], ri = 0;
              for (int q = 0; q < 4; ++q) if (q != p) r[ri++] = pts[q];
              ins.push_back(cnf.mk_in_int_tri_any(pts[p], r[0], r[1], r[2]));
            }
            int m4 = (1 << a) | (1 << b) | (1 << c) | (1 << d);
            not_conv4[m4] = cnf.mk_or(ins);
          }
    for (int m7 = 0; m7 < (1 << n_s); ++m7) {
      if (__builtin_popcount(m7) != 7) continue;
      std::vector<int> s7;
      for (int i = 0; i < n_s; ++i) if ((m7 >> i) & 1) s7.push_back(i);
      std::vector<int> cl;
      for (int i = 0; i < 7; ++i)
        for (int j = i + 1; j < 7; ++j)
          for (int k = j + 1; k < 7; ++k)
            for (int l = k + 1; l < 7; ++l) {
              int m4 = (1 << s7[i]) | (1 << s7[j]) | (1 << s7[k]) | (1 << s7[l]);
              cl.push_back(not_conv4[m4]);
            }
      cnf.add_vec(cl);
    }
  }

  // 2. 5-pt Grassmann-Plucker axioms
  cnf.add_gp(max_w, n_s);

  std::map<int, int> W;
  for (size_t i = 0; i < masks.size(); ++i) W[masks[i]] = n_s + (int)i;

  // 3. Non-certified hull vertex obstruction (only k in D = {0..n_d-1})
  for (int m : masks) {
    int w = W[m];
    std::vector<int> sn;
    for (int s = 0; s < n_s; ++s) if ((m >> s) & 1) sn.push_back(s);
    for (int k = 0; k < n_d; ++k) if (!((m >> k) & 1)) {
      for (size_t x = 0; x < sn.size(); ++x)
        for (size_t y = x + 1; y < sn.size(); ++y)
          cnf.add_in_int_tri_any(k, w, sn[x], sn[y], true);
    }
  }

  // 4. Exit-edge cone U(y; u_y, v_y) and Wedge-Sep on W(e(y))
  if ((int)edge_str.size() == n_s - n_d) {
    for (int i = 0; i < n_s - n_d; ++i) {
      if (edge_str[i] == 'x') continue;
      int y = n_d + i;
      int u_y = edge_str[i] - '0';
      int v_y = (u_y + 1) % n_d;
      std::vector<int> pos_w, neg_w;
      for (int m : masks) {
        if (((m >> u_y) & 1) && ((m >> v_y) & 1)) {
          int w = W[m];
          cnf.add_in_int_tri_any(y, w, u_y, v_y, false);
          if ((m >> y) & 1) pos_w.push_back(w);
          else neg_w.push_back(w);
        }
      }
      if (use_wedge) cnf.add_wedge_sep(y, pos_w, neg_w);
    }
  }

  // 5. H != empty rules (Prop 4.1(ii), Def certified, Lemma separation + side-corners)
  if (h_size > 0) {
    int l = lr_l, r = (lr_l + 1) % n_d;
    // B_ccw indices of H: B_ccw[lr_l + 1 .. lr_l + h_size]
    for (int hi = 0; hi < h_size; ++hi) {
      int h = n_d + hi;
      int hm = (hi == 0) ? l : (h - 1);
      int hp = (hi + 1 == h_size) ? r : (h + 1);
      std::vector<int> pos_lr, neg_lr, pos_nb, neg_nb;
      for (int m : masks) {
        int w = W[m];
        if (((m >> l) & 1) && ((m >> r) & 1)) {
          cnf.add_in_int_tri_any(h, w, l, r, false);
          if ((m >> h) & 1) pos_lr.push_back(w);
          else neg_lr.push_back(w);
        }
        if (h_size > 1 && ((m >> hm) & 1) && ((m >> hp) & 1)) {
          if (!((m >> h) & 1)) {
            cnf.add_in_int_tri_any(h, w, hm, hp, false);
            neg_nb.push_back(w);
          } else {
            pos_nb.push_back(w);
          }
        }
      }
      if (use_wedge) {
        cnf.add_wedge_sep(h, pos_lr, neg_lr);
        // On W({hm, hp}), Lemma cone applies because z_h sees hm, hp, misses h, and h in int tri(z_h, hm, hp)
        if (h_size > 1) cnf.add_wedge_sep(h, pos_nb, neg_nb);
      }

      int zm = full_mask ^ (1 << h);
      if (W.count(zm)) {
        int zh = W[zm];
        for (int u = n_d; u < h; ++u) cnf.add({cnf.mk_eq(cnf.pos(zh, h, u), cnf.pos(zh, h, hm))});
        if (hi > 0) cnf.add({cnf.mk_eq(cnf.pos(zh, h, l), cnf.pos(zh, h, hm))});
        for (int v = h + 1; v < n_d + h_size; ++v) cnf.add({cnf.mk_eq(cnf.pos(zh, h, v), cnf.pos(zh, h, hp))});
        if (hi + 1 < h_size) cnf.add({cnf.mk_eq(cnf.pos(zh, h, r), cnf.pos(zh, h, hp))});
        for (int u = 0; u < n_s; ++u) if (u != h) {
          for (int v = u + 1; v < n_s; ++v) if (v != h) {
            int opp = cnf.mk_eq(cnf.pos(zh, h, u), -cnf.pos(zh, h, v));
            for (int mw : masks) if (((mw >> u) & 1) && ((mw >> v) & 1)) {
              int in_tri = cnf.mk_in_int_tri_any(h, W[mw], u, v);
              cnf.add({-opp, in_tri});
            }
          }
        }
      }
    }
  }

  // 6. Asymmetric Two-Sided Separation (Lemma 2.1(ii) / 11.1)
  for (int mx : masks) {
    int wx = W[mx];
    for (int d = 0; d < n_s; ++d) if (!((mx >> d) & 1)) {
      std::vector<int> seen_u;
      for (int u = 0; u < n_s; ++u) if ((mx >> u) & 1) seen_u.push_back(u);
      for (size_t ui = 0; ui < seen_u.size(); ++ui) {
        int u = seen_u[ui];
        for (size_t vi = ui + 1; vi < seen_u.size(); ++vi) {
          int v = seen_u[vi];
          for (int mi : masks) if (((mi >> d) & 1) && ((mi >> u) & 1)) {
            int wi = W[mi];
            for (int mj : masks) if (((mj >> d) & 1) && ((mj >> v) & 1)) {
              int wj = W[mj];
              if (wi == wj) continue;
              cnf.add({-cnf.pos(d, wx, u), cnf.pos(d, wx, v), -cnf.pos(d, wx, wi), cnf.pos(d, wx, wj)});
              cnf.add({cnf.pos(d, wx, u), -cnf.pos(d, wx, v), cnf.pos(d, wx, wi), -cnf.pos(d, wx, wj)});
            }
          }
        }
      }
    }
  }

  // 7. Universal Half-Plane Lemma (Lemma 4.4)
  if (W.count(full_mask)) {
    int q = W[full_mask];
    for (int mv : masks) if (mv != full_mask) {
      int v = W[mv];
      for (int p_idx = 0; p_idx < n_s; ++p_idx) if ((mv >> p_idx) & 1) {
        for (int a_idx = 0; a_idx < n_s; ++a_idx) if (a_idx != p_idx && !((mv >> a_idx) & 1)) {
          for (int c_idx = 0; c_idx < n_s; ++c_idx) if (c_idx != p_idx && c_idx != a_idx && !((mv >> c_idx) & 1)) {
            for (int sgn : {1, -1}) {
              std::vector<int> cond;
              cond.push_back(sgn * cnf.pos(v, q, a_idx));
              cond.push_back(sgn * cnf.pos(v, q, p_idx));
              cond.push_back(sgn * cnf.pos(v, q, c_idx));
              cond.push_back(sgn * cnf.pos(v, a_idx, p_idx));
              cond.push_back(sgn * cnf.pos(v, p_idx, c_idx));
              cond.push_back(sgn * cnf.pos(v, a_idx, c_idx));
              cond.push_back(cnf.mk_eq(cnf.pos(a_idx, c_idx, v), -cnf.pos(a_idx, c_idx, p_idx)));
              std::vector<int> cond_iv;
              for (int e_idx = 0; e_idx < n_s; ++e_idx) if ((mv >> e_idx) & 1) {
                cond_iv.push_back(cnf.mk_and({sgn * cnf.pos(v, q, e_idx), sgn * cnf.pos(v, e_idx, a_idx)}));
              }
              std::vector<int> seen_v;
              for (int s = 0; s < n_s; ++s) if ((mv >> s) & 1) seen_v.push_back(s);
              for (size_t si = 0; si < seen_v.size(); ++si) {
                for (size_t sj = si + 1; sj < seen_v.size(); ++sj) {
                  cond_iv.push_back(cnf.mk_eq(cnf.pos(v, q, seen_v[si]), -cnf.pos(v, q, seen_v[sj])));
                }
              }
              if (cond_iv.empty()) continue;
              cond.push_back(cnf.mk_or(cond_iv));
              int act = cnf.mk_and(cond);
              std::vector<int> sees, misses;
              for (int mw : masks) if (mw != mv && ((mw >> a_idx) & 1) && ((mw >> c_idx) & 1)) {
                int w = W[mw];
                cnf.add({-act, cnf.mk_eq(cnf.pos(v, a_idx, w), cnf.pos(v, a_idx, q))});
                cnf.add({-act, cnf.mk_eq(cnf.pos(v, p_idx, w), cnf.pos(v, p_idx, q))});
                if ((mw >> p_idx) & 1) {
                  cnf.add({-act, cnf.mk_eq(cnf.pos(p_idx, a_idx, w), cnf.pos(p_idx, a_idx, q))});
                  sees.push_back(w);
                } else {
                  misses.push_back(w);
                }
              }
              for (int ws : sees) for (int wm : misses) {
                cnf.add({-act, sgn * cnf.pos(p_idx, ws, wm)});
              }
            }
          }
        }
      }
    }
  }

  // 8. Sound 4-cycle convex quad + dart enclosure
  if (use_4cyc) {
    for (int fm : masks) {
      int fw = W[fm];
      for (int fj = 0; fj < n_s; ++fj) if (!((fm >> fj) & 1)) {
        for (size_t i = 0; i < masks.size(); ++i) if (masks[i] != fm) {
          for (size_t j = i + 1; j < masks.size(); ++j) if (masks[j] != fm) {
            int cm = masks[i] & masks[j];
            std::vector<int> cs;
            for (int k = 0; k < n_s; ++k) if (((cm >> k) & 1) && k != fj) cs.push_back(k);
            for (size_t x = 0; x < cs.size(); ++x)
              for (size_t y = x + 1; y < cs.size(); ++y)
                cnf.add_sound_4cycle(W[masks[i]], cs[x], W[masks[j]], cs[y], fw, fj);
          }
        }
      }
    }
  }

  // 9. Rule N1
  if (use_n1_t1 & 1) {
    for (int fm : masks) {
      int fw = W[fm];
      for (int fj = 0; fj < n_s; ++fj) if (!((fm >> fj) & 1)) {
        for (size_t i = 0; i < masks.size(); ++i) if (masks[i] != fm && ((masks[i] >> fj) & 1)) {
          for (size_t j = i + 1; j < masks.size(); ++j) if (masks[j] != fm && ((masks[j] >> fj) & 1)) {
            int cm = masks[i] & masks[j];
            for (int b = 0; b < n_s; ++b) if (b != fj && ((cm >> b) & 1)) {
              cnf.add_vertex_4cycle(W[masks[i]], fj, W[masks[j]], b, fw);
            }
          }
        }
      }
    }
  }

  // 10. Rule T1
  if (use_n1_t1 & 6) {
    for (size_t i = 0; i < masks.size(); ++i) {
      int mi = masks[i], w1 = W[mi];
      for (int a = 0; a < n_s; ++a) if ((mi >> a) & 1) {
        for (int b = 0; b < n_s; ++b) if (b != a && ((mi >> b) & 1)) {
          for (size_t j = 0; j < masks.size(); ++j) if (j != i && ((masks[j] >> b) & 1)) {
            int mj = masks[j], w2 = W[mj];
            int cr = cnf.mk_segs_cross(w1, a, w2, b);
            for (int fm : masks) if (fm != mi && fm != mj) {
              int fw = W[fm];
              int s1 = cnf.mk_same_side(w1, a, fw, b);
              int s2 = cnf.mk_same_side(w2, b, fw, w1);
              int s3 = cnf.mk_same_side(w1, b, fw, a);
              if ((use_n1_t1 & 2) && !((fm >> b) & 1)) {
                cnf.add({-cr, -s1, -s2, -s3});
              }
              if (use_n1_t1 & 4) {
                int fw_in = cnf.mk_and({s1, s2, s3});
                for (int fj = 0; fj < n_s; ++fj) if (fj != a && fj != b && !((fm >> fj) & 1)) {
                  int j1 = cnf.mk_same_side(w1, a, fj, b);
                  int j2 = cnf.mk_same_side(w2, b, fj, w1);
                  int j3 = cnf.mk_same_side(w1, b, fj, a);
                  cnf.add({-cr, -fw_in, -j1, -j2, -j3});
                }
              }
            }
          }
        }
      }
    }
  }

  // 11. Rule T2
  if (use_n1_t1 & 8) {
    for (size_t j = 0; j < masks.size(); ++j) {
      int mj = masks[j], w2 = W[mj];
      for (int b = 0; b < n_s; ++b) if ((mj >> b) & 1) {
        for (int c = b + 1; c < n_s; ++c) if ((mj >> c) & 1) {
          for (size_t i = 0; i < masks.size(); ++i) if (i != j) {
            int mi = masks[i], w1 = W[mi];
            for (int a = 0; a < n_s; ++a) if (a != b && a != c && ((mi >> a) & 1)) {
              int cr1 = cnf.mk_segs_cross(w1, a, w2, b);
              int cr2 = cnf.mk_segs_cross(w1, a, w2, c);
              int both_cr = cnf.mk_and({cr1, cr2});
              for (int fm : masks) if (fm != mi && fm != mj) {
                int fw = W[fm];
                int f1 = cnf.mk_same_side(w1, a, fw, w2);
                int f2 = cnf.mk_same_side(w2, b, fw, c);
                int f3 = cnf.mk_same_side(w2, c, fw, b);
                int fw_in = cnf.mk_and({f1, f2, f3});
                for (int fj = 0; fj < n_s; ++fj) if (fj != a && fj != b && fj != c && !((fm >> fj) & 1)) {
                  int j1 = cnf.mk_same_side(w1, a, fj, w2);
                  int j2 = cnf.mk_same_side(w2, b, fj, c);
                  int j3 = cnf.mk_same_side(w2, c, fj, b);
                  cnf.add({-both_cr, -fw_in, -j1, -j2, -j3});
                }
              }
            }
          }
        }
      }
    }
  }

  // 12. Rule T3
  if (use_n1_t1 & 48) {
    for (size_t i = 0; i < masks.size(); ++i) {
      int mi = masks[i], w1 = W[mi];
      for (size_t j = i + 1; j < masks.size(); ++j) {
        int mj = masks[j], w2 = W[mj];
        int cm = mi & mj;
        for (int b = 0; b < n_s; ++b) if ((cm >> b) & 1) {
          for (int a = 0; a < n_s; ++a) if (a != b && ((mi >> a) & 1)) {
            for (int c = 0; c < n_s; ++c) if (c != b && c != a && ((mj >> c) & 1)) {
              int cr_ac = cnf.mk_segs_cross(w1, a, w2, c);
              int cr_ab = cnf.mk_segs_cross(w1, a, w2, b);
              int cr_cb = cnf.mk_segs_cross(w2, c, w1, b);
              int opp_a = -cnf.mk_same_side(w1, w2, a, b);
              int opp_c = -cnf.mk_same_side(w1, w2, c, b);
              int valid = cnf.mk_and({cr_ac, -cr_ab, -cr_cb, opp_a, opp_c});
              for (int fm : masks) if (fm != mi && fm != mj) {
                int fw = W[fm];
                int f1 = cnf.mk_same_side(b, w1, fw, w2);
                int f2 = cnf.mk_same_side(w1, a, fw, b);
                int f3 = cnf.mk_same_side(w2, c, fw, b);
                int f4 = cnf.mk_same_side(w2, b, fw, w1);
                if ((use_n1_t1 & 16) && !((fm >> b) & 1)) {
                  cnf.add({-valid, -f1, -f2, -f3, -f4});
                }
                if (use_n1_t1 & 32) {
                  int fw_in = cnf.mk_and({f1, f2, f3, f4});
                  for (int fj = 0; fj < n_s; ++fj) if (fj != a && fj != b && fj != c && !((fm >> fj) & 1)) {
                    int j1 = cnf.mk_same_side(b, w1, fj, w2);
                    int j2 = cnf.mk_same_side(w1, a, fj, b);
                    int j3 = cnf.mk_same_side(w2, c, fj, b);
                    int j4 = cnf.mk_same_side(w2, b, fj, w1);
                    cnf.add({-valid, -fw_in, -j1, -j2, -j3, -j4});
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  // 13. Eager vis_SS (Round-1 E1 + Round-2 E2)
  if (use_vis_ss) {
    for (int a = 0; a < n_s; ++a) {
      for (int b = a + 1; b < n_s; ++b) {
        int vis_ab = cnf.new_var();
        std::vector<int> w_ab;
        for (int m : masks) if (((m >> a) & 1) && ((m >> b) & 1)) w_ab.push_back(W[m]);
        for (size_t i = 0; i < w_ab.size(); ++i) {
          int w1 = w_ab[i];
          int l1 = cnf.pos(a, b, w1);
          for (size_t j = i + 1; j < w_ab.size(); ++j) {
            int w2 = w_ab[j];
            int l2 = cnf.pos(a, b, w2);
            cnf.add({-l1, l2, vis_ab});
            cnf.add({l1, -l2, vis_ab});
          }
        }
        for (int m3 : masks) if (((m3 >> a) & 1) && ((m3 >> b) & 1)) {
          int w3 = W[m3];
          for (int fm : masks) if (fm != m3) {
            int fw = W[fm];
            int fw_in = cnf.mk_in_int_tri_any(fw, w3, a, b);
            if (!((fm >> a) & 1) || !((fm >> b) & 1)) {
              cnf.add({-vis_ab, -fw_in});
            }
            for (int fj = 0; fj < n_s; ++fj) {
              if (fj == a || fj == b || ((fm >> fj) & 1)) continue;
              int j1 = cnf.pos(w3, a, fj), j2 = cnf.pos(a, b, fj), j3 = cnf.pos(b, w3, fj);
              cnf.add({-vis_ab, -fw_in, -j1, -j2, -j3});
              cnf.add({-vis_ab, -fw_in, j1, j2, j3});
            }
          }
        }
      }
    }
  }

  if (out_path == "-") {
    std::cerr << "[gen_chiro_u3_h1] n_s=" << n_s << " m=" << masks.size()
              << " vars=" << (cnf.next_var - 1) << " clauses=" << cnf.clauses.size() << "\n";
    std::ios::sync_with_stdio(false);
    std::cout << "p cnf " << (cnf.next_var - 1) << " " << cnf.clauses.size() << "\n";
    for (const auto& cl : cnf.clauses) {
      for (int l : cl) std::cout << l << " ";
      std::cout << "0\n";
    }
  } else {
    std::ofstream out(out_path);
    out << "p cnf " << (cnf.next_var - 1) << " " << cnf.clauses.size() << "\n";
    for (const auto& cl : cnf.clauses) {
      for (int l : cl) out << l << " ";
      out << "0\n";
    }
  }
  return 0;
}
