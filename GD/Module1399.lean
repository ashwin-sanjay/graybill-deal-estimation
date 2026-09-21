import GD.Module1398
import GD.Module0478
import GD.Module0486













set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace GD.N0160
noncomputable section

open _root_.GD.N0193 _root_.GD.N0163
open _root_.GD.N0177 _root_.GD.N0172
open _root_.GD.N0181 _root_.GD.N0167
open _root_.GD.N0171 _root_.GD.N0204


def d022516 (N : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    _root_.GD.N0163.d022186 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN)
  else 0

theorem d022517 {N : ℕ} (hN : 2 ≤ N) :
    _root_.GD.N0160.d022516 N =
      _root_.GD.N0163.d022186 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN) := by
  simp only [_root_.GD.N0160.d022516, dif_pos hN]

theorem d022518 {N : ℕ} (hN : 2 ≤ N) : 0 ≤ _root_.GD.N0160.d022516 N := by
  letI : Nonempty (_root_.GD.N0193.d007344 N) := ⟨(⟨0, _root_.GD.N0193.d007353 hN⟩, 0)⟩
  rw [_root_.GD.N0160.d022517 hN]
  exact _root_.GD.N0163.d022208 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N)
    (_root_.GD.N0177.d022414 hN) (fun _ => _root_.GD.N0193.d007367 hN)


theorem d022519 {N : ℕ} (hN : 2 ≤ N) :
    _root_.GD.N0160.d022516 N < Real.pi / 4 := by
  letI : Nonempty (_root_.GD.N0193.d007344 N) := ⟨(⟨0, _root_.GD.N0193.d007353 hN⟩, 0)⟩
  rw [_root_.GD.N0160.d022517 hN]
  exact _root_.GD.N0201.d022515
    (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN)
    (fun _ => _root_.GD.N0193.d007367 hN) (_root_.GD.N0193.d007374 hN)


def d022520 {N : ℕ} (hN : 16 ≤ N) :
    _root_.GD.N0209.d007520 (Real.pi / 4) (_root_.GD.N0160.d022516 N) (1 / (N : ℝ)) := by
  have hn2 : 2 ≤ N := by omega
  have hA : 0 < _root_.GD.N0167.d007305 N :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans (_root_.GD.N0167.d007316 hn2)
  refine {
    C := _root_.GD.N0172.d022468 (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007306 N)
    J := _root_.GD.N0181.d007274 N
    w := _root_.GD.N0204.d007394 N
    c := _root_.GD.N0171.d007331 N
    D := _root_.GD.N0181.d007269 N * _root_.GD.N0181.d007275 N
    E := _root_.GD.N0171.d007332 N
    w_nonneg := (_root_.GD.N0204.d007402 hN).le
    w_le_one := _root_.GD.N0204.d007404 hn2
    c_nonneg := (_root_.GD.N0171.d007335 hn2).le
    c_le_one := _root_.GD.N0171.d007336 hn2
    D_nonneg := (_root_.GD.N0181.d007303 hN).1
    J_le := ?_
    C_le := _root_.GD.N0201.d022514 hA (_root_.GD.N0167.d007318 hn2)
    continuum_lower := _root_.GD.N0172.d022484 hN
    discrete_lower := ?_
    truncation := (_root_.GD.N0181.d007300 hN).2
    window_error := ?_
    mass_error := (_root_.GD.N0181.d007303 hN).2
    mesh_error := ?_
    quadrature_error := ?_ }
  · linarith only [(_root_.GD.N0181.d007300 hN).1]
  · rw [_root_.GD.N0160.d022517 hn2]
    exact _root_.GD.N0172.d022483 hn2
  · simpa only [div_pow, one_pow, mul_one_div] using (_root_.GD.N0204.d007406 hN).2
  · have h := (_root_.GD.N0171.d007338 hN).2
    simpa only [div_pow, one_pow, mul_one_div, div_mul_eq_div_div] using h
  · have h := (_root_.GD.N0190.d007413 hN).2.1.trans
      (_root_.GD.N0190.d007413 hN).2.2
    simpa only [mul_one_div] using h

theorem d022521 {N : ℕ} (hN : 16 ≤ N) :
    Real.pi / 4 - _root_.GD.N0160.d022516 N ≤
      13 * (1 / (N : ℝ)) + 11 * (1 / (N : ℝ)) ^ 2 +
        3 * (1 / (N : ℝ)) ^ 3 + (7 / 2 : ℝ) * (1 / (N : ℝ)) ^ 4 := by
  exact _root_.GD.N0209.d007521 (by linarith [Real.pi_lt_four])
    (_root_.GD.N0160.d022520 hN)


theorem d022522 {N : ℕ} (hN : 16 ≤ N) :
    0 < Real.pi / 4 - _root_.GD.N0160.d022516 N ∧
      Real.pi / 4 - _root_.GD.N0160.d022516 N < 14 / (N : ℝ) := by
  refine ⟨sub_pos.mpr (_root_.GD.N0160.d022519 (by omega)), ?_⟩
  exact _root_.GD.N0209.d007523 (by linarith [Real.pi_lt_four])
    N hN (_root_.GD.N0160.d022520 hN)


theorem d022523 : (1 : ℝ) / 76 < _root_.GD.N0160.d022516 19 := by
  have h := (_root_.GD.N0160.d022522 (N := 19) (by norm_num)).2
  norm_num at h
  linarith [Real.pi_gt_three]


theorem d022524 (n : ℕ) (hn : 0 < n) :
    Real.pi / 4 - 1 / (n : ℝ) < _root_.GD.N0160.d022516 (16 * n) := by
  exact (_root_.GD.N0209.d007524 (P := ℕ) (Real.pi / 4) _root_.GD.N0160.d022516 id
    (by linarith [Real.pi_lt_four]) (fun _ hN => _root_.GD.N0160.d022520 hN)).1 n hn

theorem d022525 :
    Filter.Tendsto _root_.GD.N0160.d022516 Filter.atTop (nhds (Real.pi / 4)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt ((14 : ℝ) / ε)
  refine ⟨max 16 n, ?_⟩
  intro N hN
  have hn16 : 16 ≤ N := (le_max_left 16 n).trans hN
  have hnN : n ≤ N := (le_max_right 16 n).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hmul : (14 : ℝ) < (N : ℝ) * ε :=
    ((div_lt_iff₀ hε).mp hn).trans_le
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hnN) hε.le)
  have hfrac : (14 : ℝ) / (N : ℝ) < ε :=
    (div_lt_iff₀ hNpos).2 (by simpa only [mul_comm] using hmul)
  have hrate := _root_.GD.N0160.d022522 hn16
  rw [Real.dist_eq, abs_of_neg (sub_neg.mpr (_root_.GD.N0160.d022519 (by omega)))]
  linarith [hrate.2.trans hfrac]

end
end GD.N0160

#print axioms _root_.GD.N0160.d022517
#print axioms _root_.GD.N0160.d022518
#print axioms _root_.GD.N0160.d022519
#print axioms _root_.GD.N0160.d022521
#print axioms _root_.GD.N0160.d022522
#print axioms _root_.GD.N0160.d022523
#print axioms _root_.GD.N0160.d022524
#print axioms _root_.GD.N0160.d022525
