import GD.Module0901
import GD.Module0882


















open Filter ProbabilityTheory

namespace GD
namespace N0232
namespace N0720
namespace N1440

noncomputable section

open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0107
open _root_.GD.N0232.N0720.N1433
open _root_.GD.N0232.N0720.N1438
open _root_.GD.N0232.N0720.N1439





theorem d014041
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hbetaTwo : beta < 2)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 1))
    (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1) :
    Tendsto
      (fun k => _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p k) / (1 - p k) ^ beta)
      atTop
      (nhds ((beta / alpha) ^ beta *
        (ProbabilityTheory.beta beta (2 - beta) /
          ProbabilityTheory.beta beta alpha))) := by
  let q : ℕ → ℝ := fun k => 1 - p k
  have hq : Tendsto q atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [sub_self] using hconst.sub hp
  have hq0 : ∀ k, 0 < q k := fun k => sub_pos.mpr (hp1 k)
  have hq1 : ∀ k, q k < 1 := by
    intro k
    dsimp [q]
    linarith [hp0 k]
  have hleft := _root_.GD.N0232.N0720.N1439.d013669
    hbeta hbetaTwo halpha hq hq0 hq1
  convert hleft using 1
  funext k
  dsimp [q]
  rw [_root_.GD.N0232.N0720.N1438.d013603 halpha hbeta (hp0 k) (hp1 k)]


theorem d014042
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hbetaTwo : beta < 2)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 1))
    (hp0 : ∀ k, 0 < p k) (hp1 : ∀ k, p k < 1) :
    Tendsto
      (fun k => _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p k) / (1 - p k) ^ beta)
      atTop
      (nhds ((beta / alpha) ^ beta *
        Real.Gamma (alpha + beta) * Real.Gamma (2 - beta) /
          Real.Gamma alpha)) := by
  let q : ℕ → ℝ := fun k => 1 - p k
  have hq : Tendsto q atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [sub_self] using hconst.sub hp
  have hq0 : ∀ k, 0 < q k := fun k => sub_pos.mpr (hp1 k)
  have hq1 : ∀ k, q k < 1 := by
    intro k
    dsimp [q]
    linarith [hp0 k]
  have hleft := _root_.GD.N0232.N0720.N1439.d013670
    hbeta hbetaTwo halpha hq hq0 hq1
  convert hleft using 1
  · funext k
    dsimp [q]
    rw [_root_.GD.N0232.N0720.N1438.d013603 halpha hbeta (hp0 k) (hp1 k)]
  · rw [add_comm alpha beta]



theorem d014043
    {m : ℕ} (hm : m ≤ 4) :
    _root_.GD.N0232.N0720.N1433.d014024 m < 2 := by
  unfold _root_.GD.N0232.N0720.N1433.d014024
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  norm_num
  exact_mod_cast (show m - 1 < 4 by omega)

theorem d014044
    {n : ℕ} (hn : n ≤ 4) :
    _root_.GD.N0232.N0720.N1433.d014025 n < 2 := by
  unfold _root_.GD.N0232.N0720.N1433.d014025
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  norm_num
  exact_mod_cast (show n - 1 < 4 by omega)



theorem d014045
    {m n : ℕ} (hm : 2 ≤ m) (hmFour : m ≤ 4) (hn : 2 ≤ n)
    {mu sigma tau : ℕ → ℝ}
    (hsigma : ∀ k, 0 < sigma k) (htau : ∀ k, 0 < tau k)
    (hp : Tendsto
      (fun k => _root_.GD.N0107.d009046 m n (sigma k) (tau k))
      atTop (nhds 0)) :
    Tendsto
      (fun k =>
        _root_.GD.N0232.N0720.N1433.d014028 m n (mu k) (sigma k) (tau k) /
          (_root_.GD.N0107.d009045 m n (sigma k) (tau k) *
            _root_.GD.N0107.d009046 m n (sigma k) (tau k) ^
              _root_.GD.N0232.N0720.N1433.d014024 m))
      atTop
      (nhds ((_root_.GD.N0232.N0720.N1433.d014024 m / _root_.GD.N0232.N0720.N1433.d014025 n) ^
          _root_.GD.N0232.N0720.N1433.d014024 m *
        Real.Gamma (_root_.GD.N0232.N0720.N1433.d014024 m + _root_.GD.N0232.N0720.N1433.d014025 n) *
          Real.Gamma (2 - _root_.GD.N0232.N0720.N1433.d014024 m) /
            Real.Gamma (_root_.GD.N0232.N0720.N1433.d014025 n))) := by
  let p : ℕ → ℝ := fun k => _root_.GD.N0107.d009046 m n (sigma k) (tau k)
  have hp0 : ∀ k, 0 < p k := fun k =>
    _root_.GD.N0107.d009050 (by omega) (by omega) (hsigma k) (htau k)
  have hp1 : ∀ k, p k < 1 := fun k =>
    _root_.GD.N0107.d009051 (by omega) (by omega) (hsigma k) (htau k)
  have hBeta := _root_.GD.N0232.N0720.N1439.d013670
    (_root_.GD.N0232.N0720.N1433.d014026 hm) (_root_.GD.N0232.N0720.N1440.d014043 hmFour)
      (_root_.GD.N0232.N0720.N1433.d014027 hn) hp hp0 hp1
  convert hBeta using 1
  funext k
  rw [_root_.GD.N0232.N0720.N1433.d014032
    m n hm hn (mu k) (sigma k) (tau k) (hsigma k) (htau k)]
  have hSigma : 0 < _root_.GD.N0107.d009045 m n (sigma k) (tau k) :=
    _root_.GD.N0107.d009049 (by omega) (by omega) (hsigma k) (htau k)
  have hpow : 0 < _root_.GD.N0107.d009046 m n (sigma k) (tau k) ^
      _root_.GD.N0232.N0720.N1433.d014024 m :=
    Real.rpow_pos_of_pos (hp0 k) _
  field_simp [hSigma.ne', hpow.ne']



theorem d014046
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hnFour : n ≤ 4)
    {mu sigma tau : ℕ → ℝ}
    (hsigma : ∀ k, 0 < sigma k) (htau : ∀ k, 0 < tau k)
    (hp : Tendsto
      (fun k => _root_.GD.N0107.d009046 m n (sigma k) (tau k))
      atTop (nhds 1)) :
    Tendsto
      (fun k =>
        _root_.GD.N0232.N0720.N1433.d014028 m n (mu k) (sigma k) (tau k) /
          (_root_.GD.N0107.d009045 m n (sigma k) (tau k) *
            (1 - _root_.GD.N0107.d009046 m n (sigma k) (tau k)) ^
              _root_.GD.N0232.N0720.N1433.d014025 n))
      atTop
      (nhds ((_root_.GD.N0232.N0720.N1433.d014025 n / _root_.GD.N0232.N0720.N1433.d014024 m) ^
          _root_.GD.N0232.N0720.N1433.d014025 n *
        Real.Gamma (_root_.GD.N0232.N0720.N1433.d014024 m + _root_.GD.N0232.N0720.N1433.d014025 n) *
          Real.Gamma (2 - _root_.GD.N0232.N0720.N1433.d014025 n) /
            Real.Gamma (_root_.GD.N0232.N0720.N1433.d014024 m))) := by
  let p : ℕ → ℝ := fun k => _root_.GD.N0107.d009046 m n (sigma k) (tau k)
  have hp0 : ∀ k, 0 < p k := fun k =>
    _root_.GD.N0107.d009050 (by omega) (by omega) (hsigma k) (htau k)
  have hp1 : ∀ k, p k < 1 := fun k =>
    _root_.GD.N0107.d009051 (by omega) (by omega) (hsigma k) (htau k)
  have hBeta := _root_.GD.N0232.N0720.N1440.d014042
    (_root_.GD.N0232.N0720.N1433.d014026 hm) (_root_.GD.N0232.N0720.N1433.d014027 hn)
      (_root_.GD.N0232.N0720.N1440.d014044 hnFour) hp hp0 hp1
  convert hBeta using 1
  funext k
  rw [_root_.GD.N0232.N0720.N1433.d014032
    m n hm hn (mu k) (sigma k) (tau k) (hsigma k) (htau k)]
  have hSigma : 0 < _root_.GD.N0107.d009045 m n (sigma k) (tau k) :=
    _root_.GD.N0107.d009049 (by omega) (by omega) (hsigma k) (htau k)
  have hright : 0 < 1 - _root_.GD.N0107.d009046 m n (sigma k) (tau k) :=
    sub_pos.mpr (hp1 k)
  have hpow : 0 < (1 - _root_.GD.N0107.d009046 m n (sigma k) (tau k)) ^
      _root_.GD.N0232.N0720.N1433.d014025 n :=
    Real.rpow_pos_of_pos hright _
  field_simp [hSigma.ne', hpow.ne']

end

end N1440
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1440.d014041
#print axioms _root_.GD.N0232.N0720.N1440.d014042
#print axioms _root_.GD.N0232.N0720.N1440.d014045
#print axioms _root_.GD.N0232.N0720.N1440.d014046
