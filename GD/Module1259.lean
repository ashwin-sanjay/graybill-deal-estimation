import GD.Module1258
import GD.Module1254
import GD.Module0201














open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace GD.N0232.N0720.N1317

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1345 _root_.GD.N0232.N0720.N1336
open _root_.GD.N0232.N0720.N1368 _root_.GD.N0232.N0720.N1352
open _root_.GD.N0232.N0720.N1351 _root_.GD.N0232.N0720.N1292
open _root_.GD.N0232.N0720.N1270 (d020224 d020225 d020226 d020227
  d020228 d020229 d020234
  d020238)
open _root_.GD.N0232.N0720.N1264 (d020252 d020244)
open _root_.GD.N0232.N0720.N1308

noncomputable section

theorem d020331 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (z w u : ℝ) :
    _root_.GD.N0232.N0720.N1308.d020280 D mu (![z, w, u] : _root_.GD.N0232.N0720.N1351.d002812) =
      1 - _root_.GD.N0232.N0720.N1368.d020209 ((D : ℝ) / 2) mu w z u := by
  simp only [_root_.GD.N0232.N0720.N1308.d020280, _root_.GD.N0232.N0720.N1292.d004162, _root_.GD.N0232.N0720.N1292.d004161, _root_.GD.N0232.N0720.N1264.d020244, _root_.GD.N0232.N0720.N1292.d004153,
    _root_.GD.N0232.N0720.N1368.d020209, _root_.GD.N0232.N0720.N1290.d004140, _root_.GD.N0232.N0720.N1290.d004139, _root_.GD.N0232.N0720.N1368.d020208,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, one_mul]

def d020332 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    _root_.GD.N0232.N0720.N1352.d002752 _root_.GD.N0232.N0720.N1270.d020224 :=
  _root_.GD.N0232.N0720.N1351.d002824 _root_.GD.N0232.N0720.N1292.d004157 (_root_.GD.N0232.N0720.N1308.d020280 D mu)
    (_root_.GD.N0232.N0720.N1308.d020281 D mu) (fun _ hx ↦ _root_.GD.N0232.N0720.N1264.d020252 hx)

theorem d020333 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)
    [IsProbabilityMeasure mu] {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    _root_.GD.N0232.N0720.N1352.d002762 (_root_.GD.N0232.N0720.N1317.d020332 D mu).G (_root_.GD.N0232.N0720.N1317.d020332 D mu).Gz
      (_root_.GD.N0232.N0720.N1317.d020332 D mu).Gw (_root_.GD.N0232.N0720.N1317.d020332 D mu).Gu (_root_.GD.N0232.N0720.N1270.d020226 w z) =
        -_root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 ((D : ℝ) / 2) mu) z w 0 := by
  have hp : (![w, z, 0] : _root_.GD.N0232.N0720.N1351.d002812) ∈ _root_.GD.N0232.N0720.N1292.d004155 := by
    simpa only [_root_.GD.N0232.N0720.N1270.d020229] using _root_.GD.N0232.N0720.N1264.d020252 (_root_.GD.N0232.N0720.N1270.d020227 hw hz)
  have hg := ((_root_.GD.N0232.N0720.N1308.d020281 D mu).contDiffAt
    (_root_.GD.N0232.N0720.N1292.d004157.mem_nhds hp)).differentiableAt (by simp)
  obtain ⟨h0, h1, h2⟩ := _root_.GD.N0232.N0720.N1270.d020234 hg
  have heq : (fun z w u ↦ _root_.GD.N0232.N0720.N1308.d020280 D mu (![z, w, u] : _root_.GD.N0232.N0720.N1351.d002812)) =
      (fun z w u ↦ 1 - _root_.GD.N0232.N0720.N1368.d020209 ((D : ℝ) / 2) mu w z u) := by
    funext z w u
    exact _root_.GD.N0232.N0720.N1317.d020331 D mu z w u
  calc
    _ = _root_.GD.N0232.N0720.N1368.d020210
        (fun z w u ↦ _root_.GD.N0232.N0720.N1308.d020280 D mu (![z, w, u] : _root_.GD.N0232.N0720.N1351.d002812)) w z 0 := by
      simp only [_root_.GD.N0232.N0720.N1352.d002762,
        _root_.GD.N0232.N0720.N1317.d020332, _root_.GD.N0232.N0720.N1351.d002824,
        _root_.GD.N0232.N0720.N1351.d002820, Function.comp_apply, _root_.GD.N0232.N0720.N1270.d020229,
        _root_.GD.N0232.N0720.N1368.d020210, h0, h1, h2]
    _ = _ := by rw [heq, _root_.GD.N0232.N0720.N1368.d020223]




theorem d020334
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      g x = _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x) mu)
    (m1 : _root_.GD.N0232.N0720.N1270.d020238 (m + n + 2) (_root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu)) : False := by
  have hqeq : (((m + n + 1 : ℕ) : ℝ) / 2) = _root_.GD.N0232.N0720.N1436.d013210 m n := by
    rw [_root_.GD.N0232.N0720.N1336.d013424 m n hm hn]
    simp only [Nat.cast_add, Nat.cast_one]
  have hq : (3 / 2 : ℝ) ≤ ((m + n + 1 : ℕ) : ℝ) / 2 := by
    have hD : (3 : ℝ) ≤ ((m + n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 3 ≤ m + n + 1 by omega)
    linarith
  have hpost' : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      g x = _root_.GD.N0232.N0720.N1290.d004140 (((m + n + 1 : ℕ) : ℝ) / 2) (_root_.GD.N0232.N0720.N1336.d013420 m n x) mu := by
    simpa only [hqeq] using hpost
  obtain ⟨z, w, hz, hw, hF⟩ :=
    _root_.GD.N0232.N0720.N1345.d020330
      _ hq hm hn hd hg hb hrep mu hpost'
  let m0 := _root_.GD.N0232.N0720.N1308.d020292 (m + n + 1) mu
  let H : _root_.GD.N0232.N0720.N1352.d002739 → ℝ := fun x ↦ m1.M x / m0.M x
  have hHinf : ContDiffOn ℝ ∞ H _root_.GD.N0232.N0720.N1270.d020224 :=
    m1.smooth_M.fun_div m0.smooth_M (fun x hx ↦ (m0.positive_M x hx).ne')
  have hH : ContDiffOn ℝ 2 H _root_.GD.N0232.N0720.N1270.d020224 := (contDiffOn_infty.mp hHinf) 2
  have hx := _root_.GD.N0232.N0720.N1270.d020227 hw hz
  apply _root_.GD.N0232.N0720.N1318.d002811
    (m + n + 1) _root_.GD.N0232.N0720.N1270.d020225 (_root_.GD.N0232.N0720.N1317.d020332 (m + n + 1) mu)
    hH m0.smooth_M m1.smooth_M
    (fun x hx ↦ (m0.positive_M x hx).ne')
    (fun x hx ↦ (div_mul_cancel₀ (m1.M x) (m0.positive_M x hx).ne').symm)
    m0.numerator m1.numerator m0.pde m1.pde hx (_root_.GD.N0232.N0720.N1270.d020228 w z)
  · rw [_root_.GD.N0232.N0720.N1317.d020333 _ _ hz hw]
    exact neg_ne_zero.mpr hF
  · exact (m1.positive_M _ hx).ne'
  · filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num)] with r hr
    exact ⟨m0.homogeneous _ hx r hr, m1.homogeneous _ hx r hr⟩

end
end GD.N0232.N0720.N1317

#print axioms _root_.GD.N0232.N0720.N1317.d020333
#print axioms _root_.GD.N0232.N0720.N1317.d020334
