import GD.Module1860
import GD.Module1417
import GD.Module0980

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace GD.N0207
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1336 _root_.GD.N0232.N0720.N1339
open _root_.GD.N0232.N0720.N1344 _root_.GD.N0232.N0720.N1340
open _root_.GD.N0232.N0720.N1328 _root_.GD.N0232.N0720.N1332
open _root_.GD.N0232.N0720.N1368 _root_.GD.N0232.N0720.N1352
open _root_.GD.N0232.N0720.N1351 _root_.GD.N0232.N0720.N1292
open _root_.GD.N0232.N0720.N1270 (d020224 d020225 d020226 d020227
  d020228 d020229 d020234
  d020238)
open _root_.GD.N0232.N0720.N1264 (d020252 d020244)
open _root_.GD.N0232.N0720.N1308 _root_.GD.N0232.N0720.N1317
open _root_.GD.N0096.N0344
open _root_.GD.N0232.N0720.N1303 _root_.GD.N0232.N0720.N1325
open _root_.GD.N0232.N0720.N1399 (d020100 d020102
  d020101 d020103)
open _root_.GD.N0232.N0720.N1218

 theorem d030551
    (m n : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (m1 : _root_.GD.N0232.N0720.N1270.d020238 (m + n + 2) (_root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu))
    (z w : ℝ) (hz : 0 < z) (hw : 0 < w) :
    _root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 (((m + n + 1 : ℕ) : ℝ) / 2) mu) z w 0 = 0 := by
  by_contra hF
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


theorem d030552
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hleft : Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0232.N0720.N1399.d020100 k).1)
      atTop (𝓝 0)) {a : ℝ} (ha : 0 < a) :
    ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, a ≤ g x) := by
  intro hfloor
  have hsmall := hleft.eventually_lt_const (sq_pos_of_pos (half_pos ha))
  have hfrac := _root_.GD.N0232.N0720.N1399.d020101.eventually_lt_const (half_pos ha)
  obtain ⟨k, hk, ht⟩ := (hsmall.and hfrac).exists
  have hbound := _root_.GD.N0232.N0720.N1332.d020117 hm hn hg hb (_root_.GD.N0232.N0720.N1399.d020100 k)
    (a := a) (by linarith) hfloor
  have hgap : a / 2 < a - (_root_.GD.N0232.N0720.N1399.d020100 k).1 := by linarith
  have hsquare := (sq_lt_sq₀ (half_pos ha).le (by linarith)).2 hgap
  linarith

theorem d030553
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hright : Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0232.N0720.N1399.d020102 k).1)
      atTop (𝓝 0)) {b : ℝ} (hbone : b < 1) :
    ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x ≤ b) := by
  intro hceiling
  have hgap : 0 < (1 - b) / 2 := half_pos (sub_pos.mpr hbone)
  have hsmall := hright.eventually_lt_const (sq_pos_of_pos hgap)
  have hfrac := _root_.GD.N0232.N0720.N1399.d020103.eventually_const_lt
    (show (1 + b) / 2 < 1 by linarith)
  obtain ⟨k, hk, ht⟩ := (hsmall.and hfrac).exists
  have hbound := _root_.GD.N0232.N0720.N1332.d020118 hm hn hg hb (_root_.GD.N0232.N0720.N1399.d020102 k)
    (b := b) (by linarith) hceiling
  have hsquare := (sq_lt_sq₀ hgap.le
    (show 0 ≤ (_root_.GD.N0232.N0720.N1399.d020102 k).1 - b by linarith)).2
    (show (1 - b) / 2 < (_root_.GD.N0232.N0720.N1399.d020102 k).1 - b by linarith)
  linarith

theorem d030554
    {m n : ℕ} {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} {B : ℝ}
    (hbound : ∀ t : _root_.GD.N0232.N0720.N1441.d013676, _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 ≤ B * t.1 * (1 - t.1)) :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0232.N0720.N1399.d020100 k).1) atTop (𝓝 0) ∧
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0232.N0720.N1399.d020102 k).1) atTop (𝓝 0) := by
  constructor
  · apply squeeze_zero (fun k ↦ _root_.GD.N0232.N0720.N1332.d020107 _ _ _ _)
      (fun k ↦ hbound (_root_.GD.N0232.N0720.N1399.d020100 k))
    simpa using (_root_.GD.N0232.N0720.N1399.d020101.const_mul B).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub _root_.GD.N0232.N0720.N1399.d020101)
  · apply squeeze_zero (fun k ↦ _root_.GD.N0232.N0720.N1332.d020107 _ _ _ _)
      (fun k ↦ hbound (_root_.GD.N0232.N0720.N1399.d020102 k))
    simpa using (_root_.GD.N0232.N0720.N1399.d020103.const_mul B).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub _root_.GD.N0232.N0720.N1399.d020103)

theorem d030555
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (q : ℝ) (hq : 3 / 2 ≤ q)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1) {B : ℝ}
    (hbound : ∀ t : _root_.GD.N0232.N0720.N1441.d013676, _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 ≤ B * t.1 * (1 - t.1))
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hF : ∀ᶠ epsilon in 𝓝 0,
      _root_.GD.N0232.N0720.N1290.d004143 q (_root_.GD.N0232.N0720.N1290.d004147 (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu)
        epsilon) mu = 0)
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      g x = _root_.GD.N0232.N0720.N1290.d004140 q (_root_.GD.N0232.N0720.N1336.d013420 m n x) mu) :
    Measure.map (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ)) mu = _root_.GD.N0232.N0720.N1344.d013339 q hq (1 / 2) (1 / 2) := by
  have hclass := _root_.GD.N0232.N0720.N1344.d013344 q hq mu hF
  have hr : 0 ≤ _root_.GD.N0232.N0720.N1344.d013342 q hq 0 1 mu := Real.sqrt_nonneg _
  have hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      Continuous (_root_.GD.N0232.N0720.N1336.d013420 m n x) ∧ ∀ t, 0 < _root_.GD.N0232.N0720.N1336.d013420 m n x t := by
    filter_upwards [_root_.GD.N0232.N0720.N1458.d018947
      m n (1 / 2)] with x hx
    exact ⟨(_root_.GD.N0232.N0720.N1336.d013421 m n).comp (continuous_const.prodMk continuous_id),
      _root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx⟩
  have hin := _root_.GD.N0232.N0720.N1340.d013353 q hq hclass
  have hcoeff := _root_.GD.N0232.N0720.N1334.d020121
    q hq hr hclass (_root_.GD.N0232.N0720.N1336.d013420 m n) hP hpost
  obtain ⟨hleft, hright⟩ := _root_.GD.N0207.d030554 hbound
  have hl : _root_.GD.N0232.N0720.N1414.d004212 0 1 mu -
      _root_.GD.N0232.N0720.N1344.d013342 q hq 0 1 mu ≤ 0 := by
    by_contra! hpos
    exact _root_.GD.N0207.d030552 hm hn hg hb hleft hpos
      (hcoeff.mono fun _ hx ↦ hx.1)
  have hu : 1 ≤ _root_.GD.N0232.N0720.N1414.d004212 0 1 mu +
      _root_.GD.N0232.N0720.N1344.d013342 q hq 0 1 mu := by
    by_contra! hlt
    exact _root_.GD.N0207.d030553 hm hn hg hb hright hlt
      (hcoeff.mono fun _ hx ↦ hx.2)
  have hc : _root_.GD.N0232.N0720.N1414.d004212 0 1 mu = 1 / 2 := by
    linarith [hin.1, hin.2]
  have hradius : _root_.GD.N0232.N0720.N1344.d013342 q hq 0 1 mu = 1 / 2 := by linarith [hin.1, hin.2]
  simpa only [hc, hradius] using hclass


theorem d030556
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1) {B : ℝ}
    (hbound : ∀ t : _root_.GD.N0232.N0720.N1441.d013676, _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 ≤ B * t.1 * (1 - t.1))
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      g x = _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x) mu)
    (m1 : _root_.GD.N0232.N0720.N1270.d020238 (m + n + 2) (_root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu)) :
    g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n]
      fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 := by
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
  have hF := _root_.GD.N0232.N0720.N1368.d020221
    (((m + n + 1 : ℕ) : ℝ) / 2)
    (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) mu
    (_root_.GD.N0207.d030551 m n mu m1)
  have hclass := _root_.GD.N0207.d030555 hm hn _ hq hg hb hbound mu hF hpost'
  filter_upwards [_root_.GD.N0232.N0720.N1458.d018947
    m n (1 / 2), hpost'] with x hx heq
  exact heq.trans (_root_.GD.N0232.N0720.N1345.d020328 _ hq hm hn mu hclass hx)

theorem d030557
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030491 m n d)
    (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta)) :
    ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
      _root_.GD.N0232.N0720.N1425.d014719 m n
        (fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) := by
  obtain ⟨g, mu, hg, hb, hrep, hpost⟩ :=
    _root_.GD.N0232.N0720.N1303.d030498 m n hm hn hd
  obtain ⟨m1⟩ := _root_.GD.N0232.N0720.N1325.d030508 m n (m + n - 1) (by omega)
    hm hn hd hg hb hrep mu hpost
  have hbound := _root_.GD.N0207.N0451.d022703
    hm hn hg hb (fun theta ↦ (hrep theta).symm) hC hcap
  have heq := _root_.GD.N0207.d030556 hm hn hg hb hbound
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) hpost m1
  have hrootMeas : Measurable (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦
      _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) :=
    (_root_.GD.N0232.N0720.N1328.d014757 _ _).comp measurable_fst
  have hrootBound (x : _root_.GD.N0232.N0720.N1436.d013217) :
      _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 ∈ Icc (0 : ℝ) 1 :=
    _root_.GD.N0232.N0720.N1328.d014758 (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn) x.1
  have hdom (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n
        (fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1)) ≤
      _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
    rw [← _root_.GD.N0232.N0720.N1159.d014662 m n theta (hrep theta)]
    exact (_root_.GD.N0232.N0720.N1333.d020201
      hm hn hg hrootMeas hb hrootBound heq theta).symm.le
  intro theta
  exact (hd.2.2.2 _ (_root_.GD.N0232.N0720.N1398.d019599
    m n hrootMeas) hdom theta).symm

end
end GD.N0207

#print axioms _root_.GD.N0207.d030551

#print axioms _root_.GD.N0207.d030554
#print axioms _root_.GD.N0207.d030555

#print axioms _root_.GD.N0207.d030556
#print axioms _root_.GD.N0207.d030557
