import GD.Module1860
import GD.Module1259

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

namespace GD.N0206.N0449
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1336 _root_.GD.N0232.N0720.N1344
open _root_.GD.N0232.N0720.N1334 _root_.GD.N0232.N0720.N1340
open _root_.GD.N0232.N0720.N1345 _root_.GD.N0232.N0720.N1339
open _root_.GD.N0232.N0720.N1317 _root_.GD.N0232.N0720.N1308
open _root_.GD.N0232.N0720.N1368 _root_.GD.N0232.N0720.N1352
open _root_.GD.N0232.N0720.N1351 _root_.GD.N0232.N0720.N1292
open _root_.GD.N0232.N0720.N1270 (d020224 d020225 d020226 d020227
  d020228 d020238)
open _root_.GD.N0232.N0720.N1414 (d004212)
open _root_.GD.N0232.N0720.N1328
open _root_.GD.N0096.N0344

theorem d030692
    (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (m1 : _root_.GD.N0232.N0720.N1270.d020238 (D + 1) (_root_.GD.N0232.N0720.N1308.d020280 D mu))
    {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    _root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 ((D : ℝ) / 2) mu) z w 0 = 0 := by
  by_contra hF
  let m0 := _root_.GD.N0232.N0720.N1308.d020292 D mu
  let H : _root_.GD.N0232.N0720.N1352.d002739 → ℝ := fun x => m1.M x / m0.M x
  have hHinf : ContDiffOn ℝ ∞ H _root_.GD.N0232.N0720.N1270.d020224 :=
    m1.smooth_M.fun_div m0.smooth_M (fun x hx => (m0.positive_M x hx).ne')
  have hH : ContDiffOn ℝ 2 H _root_.GD.N0232.N0720.N1270.d020224 := (contDiffOn_infty.mp hHinf) 2
  have hx := _root_.GD.N0232.N0720.N1270.d020227 hw hz
  apply _root_.GD.N0232.N0720.N1318.d002811
    D _root_.GD.N0232.N0720.N1270.d020225 (_root_.GD.N0232.N0720.N1317.d020332 D mu)
    hH m0.smooth_M m1.smooth_M
    (fun x hx => (m0.positive_M x hx).ne')
    (fun x hx => (div_mul_cancel₀ (m1.M x) (m0.positive_M x hx).ne').symm)
    m0.numerator m1.numerator m0.pde m1.pde hx (_root_.GD.N0232.N0720.N1270.d020228 w z)
  · rw [_root_.GD.N0232.N0720.N1317.d020333 _ _ hz hw]
    exact neg_ne_zero.mpr hF
  · exact (m1.positive_M _ hx).ne'
  · filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num)] with r hr
    exact ⟨m0.homogeneous _ hx r hr, m1.homogeneous _ hx r hr⟩

theorem d030693
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n D : ℕ}
    (hqD : q = (D : ℝ) / 2)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (m1 : _root_.GD.N0232.N0720.N1270.d020238 (D + 1) (_root_.GD.N0232.N0720.N1308.d020280 D mu))
    (P : _root_.GD.N0232.N0720.N1436.d013217 → _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, Continuous (P x) ∧ ∀ t, 0 < P x t)
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x = _root_.GD.N0232.N0720.N1290.d004140 q (P x) mu)
    (hfloor : ∀ a : ℝ, 0 < a → ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, a ≤ g x))
    (hceiling : ∀ b : ℝ, b < 1 → ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x ≤ b)) :
    Measure.map (fun t : _root_.GD.N0232.N0720.N1290.d004131 => (t : ℝ)) mu = _root_.GD.N0232.N0720.N1344.d013339 q hq (1 / 2) (1 / 2) := by
  have hzero : ∀ z w : ℝ, 0 < z → 0 < w →
      _root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 q mu) z w 0 = 0 := by
    intro z w hz hw
    rw [hqD]
    exact _root_.GD.N0206.N0449.d030692 D mu m1 hz hw
  have hF := _root_.GD.N0232.N0720.N1368.d020221
    q (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) mu hzero
  have hclass := _root_.GD.N0232.N0720.N1344.d013344 q hq mu hF
  have hr : 0 ≤ _root_.GD.N0232.N0720.N1344.d013342 q hq 0 1 mu := Real.sqrt_nonneg _
  have hend := _root_.GD.N0232.N0720.N1340.d013353 q hq hclass
  have hcoeff := _root_.GD.N0232.N0720.N1334.d020121 q hq hr hclass P hP hpost
  have hleft : _root_.GD.N0232.N0720.N1414.d004212 0 1 mu - _root_.GD.N0232.N0720.N1344.d013342 q hq 0 1 mu ≤ 0 := by
    by_contra! hpos
    exact hfloor _ hpos (hcoeff.mono fun _ hx => hx.1)
  have hright : 1 ≤ _root_.GD.N0232.N0720.N1414.d004212 0 1 mu + _root_.GD.N0232.N0720.N1344.d013342 q hq 0 1 mu := by
    by_contra! hlt
    exact hceiling _ hlt (hcoeff.mono fun _ hx => hx.2)
  have hc : _root_.GD.N0232.N0720.N1414.d004212 0 1 mu = 1 / 2 := by linarith [hend.1, hend.2]
  have hradius : _root_.GD.N0232.N0720.N1344.d013342 q hq 0 1 mu = 1 / 2 := by linarith [hend.1, hend.2]
  simpa only [hc, hradius] using hclass

theorem d030694
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      g x = _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x) mu)
    (m1 : _root_.GD.N0232.N0720.N1270.d020238 (m + n + 2) (_root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu))
    (hfloor : ∀ a : ℝ, 0 < a → ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, a ≤ g x))
    (hceiling : ∀ b : ℝ, b < 1 → ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x ≤ b)) :
    g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun x =>
      _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 := by
  have hqeq : _root_.GD.N0232.N0720.N1436.d013210 m n = (((m + n + 1 : ℕ) : ℝ) / 2) := by
    rw [_root_.GD.N0232.N0720.N1336.d013424 m n hm hn]
    simp only [Nat.cast_add, Nat.cast_one]
  have hq : (3 / 2 : ℝ) ≤ _root_.GD.N0232.N0720.N1436.d013210 m n := by
    rw [hqeq]
    have hD : (3 : ℝ) ≤ ((m + n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 3 ≤ m + n + 1 by omega)
    linarith
  have hdomain : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, x ∈ _root_.GD.N0232.N0720.N1436.d013218 :=
    _root_.GD.N0232.N0720.N1458.d018947 m n (1 / 2)
  have hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      Continuous (_root_.GD.N0232.N0720.N1336.d013420 m n x) ∧ ∀ t, 0 < _root_.GD.N0232.N0720.N1336.d013420 m n x t := by
    filter_upwards [hdomain] with x hx
    exact ⟨(_root_.GD.N0232.N0720.N1336.d013421 m n).comp (continuous_const.prodMk continuous_id),
      _root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx⟩
  have hm1 : _root_.GD.N0232.N0720.N1270.d020238 ((m + n + 1) + 1) (_root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu) := by
    simpa only [Nat.add_assoc] using m1
  have hclass := _root_.GD.N0206.N0449.d030693
    (_root_.GD.N0232.N0720.N1436.d013210 m n) hq hqeq mu hm1 (_root_.GD.N0232.N0720.N1336.d013420 m n) hP hpost hfloor hceiling
  filter_upwards [hdomain, hpost] with x hx heq
  exact heq.trans (_root_.GD.N0232.N0720.N1345.d020328
    (_root_.GD.N0232.N0720.N1436.d013210 m n) hq hm hn mu hclass hx)

end
end GD.N0206.N0449

#print axioms _root_.GD.N0206.N0449.d030692
#print axioms _root_.GD.N0206.N0449.d030693
#print axioms _root_.GD.N0206.N0449.d030694
