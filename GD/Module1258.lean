import GD.Module1237
import GD.Module0864
import GD.Module1249
import GD.Module0872
import GD.Module1251










open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1345

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1334 _root_.GD.N0232.N0720.N1339
open _root_.GD.N0232.N0720.N1344 _root_.GD.N0232.N0720.N1336
open _root_.GD.N0232.N0720.N1328 _root_.GD.N0232.N0720.N1333
open _root_.GD.N0232.N0720.N1357 _root_.GD.N0232.N0720.N1368
open _root_.GD.N0232.N0720.N1414 (d004212)

noncomputable section

theorem d020327 (m n : ℕ) (r : ℝ) :
    _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) r =
      Real.sqrt (((n - 1 : ℕ) : ℝ) * r) /
        (Real.sqrt (((n - 1 : ℕ) : ℝ) * r) +
          Real.sqrt (((m - 1 : ℕ) : ℝ) * (1 - r))) := by
  unfold _root_.GD.N0232.N0720.N1328.d014755 _root_.GD.N0232.N0720.N1436.d013207 _root_.GD.N0232.N0720.N1436.d013208
  rw [show (((n - 1 : ℕ) : ℝ) / 2) * r =
      (1 / 2) * (((n - 1 : ℕ) : ℝ) * r) by ring,
    show (((m - 1 : ℕ) : ℝ) / 2) * (1 - r) =
      (1 / 2) * (((m - 1 : ℕ) : ℝ) * (1 - r)) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), ← mul_add]
  exact mul_div_mul_left _ _ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 1 / 2)).ne'

theorem d020328
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hclass : Measure.map (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ)) mu = _root_.GD.N0232.N0720.N1344.d013339 q hq (1 / 2) (1 / 2))
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1290.d004140 q (_root_.GD.N0232.N0720.N1336.d013420 m n x) mu =
      _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 := by
  have hz : 0 < ((n - 1 : ℕ) : ℝ) * x.1 :=
    mul_pos (by exact_mod_cast (show 0 < n - 1 by omega)) hx.1.1
  have hw : 0 < ((m - 1 : ℕ) : ℝ) * (1 - x.1) :=
    mul_pos (by exact_mod_cast (show 0 < m - 1 by omega)) (sub_pos.mpr hx.1.2)
  have heq : (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ _root_.GD.N0232.N0720.N1357.d004229
      (Real.sqrt (((n - 1 : ℕ) : ℝ) * x.1))
      (Real.sqrt (((m - 1 : ℕ) : ℝ) * (1 - x.1))) x.2 t) =
      _root_.GD.N0232.N0720.N1336.d013420 m n x := by
    funext t
    unfold _root_.GD.N0232.N0720.N1357.d004229 _root_.GD.N0232.N0720.N1336.d013420 _root_.GD.N0232.N0720.N1271.d013403
    rw [Real.sq_sqrt hz.le, Real.sq_sqrt hw.le]
    ring
  have h := _root_.GD.N0232.N0720.N1339.d013347 q hq mu hclass
    (Real.sqrt_pos.mpr hz) (Real.sqrt_pos.mpr hw) hx.2.le
  rw [heq] at h
  exact h.trans (_root_.GD.N0232.N0720.N1345.d020327 m n x.1).symm

theorem d020329
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x = _root_.GD.N0232.N0720.N1290.d004140 q (_root_.GD.N0232.N0720.N1336.d013420 m n x) mu) :
    ¬ (∀ᶠ epsilon in nhds 0,
      _root_.GD.N0232.N0720.N1290.d004143 q (_root_.GD.N0232.N0720.N1290.d004147 (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) epsilon) mu = 0) := by
  intro hF
  have hdomain : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, x ∈ _root_.GD.N0232.N0720.N1436.d013218 :=
    _root_.GD.N0232.N0720.N1458.d018947 m n (1 / 2)
  have hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      Continuous (_root_.GD.N0232.N0720.N1336.d013420 m n x) ∧ ∀ t, 0 < _root_.GD.N0232.N0720.N1336.d013420 m n x t := by
    filter_upwards [hdomain] with x hx
    exact ⟨(_root_.GD.N0232.N0720.N1336.d013421 m n).comp (continuous_const.prodMk continuous_id),
      _root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx⟩
  have hclass := _root_.GD.N0232.N0720.N1334.d020123 q hq hm hn
    hd hg hb hrep mu hF (_root_.GD.N0232.N0720.N1336.d013420 m n) hP hpost
  apply _root_.GD.N0232.N0720.N1333.d020204 hm hn hd hg hb hrep
  filter_upwards [hdomain, hpost] with x hx heq
  exact heq.trans (_root_.GD.N0232.N0720.N1345.d020328 q hq hm hn mu hclass hx)

theorem d020330
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x = _root_.GD.N0232.N0720.N1290.d004140 q (_root_.GD.N0232.N0720.N1336.d013420 m n x) mu) :
    ∃ z w : ℝ, 0 < z ∧ 0 < w ∧
      _root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 q mu) z w 0 ≠ 0 := by
  by_contra hnone
  have hzero : ∀ z w : ℝ, 0 < z → 0 < w →
      _root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 q mu) z w 0 = 0 := by
    intro z w hz hw
    by_contra hne
    exact hnone ⟨z, w, hz, hw, hne⟩
  apply _root_.GD.N0232.N0720.N1345.d020329 q hq hm hn hd hg hb hrep mu hpost
  exact _root_.GD.N0232.N0720.N1368.d020221
    q (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) mu hzero

end
end GD.N0232.N0720.N1345

#print axioms _root_.GD.N0232.N0720.N1345.d020328
#print axioms _root_.GD.N0232.N0720.N1345.d020329
#print axioms _root_.GD.N0232.N0720.N1345.d020330
