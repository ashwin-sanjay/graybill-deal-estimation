import GD.Module0863









open MeasureTheory Set Filter
open scoped Topology Interval

namespace GD.N0232.N0720.N1339

open _root_.GD.N0232.N0720.N1320 _root_.GD.N0232.N0720.N1344
open _root_.GD.N0232.N0720.N1357 _root_.GD.N0232.N0720.N1338
open _root_.GD.N0232.N0720.N1290

noncomputable section

private theorem d013345 (q : ℝ) (hq : 3 / 2 ≤ q)
    {a v : ℝ} (ha : |a| < 1) (hv : 0 ≤ v) :
    (∫ x : _root_.GD.N0232.N0720.N1320.d013309, ((x : ℝ) - a) *
      (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-q) ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) = 0 := by
  rw [_root_.GD.N0232.N0720.N1320.d013322 q hq (fun x : ℝ ↦ (x - a) * (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-q))]
  have horder : (fun x : ℝ ↦ _root_.GD.N0232.N0720.N1320.d013310 q x * ((x - a) *
      (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-q))) =
      fun x ↦ (x - a) * (1 - x ^ 2) ^ (q - 3 / 2) *
        (_root_.GD.N0232.N0720.N1357.d004218 a v x) ^ (-q) := by
    funext x
    unfold _root_.GD.N0232.N0720.N1320.d013310
    ring
  rw [horder, _root_.GD.N0232.N0720.N1338.d013306 hq ha hv, mul_zero]



theorem d013346 (q : ℝ) (hq : 3 / 2 ≤ q) {p r u : ℝ}
    (hp : 0 < p) (hr : 0 < r) (hu : 0 ≤ u) :
    (∫ t : ℝ, (t - p / (p + r)) *
      (_root_.GD.N0232.N0720.N1357.d004229 p r u t) ^ (-q) ∂_root_.GD.N0232.N0720.N1344.d013339 q hq (1 / 2) (1 / 2)) = 0 := by
  have ha := _root_.GD.N0232.N0720.N1357.d004233 hp hr
  have hA : 0 < _root_.GD.N0232.N0720.N1357.d004231 p r := by unfold _root_.GD.N0232.N0720.N1357.d004231; positivity
  have hv : 0 ≤ _root_.GD.N0232.N0720.N1357.d004232 p r u := by unfold _root_.GD.N0232.N0720.N1357.d004232; positivity
  have hmeas : Measurable (fun t : ℝ ↦ (t - p / (p + r)) *
      (_root_.GD.N0232.N0720.N1357.d004229 p r u t) ^ (-q)) := by
    unfold _root_.GD.N0232.N0720.N1357.d004229
    fun_prop
  rw [_root_.GD.N0232.N0720.N1344.d013339, integral_map
    (f := fun t : ℝ ↦ (t - p / (p + r)) *
      (_root_.GD.N0232.N0720.N1357.d004229 p r u t) ^ (-q))
    (by fun_prop) hmeas.aestronglyMeasurable]
  have heq :
      (∫ x : _root_.GD.N0232.N0720.N1320.d013309, (1 / 2 + 1 / 2 * (x : ℝ) - p / (p + r)) *
        (_root_.GD.N0232.N0720.N1357.d004229 p r u (1 / 2 + 1 / 2 * (x : ℝ))) ^ (-q)
        ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) =
      ((_root_.GD.N0232.N0720.N1357.d004231 p r) ^ (-q) / 2) *
        ∫ x : _root_.GD.N0232.N0720.N1320.d013309, ((x : ℝ) - _root_.GD.N0232.N0720.N1357.d004230 p r) *
          (_root_.GD.N0232.N0720.N1357.d004218 (_root_.GD.N0232.N0720.N1357.d004230 p r) (_root_.GD.N0232.N0720.N1357.d004232 p r u) x) ^ (-q)
          ∂(_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [show (1 / 2 : ℝ) + 1 / 2 * (x : ℝ) = (1 + (x : ℝ)) / 2 by ring,
      _root_.GD.N0232.N0720.N1357.d004234 hp hr,
      _root_.GD.N0232.N0720.N1357.d004235 hp hr,
      Real.mul_rpow hA.le (_root_.GD.N0232.N0720.N1357.d004219 ha hv x.2).le]
    ring
  rw [heq, _root_.GD.N0232.N0720.N1339.d013345 q hq ha hv, mul_zero]





theorem d013347 (q : ℝ) (hq : 3 / 2 ≤ q)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hclass : Measure.map (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ)) mu = _root_.GD.N0232.N0720.N1344.d013339 q hq (1 / 2) (1 / 2))
    {p r u : ℝ} (hp : 0 < p) (hr : 0 < r) (hu : 0 ≤ u) :
    _root_.GD.N0232.N0720.N1290.d004140 q (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ _root_.GD.N0232.N0720.N1357.d004229 p r u t) mu = p / (p + r) := by
  let P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ := fun t ↦ _root_.GD.N0232.N0720.N1357.d004229 p r u t
  let K : _root_.GD.N0232.N0720.N1290.d004131 → ℝ := fun t ↦ (P t) ^ (-q)
  have hP : Continuous P := by unfold P _root_.GD.N0232.N0720.N1357.d004229; fun_prop
  have hpos (t : _root_.GD.N0232.N0720.N1290.d004131) : 0 < P t := _root_.GD.N0232.N0720.N1357.d004236 hp hr hu t.2
  have hK : Integrable K mu := by
    simpa [K] using _root_.GD.N0232.N0720.N1290.d004135 q (phi := fun _ ↦ 1)
      continuous_const hP hpos mu
  have hTK : Integrable (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ) * K t) mu :=
    _root_.GD.N0232.N0720.N1290.d004135 q continuous_subtype_val hP hpos mu
  have hzero : (∫ t : _root_.GD.N0232.N0720.N1290.d004131, ((t : ℝ) - p / (p + r)) * K t ∂mu) = 0 := by
    have h := _root_.GD.N0232.N0720.N1339.d013346 q hq hp hr hu
    have hmeas : Measurable (fun t : ℝ ↦ (t - p / (p + r)) *
        (_root_.GD.N0232.N0720.N1357.d004229 p r u t) ^ (-q)) := by
      unfold _root_.GD.N0232.N0720.N1357.d004229
      fun_prop
    rw [← hclass, integral_map
      (f := fun t : ℝ ↦ (t - p / (p + r)) *
        (_root_.GD.N0232.N0720.N1357.d004229 p r u t) ^ (-q))
      measurable_subtype_coe.aemeasurable hmeas.aestronglyMeasurable] at h
    exact h
  have hmoment : (∫ t : _root_.GD.N0232.N0720.N1290.d004131, (t : ℝ) * K t ∂mu) =
      (p / (p + r)) * ∫ t : _root_.GD.N0232.N0720.N1290.d004131, K t ∂mu := by
    simp_rw [sub_mul] at hzero
    rw [integral_sub hTK (hK.const_mul _), integral_const_mul] at hzero
    exact sub_eq_zero.mp hzero
  change (∫ t : _root_.GD.N0232.N0720.N1290.d004131, (t : ℝ) * K t ∂mu) / _root_.GD.N0232.N0720.N1290.d004139 q P mu = _
  apply (div_eq_iff (ne_of_gt (_root_.GD.N0232.N0720.N1290.d004146 q P hP hpos mu))).2
  exact hmoment

end
end GD.N0232.N0720.N1339

#print axioms _root_.GD.N0232.N0720.N1339.d013346
#print axioms _root_.GD.N0232.N0720.N1339.d013347
