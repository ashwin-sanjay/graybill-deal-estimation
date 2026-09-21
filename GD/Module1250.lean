import GD.Module1247
import GD.Module0284
import GD.Module1248
import GD.Module0870
import GD.Module1177













open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1402

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1398 _root_.GD.N0232.N0720.N1403
open _root_.GD.N0232.N0720.N1414 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1357 _root_.GD.N0232.N0720.N1404
open _root_.GD.N0232.N0720.N1271

noncomputable section

theorem d020205 (x : _root_.GD.N0232.N0720.N1436.d013217) :
    Continuous (_root_.GD.N0232.N0720.N1271.d013404 x) :=
  _root_.GD.N0232.N0720.N1271.d013405.comp (continuous_const.prodMk continuous_id)

theorem d020206
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hclass : Measure.map (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ)) mu = _root_.GD.N0232.N0720.N1414.d004209 (1 / 2) (1 / 2))
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x) mu = _root_.GD.N0232.N0720.N1404.d020183 x.1 := by
  have heq :
      (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ _root_.GD.N0232.N0720.N1357.d004229 (Real.sqrt x.1) (Real.sqrt (1 - x.1)) x.2 t) =
        _root_.GD.N0232.N0720.N1271.d013404 x := by
    funext t
    unfold _root_.GD.N0232.N0720.N1357.d004229 _root_.GD.N0232.N0720.N1271.d013404 _root_.GD.N0232.N0720.N1271.d013403
    rw [Real.sq_sqrt hx.1.1.le, Real.sq_sqrt (sub_nonneg.mpr hx.1.2.le)]
    ring
  have h := _root_.GD.N0232.N0720.N1357.d004238 mu hclass
    (Real.sqrt_pos.2 hx.1.1) (Real.sqrt_pos.2 (sub_pos.mpr hx.1.2)) hx.2.le
  rw [heq] at h
  exact h




theorem d020207
    {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2,
      _root_.GD.N0232.N0720.N1398.d019601 d x = _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x) mu) :
    ¬ (∀ᶠ epsilon in nhds 0,
      _root_.GD.N0232.N0720.N1290.d004143 (5 / 2) (_root_.GD.N0232.N0720.N1290.d004147 (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) epsilon) mu = 0) := by
  intro hF
  have hdomain : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2, x ∈ _root_.GD.N0232.N0720.N1436.d013218 :=
    _root_.GD.N0232.N0720.N1458.d018947 2 2 (1 / 2)
  have hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2,
      Continuous (_root_.GD.N0232.N0720.N1271.d013404 x) ∧ ∀ t, 0 < _root_.GD.N0232.N0720.N1271.d013404 x t := by
    filter_upwards [hdomain] with x hx
    exact ⟨_root_.GD.N0232.N0720.N1402.d020205 x, _root_.GD.N0232.N0720.N1271.d013407 hx⟩
  have hclass := _root_.GD.N0232.N0720.N1403.d020182 hd mu hF
    _root_.GD.N0232.N0720.N1271.d013404 hP hpost
  apply _root_.GD.N0232.N0720.N1404.d020200 hd
  filter_upwards [hdomain, hpost] with x hx heq
  exact heq.trans (_root_.GD.N0232.N0720.N1402.d020206 mu hclass hx)

end
end GD.N0232.N0720.N1402

#print axioms _root_.GD.N0232.N0720.N1402.d020206
#print axioms _root_.GD.N0232.N0720.N1402.d020207
