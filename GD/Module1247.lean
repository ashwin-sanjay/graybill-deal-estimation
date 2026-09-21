import GD.Module0285
import GD.Module1235















open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1403

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1398 _root_.GD.N0232.N0720.N1399
open _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1414 _root_.GD.N0232.N0720.N1359

noncomputable section



theorem d020180
    {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ} {mu : Measure _root_.GD.N0232.N0720.N1290.d004131} [IsProbabilityMeasure mu]
    {center r : ℝ} (hr : 0 ≤ r)
    (hclass : Measure.map (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ)) mu = _root_.GD.N0232.N0720.N1414.d004209 center r)
    (P : _root_.GD.N0232.N0720.N1436.d013217 → _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2, Continuous (P x) ∧ ∀ t, 0 < P x t)
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2,
      _root_.GD.N0232.N0720.N1398.d019601 d x = _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (P x) mu) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2,
      _root_.GD.N0232.N0720.N1398.d019601 d x ∈ Icc (center - r) (center + r) := by
  have hs := _root_.GD.N0232.N0720.N1359.d004245 hr hclass
  filter_upwards [hP, hpost] with x hx heq
  rw [heq]
  exact _root_.GD.N0232.N0720.N1359.d004246 (5 / 2) (P x) hx.1 hx.2 mu hs




theorem d020181
    {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d)
    {mu : Measure _root_.GD.N0232.N0720.N1290.d004131} [IsProbabilityMeasure mu]
    {center r : ℝ} (hr : 0 ≤ r)
    (hclass : Measure.map (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ)) mu = _root_.GD.N0232.N0720.N1414.d004209 center r)
    (P : _root_.GD.N0232.N0720.N1436.d013217 → _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2, Continuous (P x) ∧ ∀ t, 0 < P x t)
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2,
      _root_.GD.N0232.N0720.N1398.d019601 d x = _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (P x) mu) :
    center = 1 / 2 ∧ r = 1 / 2 := by
  have hin := _root_.GD.N0232.N0720.N1359.d004244 hclass
  have hcoeff := _root_.GD.N0232.N0720.N1403.d020180 hr hclass P hP hpost
  have hleft : center - r ≤ 0 := by
    by_contra! hpos
    exact _root_.GD.N0232.N0720.N1399.d020104 hd hpos (hcoeff.mono fun _ hx ↦ hx.1)
  have hright : 1 ≤ center + r := by
    by_contra! hlt
    exact _root_.GD.N0232.N0720.N1399.d020105 hd hlt (hcoeff.mono fun _ hx ↦ hx.2)
  constructor <;> linarith [hin.1, hin.2]





theorem d020182
    {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hF : ∀ᶠ epsilon in nhds 0,
      _root_.GD.N0232.N0720.N1290.d004143 (5 / 2) (_root_.GD.N0232.N0720.N1290.d004147 (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) epsilon) mu = 0)
    (P : _root_.GD.N0232.N0720.N1436.d013217 → _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2, Continuous (P x) ∧ ∀ t, 0 < P x t)
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2,
      _root_.GD.N0232.N0720.N1398.d019601 d x = _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (P x) mu) :
    Measure.map (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ)) mu = _root_.GD.N0232.N0720.N1414.d004209 (1 / 2) (1 / 2) := by
  have hclass := _root_.GD.N0232.N0720.N1414.d004217 mu hF
  have hr : 0 ≤ _root_.GD.N0232.N0720.N1414.d004215 0 1 mu := Real.sqrt_nonneg _
  obtain ⟨hc, hradius⟩ := _root_.GD.N0232.N0720.N1403.d020181 hd hr hclass P hP hpost
  simpa only [hc, hradius] using hclass

end
end GD.N0232.N0720.N1403

#print axioms _root_.GD.N0232.N0720.N1403.d020181
#print axioms _root_.GD.N0232.N0720.N1403.d020182
