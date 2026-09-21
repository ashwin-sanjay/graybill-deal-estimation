import GD.Module1231
import GD.Module0313
import Mathlib.MeasureTheory.Measure.OpenPos













open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1322

open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1329
open _root_.GD.N0232.N0720.N1315 _root_.GD.N0232.N0720.N1331
open _root_.GD.N0232.N0720.N1382 (d004652 d004653)

noncomputable section

variable {m n d : ℕ} (hdim : m + n = d + 1)

def d020080 : Set (_root_.GD.N0232.N0720.N1341.d004414 d) :=
  (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim) ⁻¹' _root_.GD.N0232.N0720.N1382.d004652

theorem d020081 : IsOpen (_root_.GD.N0232.N0720.N1322.d020080 hdim) :=
  _root_.GD.N0232.N0720.N1382.d004653.preimage (_root_.GD.N0232.N0720.N1331.d020049 hdim)



theorem d020082 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1315.d019833} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) :
    ∃ omega : _root_.GD.N0232.N0720.N1341.d004414 d, _root_.GD.N0232.N0720.N1315.d019850 m n d hdim omega = x := by
  obtain ⟨X, hXmean, hXres⟩ := _root_.GD.N0232.N0720.N1331.d020048 m hm (x 0) hx.1
  obtain ⟨Y, hYmean, hYres⟩ := _root_.GD.N0232.N0720.N1331.d020048 n hn (x 1) hx.2
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨_root_.GD.N0232.N0720.N1329.d019648 m n d hdim (X, Y), ?_⟩
  have hdata : _root_.GD.N0232.N0720.N1315.d019850 m n d hdim (_root_.GD.N0232.N0720.N1329.d019648 m n d hdim (X, Y)) =
      ![_root_.GD.N0107.d009084 X,
        _root_.GD.N0107.d009084 Y,
        _root_.GD.N0126.d006422 X / (2 * (m : ℝ)),
        _root_.GD.N0126.d006422 Y / (2 * (n : ℝ))] := by
    simp only [_root_.GD.N0232.N0720.N1315.d019850, MeasurableEquiv.symm_apply_apply]
  rw [hdata]
  ext i
  fin_cases i
  · change _root_.GD.N0107.d009084 X = x 0
    exact hXmean
  · change _root_.GD.N0107.d009084 Y = x 1
    exact hYmean
  · change _root_.GD.N0126.d006422 X / (2 * (m : ℝ)) = x 2
    rw [hXres]
    field_simp [hmR]
  · change _root_.GD.N0126.d006422 Y / (2 * (n : ℝ)) = x 3
    rw [hYres]
    field_simp [hnR]

theorem d020083 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1315.d019833} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) :
    ∃ omega ∈ _root_.GD.N0232.N0720.N1322.d020080 hdim, _root_.GD.N0232.N0720.N1315.d019850 m n d hdim omega = x := by
  obtain ⟨omega, heq⟩ := _root_.GD.N0232.N0720.N1322.d020082 hdim hm hn hx
  refine ⟨omega, ?_, heq⟩
  change _root_.GD.N0232.N0720.N1315.d019850 m n d hdim omega ∈ _root_.GD.N0232.N0720.N1382.d004652
  rwa [heq]



theorem d020084 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {f g : _root_.GD.N0232.N0720.N1315.d019833 → ℝ} (hf : ContinuousOn f _root_.GD.N0232.N0720.N1382.d004652) (hg : ContinuousOn g _root_.GD.N0232.N0720.N1382.d004652)
    (hae : ∀ᵐ omega ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
      omega ∈ _root_.GD.N0232.N0720.N1322.d020080 hdim →
        f (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim omega) = g (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim omega)) :
    EqOn f g _root_.GD.N0232.N0720.N1382.d004652 := by
  have heq : EqOn (f ∘ _root_.GD.N0232.N0720.N1315.d019850 m n d hdim)
      (g ∘ _root_.GD.N0232.N0720.N1315.d019850 m n d hdim) (_root_.GD.N0232.N0720.N1322.d020080 hdim) :=
    Measure.eqOn_open_of_ae_eq
      ((ae_restrict_iff' (_root_.GD.N0232.N0720.N1322.d020081 hdim).measurableSet).2 hae)
      (_root_.GD.N0232.N0720.N1322.d020081 hdim)
      (hf.comp (_root_.GD.N0232.N0720.N1331.d020049 hdim).continuousOn (fun _ hx ↦ hx))
      (hg.comp (_root_.GD.N0232.N0720.N1331.d020049 hdim).continuousOn (fun _ hx ↦ hx))
  intro x hx
  obtain ⟨omega, homega, hdata⟩ := _root_.GD.N0232.N0720.N1322.d020083 hdim hm hn hx
  have h := heq homega
  simpa only [Function.comp_apply, hdata] using h

theorem d020085 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {f g : _root_.GD.N0232.N0720.N1315.d019833 → ℝ} (hf : ContinuousOn f _root_.GD.N0232.N0720.N1382.d004652) (hg : ContinuousOn g _root_.GD.N0232.N0720.N1382.d004652)
    (hae : f ∘ _root_.GD.N0232.N0720.N1315.d019850 m n d hdim =ᵐ[volume] g ∘ _root_.GD.N0232.N0720.N1315.d019850 m n d hdim) :
    EqOn f g _root_.GD.N0232.N0720.N1382.d004652 := by
  apply _root_.GD.N0232.N0720.N1322.d020084 hdim hm hn hf hg
  filter_upwards [hae] with omega heq _homega
  exact heq




theorem d020086 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {f g : _root_.GD.N0232.N0720.N1315.d019833 → ℝ} {r : _root_.GD.N0232.N0720.N1341.d004414 d → ℝ}
    (hf : ContinuousOn f _root_.GD.N0232.N0720.N1382.d004652) (hg : ContinuousOn g _root_.GD.N0232.N0720.N1382.d004652)
    (hfr : ∀ᵐ omega ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
      omega ∈ _root_.GD.N0232.N0720.N1322.d020080 hdim → f (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim omega) = r omega)
    (hgr : ∀ᵐ omega ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
      omega ∈ _root_.GD.N0232.N0720.N1322.d020080 hdim → g (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim omega) = r omega) :
    EqOn f g _root_.GD.N0232.N0720.N1382.d004652 := by
  apply _root_.GD.N0232.N0720.N1322.d020084 hdim hm hn hf hg
  filter_upwards [hfr, hgr] with omega hfomega hgomega homega
  exact (hfomega homega).trans (hgomega homega).symm

end

end GD.N0232.N0720.N1322

#print axioms _root_.GD.N0232.N0720.N1322.d020082
#print axioms _root_.GD.N0232.N0720.N1322.d020084
#print axioms _root_.GD.N0232.N0720.N1322.d020086
