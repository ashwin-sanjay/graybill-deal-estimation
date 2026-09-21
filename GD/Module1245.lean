import GD.Module1244
import GD.Module0315
import GD.Module0197





open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace GD.N0232.N0720.N1391

open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1373 _root_.GD.N0232.N0720.N1390
open _root_.GD.N0232.N0720.N1384 _root_.GD.N0232.N0720.N1297
open _root_.GD.N0232.N0720.N1401 _root_.GD.N0232.N0720.N1398

noncomputable section

variable {I : Type*} [Fintype I]

theorem d020163 (p : I → _root_.GD.N0232.N0720.N1373.d004629) (weight : I → ℝ)
    (f : _root_.GD.N0232.N0720.N1373.d004629 → ℝ) :
    Integrable f (∑ i, ENNReal.ofReal (weight i) • Measure.dirac (p i)) := by
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d020164 (p : I → _root_.GD.N0232.N0720.N1373.d004629) (weight : I → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (f : _root_.GD.N0232.N0720.N1373.d004629 → ℝ) :
    (∫ y, f y ∂(∑ i, ENNReal.ofReal (weight i) • Measure.dirac (p i))) =
      ∑ i, weight i * f (p i) := by
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d020165 (p : I → _root_.GD.N0232.N0720.N1373.d004629) (weight : I → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (x : _root_.GD.N0232.N0720.N1393.d004492) :
    _root_.GD.N0232.N0720.N1373.d004645 (∑ i, ENNReal.ofReal (weight i) • Measure.dirac (p i)) x =
      _root_.GD.N0232.N0720.N1384.d004684 p weight x := by
  unfold _root_.GD.N0232.N0720.N1373.d004645 _root_.GD.N0232.N0720.N1373.d004644 _root_.GD.N0232.N0720.N1373.d004643 _root_.GD.N0232.N0720.N1384.d004684
  rw [_root_.GD.N0232.N0720.N1391.d020164 p weight hw, _root_.GD.N0232.N0720.N1391.d020164 p weight hw]



theorem d020166
    {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) :
    ∃ ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629,
      (∀ β : ℝ, 0 < β → β < 1 / 2 → ∃ B : ℝ, _root_.GD.N0232.N0720.N1297.d002706 ν β B) ∧
      (∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1393.d004492),
        Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1373.d004645 (ν n : Measure _root_.GD.N0232.N0720.N1373.d004629) x) atTop
          (𝓝 (_root_.GD.N0232.N0720.N1401.d020150 (_root_.GD.N0232.N0720.N1398.d019601 d) x))) := by
  obtain ⟨m, p, weight, ν, hw, hprob, hν, _hinterior, hlim, hbetween⟩ :=
    _root_.GD.N0232.N0720.N1390.d020162 hd
  refine ⟨ν, ?_, hlim⟩
  intro β hβ hhalf
  have hlim' : ∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1393.d004492),
      Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1384.d004684 (p n) (weight n) x) atTop
        (𝓝 (_root_.GD.N0232.N0720.N1401.d020150 (_root_.GD.N0232.N0720.N1398.d019601 d) x)) := by
    simpa only [hν, _root_.GD.N0232.N0720.N1391.d020165 _ _ (hw _)] using hlim
  obtain ⟨B, hB⟩ := _root_.GD.N0232.N0720.N1384.d004696 p weight hw hprob
    (_root_.GD.N0232.N0720.N1401.d020150 (_root_.GD.N0232.N0720.N1398.d019601 d)) hlim' hbetween hβ.le hhalf
  refine ⟨B, ?_⟩
  intro n
  constructor
  · rw [hν]
    exact _root_.GD.N0232.N0720.N1391.d020163 (p n) (weight n) (_root_.GD.N0232.N0720.N1297.d002703 β)
  · rw [hν, _root_.GD.N0232.N0720.N1391.d020164 (p n) (weight n) (hw n)]
    exact hB n

end
end GD.N0232.N0720.N1391

#print axioms _root_.GD.N0232.N0720.N1391.d020166
