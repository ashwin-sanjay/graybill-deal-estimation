import GD.Module1245
import GD.Module0313
import GD.Module0198














open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1394

open _root_.GD.N0232.N0720.N1373 _root_.GD.N0232.N0720.N1391
open _root_.GD.N0232.N0720.N1382 _root_.GD.N0232.N0720.N1376
open _root_.GD.N0232.N0720.N1297 _root_.GD.N0232.N0720.N1296
open _root_.GD.N0232.N0720.N1401 _root_.GD.N0232.N0720.N1398
open _root_.GD.N0232.N0720.N1159

noncomputable section

abbrev d020167 := _root_.GD.N0232.N0720.N1393.d004492

def d020168 (x : _root_.GD.N0232.N0720.N1394.d020167) : _root_.GD.N0232.N0720.N1382.d004651 :=
  ![x 0, x 2, x 1 ^ 2 / 2, x 3 ^ 2 / 2]

def d020169 : Set _root_.GD.N0232.N0720.N1394.d020167 :=
  {x | _root_.GD.N0232.N0720.N1394.d020168 x ∈ _root_.GD.N0232.N0720.N1382.d004652}

theorem d020170 : Continuous _root_.GD.N0232.N0720.N1394.d020168 := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [_root_.GD.N0232.N0720.N1394.d020168] <;> fun_prop

theorem d020171 : IsOpen _root_.GD.N0232.N0720.N1394.d020169 :=
  _root_.GD.N0232.N0720.N1382.d004653.preimage _root_.GD.N0232.N0720.N1394.d020170

def d020172 (ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629) : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 / 2 → ∃ B : ℝ, _root_.GD.N0232.N0720.N1297.d002706 ν β B

theorem d020173
    {ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629} {μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629}
    (hlim : Tendsto ν atTop (𝓝 μ)) (hmoment : _root_.GD.N0232.N0720.N1394.d020172 ν) :
    _root_.GD.N0232.N0720.N1382.d004657 (μ : Measure _root_.GD.N0232.N0720.N1373.d004629) := by
  intro β hβ hhalf
  obtain ⟨B, hB⟩ := hmoment β hβ hhalf
  exact (_root_.GD.N0232.N0720.N1297.d002712 hlim hB).1

theorem d020174
    {ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629} {μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629}
    (hlim : Tendsto ν atTop (𝓝 μ)) (hmoment : _root_.GD.N0232.N0720.N1394.d020172 ν)
    (n m : ℕ) {φ : _root_.GD.N0232.N0720.N1373.d004628 → ℝ} (hφ : Continuous φ)
    {x : _root_.GD.N0232.N0720.N1382.d004651} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) :
    Tendsto (fun j ↦ ∫ p, _root_.GD.N0232.N0720.N1382.d004668 n m φ x p ∂(ν j : Measure _root_.GD.N0232.N0720.N1373.d004629))
      atTop (𝓝 (∫ p, _root_.GD.N0232.N0720.N1382.d004668 n m φ x p ∂(μ : Measure _root_.GD.N0232.N0720.N1373.d004629))) := by
  obtain ⟨δ, R, hδ, hR, hbox⟩ := _root_.GD.N0232.N0720.N1382.d004667 hx
  let α : ℝ := (_root_.GD.N0232.N0720.N1382.d004663 δ R + 1 / 2) / 2
  let β : ℝ := (α + 1 / 2) / 2
  have hrate : _root_.GD.N0232.N0720.N1382.d004663 δ R < 1 / 2 := _root_.GD.N0232.N0720.N1382.d004665 hδ
  have hrate0 : 0 < _root_.GD.N0232.N0720.N1382.d004663 δ R := _root_.GD.N0232.N0720.N1382.d004664 hδ hR
  have hα : _root_.GD.N0232.N0720.N1382.d004663 δ R < α := by dsimp [α]; linarith
  have hαβ : α < β := by dsimp [α, β]; linarith
  have hβ : 0 < β := by dsimp [α, β]; linarith
  have hβhalf : β < 1 / 2 := by dsimp [α, β]; linarith
  obtain ⟨C, hC, hb⟩ := _root_.GD.N0232.N0720.N1382.d004670 n m hφ hδ hR hα
  obtain ⟨B, hB⟩ := hmoment β hβ hβhalf
  exact _root_.GD.N0232.N0720.N1296.d002721 hlim hB
    (_root_.GD.N0232.N0720.N1382.d004669 n m hφ hx) hC.le hβ hαβ
    (hb x (mem_of_mem_nhds hbox))

theorem d020175 (ν : Measure _root_.GD.N0232.N0720.N1373.d004629)
    (x : _root_.GD.N0232.N0720.N1394.d020167) :
    _root_.GD.N0232.N0720.N1373.d004643 ν x = (∫ p, _root_.GD.N0232.N0720.N1382.d004668 5 0 (fun _ ↦ 1) (_root_.GD.N0232.N0720.N1394.d020168 x) p ∂ν) / 8 := by
  simp [_root_.GD.N0232.N0720.N1373.d004643, _root_.GD.N0232.N0720.N1373.d004631, _root_.GD.N0232.N0720.N1376.d002894, _root_.GD.N0232.N0720.N1382.d004668,
    _root_.GD.N0232.N0720.N1394.d020168, _root_.GD.N0232.N0720.N1382.d004654, _root_.GD.N0232.N0720.N1382.d004655, integral_div]

theorem d020176 (ν : Measure _root_.GD.N0232.N0720.N1373.d004629)
    (x : _root_.GD.N0232.N0720.N1394.d020167) :
    _root_.GD.N0232.N0720.N1373.d004644 ν x = (∫ p, _root_.GD.N0232.N0720.N1382.d004668 4 1 (fun _ ↦ 1) (_root_.GD.N0232.N0720.N1394.d020168 x) p ∂ν) / 8 := by
  simp [_root_.GD.N0232.N0720.N1373.d004644, _root_.GD.N0232.N0720.N1373.d004632, _root_.GD.N0232.N0720.N1376.d002895, _root_.GD.N0232.N0720.N1382.d004668,
    _root_.GD.N0232.N0720.N1394.d020168, _root_.GD.N0232.N0720.N1382.d004654, _root_.GD.N0232.N0720.N1382.d004655, integral_div]

theorem d020177 (μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629)
    (hμ : _root_.GD.N0232.N0720.N1382.d004657 (μ : Measure _root_.GD.N0232.N0720.N1373.d004629))
    {x : _root_.GD.N0232.N0720.N1394.d020167} (hx : x ∈ _root_.GD.N0232.N0720.N1394.d020169) :
    0 < _root_.GD.N0232.N0720.N1373.d004643 (μ : Measure _root_.GD.N0232.N0720.N1373.d004629) x := by
  have hi : Integrable (fun p ↦ _root_.GD.N0232.N0720.N1373.d004631 p x) (μ : Measure _root_.GD.N0232.N0720.N1373.d004629) := by
    convert (_root_.GD.N0232.N0720.N1382.d004671 5 0 (phi := fun _ ↦ 1) continuous_const
      (μ : Measure _root_.GD.N0232.N0720.N1373.d004629) hμ hx).div_const 8 using 1
    ext p
    simp [_root_.GD.N0232.N0720.N1373.d004631, _root_.GD.N0232.N0720.N1376.d002894, _root_.GD.N0232.N0720.N1382.d004668, _root_.GD.N0232.N0720.N1394.d020168, _root_.GD.N0232.N0720.N1382.d004654, _root_.GD.N0232.N0720.N1382.d004655]
  have hp (p : _root_.GD.N0232.N0720.N1373.d004629) : 0 < _root_.GD.N0232.N0720.N1373.d004631 p x :=
    _root_.GD.N0232.N0720.N1376.d002900 p.1 p.2.2 hx.1 hx.2 (x 0) (x 2)
  have hs : Function.support (fun p : _root_.GD.N0232.N0720.N1373.d004629 ↦ _root_.GD.N0232.N0720.N1373.d004631 p x) = univ := by
    exact eq_univ_of_forall fun p ↦ (hp p).ne'
  unfold _root_.GD.N0232.N0720.N1373.d004643
  rw [integral_pos_iff_support_of_nonneg (fun p ↦ (hp p).le) hi, hs, measure_univ]
  exact zero_lt_one

theorem d020178
    {ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629} {μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629}
    (hlim : Tendsto ν atTop (𝓝 μ)) (hmoment : _root_.GD.N0232.N0720.N1394.d020172 ν)
    {x : _root_.GD.N0232.N0720.N1394.d020167} (hx : x ∈ _root_.GD.N0232.N0720.N1394.d020169) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1373.d004645 (ν j : Measure _root_.GD.N0232.N0720.N1373.d004629) x) atTop
      (𝓝 (_root_.GD.N0232.N0720.N1373.d004645 (μ : Measure _root_.GD.N0232.N0720.N1373.d004629) x)) := by
  have hK := (_root_.GD.N0232.N0720.N1394.d020174 hlim hmoment 5 0
    (φ := fun _ ↦ 1) continuous_const hx).div_const (8 : ℝ)
  have hL := (_root_.GD.N0232.N0720.N1394.d020174 hlim hmoment 4 1
    (φ := fun _ ↦ 1) continuous_const hx).div_const (8 : ℝ)
  simp only [← _root_.GD.N0232.N0720.N1394.d020175] at hK
  simp only [← _root_.GD.N0232.N0720.N1394.d020176] at hL
  exact hL.div hK (_root_.GD.N0232.N0720.N1394.d020177 μ (_root_.GD.N0232.N0720.N1394.d020173 hlim hmoment) hx).ne'



theorem d020179
    {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) :
    ∃ μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629,
      _root_.GD.N0232.N0720.N1382.d004657 (μ : Measure _root_.GD.N0232.N0720.N1373.d004629) ∧
      (∀ᵐ x ∂(volume : Measure _root_.GD.N0232.N0720.N1394.d020167), x ∈ _root_.GD.N0232.N0720.N1394.d020169 →
        _root_.GD.N0232.N0720.N1373.d004645 (μ : Measure _root_.GD.N0232.N0720.N1373.d004629) x =
          _root_.GD.N0232.N0720.N1401.d020150 (_root_.GD.N0232.N0720.N1398.d019601 d) x) := by
  obtain ⟨ν, hmoment, hraw⟩ := _root_.GD.N0232.N0720.N1391.d020166 hd
  obtain ⟨B, hB⟩ := hmoment (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨μ, ψ, hψ, hlim⟩ :=
    _root_.GD.N0232.N0720.N1297.d002710 ν (by norm_num : (0 : ℝ) < 1 / 4) hB
  have hsub : _root_.GD.N0232.N0720.N1394.d020172 (ν ∘ ψ) := by
    intro β hβ hhalf
    obtain ⟨C, hC⟩ := hmoment β hβ hhalf
    exact ⟨C, fun j ↦ hC (ψ j)⟩
  refine ⟨μ, _root_.GD.N0232.N0720.N1394.d020173 hlim hsub, ?_⟩
  filter_upwards [hraw] with x hx
  intro hphysical
  exact tendsto_nhds_unique (_root_.GD.N0232.N0720.N1394.d020178 hlim hsub hphysical)
    (hx.comp hψ.tendsto_atTop)

end
end GD.N0232.N0720.N1394

#print axioms _root_.GD.N0232.N0720.N1394.d020174
#print axioms _root_.GD.N0232.N0720.N1394.d020178
#print axioms _root_.GD.N0232.N0720.N1394.d020179
