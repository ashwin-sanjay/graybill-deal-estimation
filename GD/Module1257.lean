import GD.Module1225
import GD.Module1256
import GD.Module1246
import GD.Module1232











open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1343

open _root_.GD.N0232.N0720.N1315 _root_.GD.N0232.N0720.N1323
open _root_.GD.N0232.N0720.N1382 _root_.GD.N0232.N0720.N1297
open _root_.GD.N0232.N0720.N1394

noncomputable section

abbrev d020318 := _root_.GD.N0232.N0720.N1315.d019832
abbrev d020319 := _root_.GD.N0232.N0720.N1315.d019833

def d020320 (d : ℕ) (ν : Measure _root_.GD.N0232.N0720.N1343.d020318) (x : _root_.GD.N0232.N0720.N1343.d020319) : ℝ :=
  (∫ p, _root_.GD.N0232.N0720.N1315.d019849 d p x ∂ν) / (∫ p, _root_.GD.N0232.N0720.N1315.d019848 d p x ∂ν)

theorem d020321 (d : ℕ) (p : _root_.GD.N0232.N0720.N1343.d020318) (x : _root_.GD.N0232.N0720.N1343.d020319) :
    _root_.GD.N0232.N0720.N1315.d019848 d p x = _root_.GD.N0232.N0720.N1382.d004668 (d + 2) 0 (fun _ ↦ 1) x p := by
  simp [_root_.GD.N0232.N0720.N1315.d019848, _root_.GD.N0232.N0720.N1382.d004668, _root_.GD.N0232.N0720.N1382.d004654, _root_.GD.N0232.N0720.N1382.d004655]

theorem d020322 (d : ℕ) (p : _root_.GD.N0232.N0720.N1343.d020318) (x : _root_.GD.N0232.N0720.N1343.d020319) :
    _root_.GD.N0232.N0720.N1315.d019849 d p x = _root_.GD.N0232.N0720.N1382.d004668 (d + 1) 1 (fun _ ↦ 1) x p := by
  simp [_root_.GD.N0232.N0720.N1315.d019849, _root_.GD.N0232.N0720.N1382.d004668, _root_.GD.N0232.N0720.N1382.d004654, _root_.GD.N0232.N0720.N1382.d004655]

theorem d020323 (d : ℕ) (ν : Measure _root_.GD.N0232.N0720.N1343.d020318) (x : _root_.GD.N0232.N0720.N1343.d020319) :
    _root_.GD.N0232.N0720.N1343.d020320 d ν x = _root_.GD.N0232.N0720.N1323.d020304 (d + 1) ν x / _root_.GD.N0232.N0720.N1323.d020303 (d + 1) ν x := by
  simp only [_root_.GD.N0232.N0720.N1343.d020320, _root_.GD.N0232.N0720.N1343.d020321,
    _root_.GD.N0232.N0720.N1343.d020322, _root_.GD.N0232.N0720.N1323.d020303, _root_.GD.N0232.N0720.N1323.d020304,
    _root_.GD.N0232.N0720.N1386.d004705, Nat.add_assoc]

theorem d020324 (d : ℕ)
    {ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1343.d020318} {μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1343.d020318}
    (hlim : Tendsto ν atTop (𝓝 μ)) (hmoment : _root_.GD.N0232.N0720.N1394.d020172 ν)
    {x : _root_.GD.N0232.N0720.N1343.d020319} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1343.d020320 d (ν j : Measure _root_.GD.N0232.N0720.N1343.d020318) x) atTop
      (𝓝 (_root_.GD.N0232.N0720.N1343.d020320 d (μ : Measure _root_.GD.N0232.N0720.N1343.d020318) x)) := by
  have hK := _root_.GD.N0232.N0720.N1394.d020174 hlim hmoment (d + 2) 0
    (φ := fun _ ↦ 1) continuous_const hx
  have hL := _root_.GD.N0232.N0720.N1394.d020174 hlim hmoment (d + 1) 1
    (φ := fun _ ↦ 1) continuous_const hx
  have hpos := _root_.GD.N0232.N0720.N1323.d020307 (d + 1)
    (μ : Measure _root_.GD.N0232.N0720.N1343.d020318) (_root_.GD.N0232.N0720.N1394.d020173 hlim hmoment) hx
  have hne : (∫ p, _root_.GD.N0232.N0720.N1382.d004668 (d + 2) 0 (fun _ ↦ 1) x p
      ∂(μ : Measure _root_.GD.N0232.N0720.N1343.d020318)) ≠ 0 := by
    simpa only [_root_.GD.N0232.N0720.N1323.d020303, _root_.GD.N0232.N0720.N1386.d004705,
      Nat.add_assoc] using hpos.ne'
  simpa only [_root_.GD.N0232.N0720.N1343.d020320, _root_.GD.N0232.N0720.N1343.d020321,
    _root_.GD.N0232.N0720.N1343.d020322, Pi.div_def] using hL.div hK hne




theorem d020325 (d : ℕ)
    {X : Type*} [MeasurableSpace X] (ρ : Measure X) (chart : X → _root_.GD.N0232.N0720.N1343.d020319) (f : X → ℝ)
    (ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1343.d020318) (hmoment : _root_.GD.N0232.N0720.N1394.d020172 ν)
    (hraw : ∀ᵐ x ∂ρ,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1343.d020320 d (ν j : Measure _root_.GD.N0232.N0720.N1343.d020318) (chart x))
        atTop (𝓝 (f x))) :
    ∃ μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1343.d020318,
      _root_.GD.N0232.N0720.N1382.d004657 (μ : Measure _root_.GD.N0232.N0720.N1343.d020318) ∧
      (∀ᵐ x ∂ρ, chart x ∈ _root_.GD.N0232.N0720.N1382.d004652 →
        _root_.GD.N0232.N0720.N1343.d020320 d (μ : Measure _root_.GD.N0232.N0720.N1343.d020318) (chart x) = f x) := by
  obtain ⟨B, hB⟩ := hmoment (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨μ, ψ, hψ, hlim⟩ :=
    _root_.GD.N0232.N0720.N1297.d002710 ν
      (by norm_num : (0 : ℝ) < 1 / 4) hB
  have hsub : _root_.GD.N0232.N0720.N1394.d020172 (ν ∘ ψ) := by
    intro β hβ hhalf
    obtain ⟨C, hC⟩ := hmoment β hβ hhalf
    exact ⟨C, fun j ↦ hC (ψ j)⟩
  refine ⟨μ, _root_.GD.N0232.N0720.N1394.d020173 hlim hsub, ?_⟩
  filter_upwards [hraw] with x hx
  intro hphysical
  exact tendsto_nhds_unique (_root_.GD.N0232.N0720.N1343.d020324 d hlim hsub hphysical)
    (hx.comp hψ.tendsto_atTop)



theorem d020326
    (m n d : ℕ) (hdim : m + n = d + 1) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {δ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n δ) :
    ∃ (g : ℝ × ℝ → ℝ) (μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1343.d020318),
      Measurable g ∧ (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        δ =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ]
          _root_.GD.N0232.N0720.N1425.d014719 m n g) ∧
      _root_.GD.N0232.N0720.N1382.d004657 (μ : Measure _root_.GD.N0232.N0720.N1343.d020318) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
        _root_.GD.N0232.N0720.N1315.d019850 m n d hdim x ∈ _root_.GD.N0232.N0720.N1382.d004652 →
        _root_.GD.N0232.N0720.N1343.d020320 d (μ : Measure _root_.GD.N0232.N0720.N1343.d020318)
            (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x) =
          _root_.GD.N0232.N0720.N1329.d019671 m n d hdim g x) := by
  obtain ⟨g, ν, hg, hb, hrep, hmoment, hraw⟩ :=
    _root_.GD.N0232.N0720.N1321.d020079
      m n d hdim hm hn hd
  have hraw' : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1343.d020320 d (ν j : Measure _root_.GD.N0232.N0720.N1343.d020318)
        (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x))
        atTop (𝓝 (_root_.GD.N0232.N0720.N1329.d019671 m n d hdim g x)) := by
    exact hraw
  obtain ⟨μ, hμ, hpost⟩ := _root_.GD.N0232.N0720.N1343.d020325 d volume
    (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim)
    (_root_.GD.N0232.N0720.N1329.d019671 m n d hdim g) ν hmoment hraw'
  exact ⟨g, μ, hg, hb, hrep, hμ, hpost⟩

end
end GD.N0232.N0720.N1343

#print axioms _root_.GD.N0232.N0720.N1343.d020323
#print axioms _root_.GD.N0232.N0720.N1343.d020324
#print axioms _root_.GD.N0232.N0720.N1343.d020325
#print axioms _root_.GD.N0232.N0720.N1343.d020326
