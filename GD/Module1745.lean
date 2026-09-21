import GD.Module0503
import GD.Module1270
import GD.Module1271

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0212.N0475

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0990 _root_.GD.N0232.N0719.N0994
open _root_.GD.N0232.N0719.N0995 _root_.GD.N0232.N0719.N0993
open _root_.GD.N0232.N0719.N0989 (d011338)
open _root_.GD.N0232.N0719.N0983
open _root_.GD.N0232.N0720.N1382
  (d004663 d004664 d004665)
open _root_.GD.N0212.N0468 _root_.GD.N0212.N0469

noncomputable section
variable {k : ℕ}

def d028980 (ν : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k)) : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 / 2 → ∃ B : ℝ, _root_.GD.N0212.N0468.d007648 ν β B

theorem d028981
    {ν : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k)} {μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k)}
    (hlim : Tendsto ν atTop (𝓝 μ)) (hmoment : _root_.GD.N0212.N0475.d028980 ν) :
    _root_.GD.N0232.N0719.N0994.d011375 (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) := by
  intro β hβ hhalf
  obtain ⟨B, hB⟩ := hmoment β hβ hhalf
  exact (_root_.GD.N0212.N0468.d007654 hlim hB).1

theorem d028982
    {ν : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k)} {μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k)}
    (hlim : Tendsto ν atTop (𝓝 μ)) (hmoment : _root_.GD.N0212.N0475.d028980 ν)
    (n m : ℕ) {φ : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ} (hφ : Continuous φ)
    {x : _root_.GD.N0232.N0719.N0990.d020497 k} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) :
    Tendsto (fun j => ∫ p, _root_.GD.N0232.N0719.N0994.d011381 n m φ x p ∂(ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)))
      atTop (𝓝 (∫ p, _root_.GD.N0232.N0719.N0994.d011381 n m φ x p ∂(μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)))) := by
  obtain ⟨δ, R, hδ, hR, hbox⟩ := _root_.GD.N0232.N0719.N0994.d011380 hx
  let α : ℝ := (_root_.GD.N0232.N0720.N1382.d004663 δ R + 1 / 2) / 2
  let β : ℝ := (α + 1 / 2) / 2
  have hrate : _root_.GD.N0232.N0720.N1382.d004663 δ R < 1 / 2 := _root_.GD.N0232.N0720.N1382.d004665 hδ
  have hrate0 : 0 < _root_.GD.N0232.N0720.N1382.d004663 δ R := _root_.GD.N0232.N0720.N1382.d004664 hδ hR
  have hα : _root_.GD.N0232.N0720.N1382.d004663 δ R < α := by dsimp [α]; linarith
  have hαβ : α < β := by dsimp [α, β]; linarith
  have hβ : 0 < β := by dsimp [α, β]; linarith
  have hβhalf : β < 1 / 2 := by dsimp [α, β]; linarith
  obtain ⟨C, hC, hb⟩ := _root_.GD.N0232.N0719.N0994.d011383 n m hφ hδ hR hα
  obtain ⟨B, hB⟩ := hmoment β hβ hβhalf
  exact _root_.GD.N0212.N0469.d007663 hlim hB
    (_root_.GD.N0232.N0719.N0994.d011382 n m hφ hx) hC.le hβ hαβ
    (hb x (mem_of_mem_nhds hbox))

def d028983 (d : ℕ) (ν : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) (x : _root_.GD.N0232.N0719.N0990.d020497 k) : ℝ :=
  (∫ p, _root_.GD.N0232.N0719.N0990.d020511 (d := d) p x ∂ν) / (∫ p, _root_.GD.N0232.N0719.N0990.d020510 (d := d) p x ∂ν)

theorem d028984 (d : ℕ) (p : _root_.GD.N0232.N0719.N0990.d020496 k) (x : _root_.GD.N0232.N0719.N0990.d020497 k) :
    _root_.GD.N0232.N0719.N0990.d020510 (d := d) p x = _root_.GD.N0232.N0719.N0994.d011381 (d + 2) 0 (fun _ => 1) x p := by
  simp only [_root_.GD.N0232.N0719.N0990.d020510, _root_.GD.N0232.N0719.N0994.d011381, pow_zero, mul_one, one_mul]
  rfl

theorem d028985 (d : ℕ) (p : _root_.GD.N0232.N0719.N0990.d020496 k) (x : _root_.GD.N0232.N0719.N0990.d020497 k) :
    _root_.GD.N0232.N0719.N0990.d020511 (d := d) p x = _root_.GD.N0232.N0719.N0994.d011381 (d + 1) 1 (fun _ => 1) x p := by
  simp only [_root_.GD.N0232.N0719.N0990.d020511, _root_.GD.N0232.N0719.N0994.d011381, pow_one, mul_one]
  rfl

theorem d028986 (d : ℕ) (ν : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) (x : _root_.GD.N0232.N0719.N0990.d020497 k) :
    _root_.GD.N0212.N0475.d028983 d ν x = _root_.GD.N0232.N0719.N0993.d020541 (d + 1) ν x / _root_.GD.N0232.N0719.N0993.d020540 (d + 1) ν x := by
  simp only [_root_.GD.N0212.N0475.d028983, _root_.GD.N0212.N0475.d028984, _root_.GD.N0212.N0475.d028985,
    _root_.GD.N0232.N0719.N0993.d020540, _root_.GD.N0232.N0719.N0993.d020541, _root_.GD.N0232.N0719.N0995.d011389, Nat.add_assoc]

theorem d028987 (d : ℕ)
    {ν : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k)} {μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k)}
    (hlim : Tendsto ν atTop (𝓝 μ)) (hmoment : _root_.GD.N0212.N0475.d028980 ν)
    {x : _root_.GD.N0232.N0719.N0990.d020497 k} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) :
    Tendsto (fun j => _root_.GD.N0212.N0475.d028983 d (ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) x) atTop
      (𝓝 (_root_.GD.N0212.N0475.d028983 d (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) x)) := by
  have hK := _root_.GD.N0212.N0475.d028982 hlim hmoment (d + 2) 0
    (φ := fun _ => 1) continuous_const hx
  have hL := _root_.GD.N0212.N0475.d028982 hlim hmoment (d + 1) 1
    (φ := fun _ => 1) continuous_const hx
  have hpos := _root_.GD.N0232.N0719.N0993.d020542 (d + 1) (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k))
    (_root_.GD.N0212.N0475.d028981 hlim hmoment) hx
  have hne : (∫ p, _root_.GD.N0232.N0719.N0994.d011381 (d + 2) 0 (fun _ => 1) x p
      ∂(μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k))) ≠ 0 := by
    simpa only [_root_.GD.N0232.N0719.N0993.d020540, _root_.GD.N0232.N0719.N0995.d011389, Nat.add_assoc] using hpos.ne'
  simpa only [_root_.GD.N0212.N0475.d028983, _root_.GD.N0212.N0475.d028984,
    _root_.GD.N0212.N0475.d028985, Pi.div_def] using hL.div hK hne



theorem d028988 (d : ℕ)
    {X : Type*} [MeasurableSpace X] (ρ : Measure X) (chart : X → _root_.GD.N0232.N0719.N0990.d020497 k) (f : X → ℝ)
    (ν : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k)) (hmoment : _root_.GD.N0212.N0475.d028980 ν)
    (hraw : ∀ᵐ x ∂ρ, Tendsto
      (fun j => _root_.GD.N0212.N0475.d028983 d (ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) (chart x))
        atTop (𝓝 (f x))) :
    ∃ μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k),
      _root_.GD.N0232.N0719.N0994.d011375 (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) ∧
      (∀ᵐ x ∂ρ, chart x ∈ _root_.GD.N0232.N0719.N0989.d011338 →
        _root_.GD.N0212.N0475.d028983 d (μ : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) (chart x) = f x) := by
  obtain ⟨B, hB⟩ := hmoment (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨μ, ψ, hψ, hlim⟩ := _root_.GD.N0212.N0468.d007652 ν
    (by norm_num : (0 : ℝ) < 1 / 4) hB
  have hsub : _root_.GD.N0212.N0475.d028980 (ν ∘ ψ) := by
    intro β hβ hhalf
    obtain ⟨C, hC⟩ := hmoment β hβ hhalf
    exact ⟨C, fun j => hC (ψ j)⟩
  refine ⟨μ, _root_.GD.N0212.N0475.d028981 hlim hsub, ?_⟩
  filter_upwards [hraw] with x hx
  intro hphysical
  exact tendsto_nhds_unique (_root_.GD.N0212.N0475.d028987 d hlim hsub hphysical)
    (hx.comp hψ.tendsto_atTop)

end
end GD.N0212.N0475

#print axioms _root_.GD.N0212.N0475.d028982
#print axioms _root_.GD.N0212.N0475.d028988
