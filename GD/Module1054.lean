import GD.Module1040
import GD.Module1053
import Mathlib.Tactic

















open MeasureTheory Set Topology
open scoped ENNReal

namespace GD.N0232.N0720.N1088

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1367

noncomputable local instance d016883 :
    MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168 := borel _root_.GD.N0232.N0720.N1080.d014168

local instance d016884 : BorelSpace _root_.GD.N0232.N0720.N1080.d014168 := ⟨rfl⟩


def d016885 : Set _root_.GD.N0232.N0720.N1080.d014168 :=
  {theta | theta.scale₁ = theta.scale₂}

theorem d016886 : IsClosed _root_.GD.N0232.N0720.N1088.d016885 := by
  exact isClosed_eq _root_.GD.N0232.N0720.N1499.d014999 _root_.GD.N0232.N0720.N1499.d015000


def d016887 : _root_.GD.N0232.N0720.N1080.d014168 where
  location := 0
  scale₁ := 1
  scale₂ := 2
  scale₁_pos := by norm_num
  scale₂_pos := by norm_num

theorem d016888 :
    _root_.GD.N0232.N0720.N1088.d016887 ∉ _root_.GD.N0232.N0720.N1088.d016885 := by
  norm_num [_root_.GD.N0232.N0720.N1088.d016887, _root_.GD.N0232.N0720.N1088.d016885]




theorem d016889
    {Xi : Type*} (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (hscale : ∀ xi, chart xi ∈ _root_.GD.N0232.N0720.N1088.d016885) :
    ¬ Function.Surjective chart := by
  intro hsurj
  obtain ⟨xi, hxi⟩ := hsurj _root_.GD.N0232.N0720.N1088.d016887
  apply _root_.GD.N0232.N0720.N1088.d016888
  simpa only [hxi] using hscale xi

theorem d016890 :
    _root_.GD.N0232.N0720.N1080.d014169 ∈ _root_.GD.N0232.N0720.N1088.d016885 := by
  rfl

theorem d016891
    (N : ℝ) (hN : 3 ≤ N) (mu : ℝ) :
    _root_.GD.N0232.N0720.N1367.d016856 N hN mu ∈ _root_.GD.N0232.N0720.N1088.d016885 := by
  rfl

theorem d016892
    (N : ℝ) (hN : 3 ≤ N) (mu : ℝ) :
    _root_.GD.N0232.N0720.N1367.d016857 N hN mu ∈ _root_.GD.N0232.N0720.N1088.d016885 := by
  rfl

theorem d016893
    {Alpha : Type*} [MeasurableSpace Alpha]
    (mu : Measure Alpha) (f : Alpha → _root_.GD.N0232.N0720.N1080.d014168)
    (hf : Measurable f) (hscale : ∀ x, f x ∈ _root_.GD.N0232.N0720.N1088.d016885) :
    mu.map f _root_.GD.N0232.N0720.N1088.d016885ᶜ = 0 := by
  have hmeas : MeasurableSet _root_.GD.N0232.N0720.N1088.d016885ᶜ :=
    _root_.GD.N0232.N0720.N1088.d016886.measurableSet.compl
  rw [Measure.map_apply hf hmeas]
  have hempty : f ⁻¹' _root_.GD.N0232.N0720.N1088.d016885ᶜ = ∅ := by
    ext x
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
    exact not_not_intro (hscale x)
  rw [hempty, measure_empty]



theorem d016894
    {N : ℝ} (hN : 3 ≤ N) :
    _root_.GD.N0232.N0720.N1367.d016868 N hN _root_.GD.N0232.N0720.N1088.d016885ᶜ = 0 := by
  have hmeas : MeasurableSet _root_.GD.N0232.N0720.N1088.d016885ᶜ :=
    _root_.GD.N0232.N0720.N1088.d016886.measurableSet.compl
  have href : Measure.dirac _root_.GD.N0232.N0720.N1080.d014169 _root_.GD.N0232.N0720.N1088.d016885ᶜ = 0 := by
    rw [Measure.dirac_apply' _ hmeas]
    simp [_root_.GD.N0232.N0720.N1088.d016890]
  have hfirst :
      (_root_.GD.N0232.N0720.N1367.d016860 N).map (_root_.GD.N0232.N0720.N1367.d016856 N hN)
          _root_.GD.N0232.N0720.N1088.d016885ᶜ = 0 :=
    _root_.GD.N0232.N0720.N1088.d016893 _ _
      (_root_.GD.N0232.N0720.N1367.d016858 N hN)
      (_root_.GD.N0232.N0720.N1088.d016891 N hN)
  have hsecond :
      (_root_.GD.N0232.N0720.N1367.d016861 N).map (_root_.GD.N0232.N0720.N1367.d016857 N hN)
          _root_.GD.N0232.N0720.N1088.d016885ᶜ = 0 :=
    _root_.GD.N0232.N0720.N1088.d016893 _ _
      (_root_.GD.N0232.N0720.N1367.d016859 N hN)
      (_root_.GD.N0232.N0720.N1088.d016892 N hN)
  unfold _root_.GD.N0232.N0720.N1367.d016868
  rw [Measure.add_apply, Measure.add_apply,
    href, hfirst, hsecond]
  simp




theorem d016895
    (prior : ℕ → Measure _root_.GD.N0232.N0720.N1080.d014168)
    (hzero : ∀ k, prior k _root_.GD.N0232.N0720.N1088.d016885ᶜ = 0) :
    ¬ _root_.GD.N0232.N0720.N1111.d016605 prior := by
  intro hretain
  have hopen : IsOpen _root_.GD.N0232.N0720.N1088.d016885ᶜ := _root_.GD.N0232.N0720.N1088.d016886.isOpen_compl
  have hmem : _root_.GD.N0232.N0720.N1088.d016887 ∈ _root_.GD.N0232.N0720.N1088.d016885ᶜ :=
    _root_.GD.N0232.N0720.N1088.d016888
  obtain ⟨a, ha, N, hN⟩ :=
    hretain _root_.GD.N0232.N0720.N1088.d016887 _root_.GD.N0232.N0720.N1088.d016885ᶜ (hopen.mem_nhds hmem)
  have hbound := hN N le_rfl
  rw [hzero N] at hbound
  simpa using (not_lt_of_ge hbound ha)




theorem d016896
    (N : ℕ → ℝ) (hN : ∀ k, 3 ≤ N k) :
    ¬ _root_.GD.N0232.N0720.N1111.d016605
      (fun k ↦ _root_.GD.N0232.N0720.N1367.d016868 (N k) (hN k)) := by
  apply _root_.GD.N0232.N0720.N1088.d016895
  intro k
  exact _root_.GD.N0232.N0720.N1088.d016894 (hN k)







def d016897
    {Xi : Type*} [TopologicalSpace Xi] [MeasurableSpace Xi]
    (rho : Measure Xi) : Prop :=
  ∀ xi U, U ∈ nhds xi → 0 < rho U







theorem d016898
    {Xi : Type*} [TopologicalSpace Xi] [MeasurableSpace Xi]
    [OpensMeasurableSpace Xi]
    (rho : Measure Xi) [IsFiniteMeasure rho]
    (central : ℕ → Measure Xi)
    (hcentralFinite : ∀ k, IsFiniteMeasure (central k))
    (delta : NNReal) (hdelta : 0 < delta)
    (hrho : _root_.GD.N0232.N0720.N1088.d016897 rho) :
    _root_.GD.N0232.N0720.N1111.d016605
      (fun k ↦ delta • rho + central k) := by
  intro xi U hU
  have hweightedPos : 0 < (delta • rho) U := by
    rw [Measure.coe_nnreal_smul_apply]
    exact ENNReal.mul_pos (by exact_mod_cast hdelta.ne') (hrho xi U hU).ne'
  let a : ℝ := ((delta • rho) U).toReal
  have ha : 0 < a := by
    exact ENNReal.toReal_pos hweightedPos.ne'
      (measure_ne_top (delta • rho) U)
  refine ⟨a, ha, 0, ?_⟩
  intro k hk
  letI : IsFiniteMeasure (central k) := hcentralFinite k
  letI : IsFiniteMeasure (delta • rho + central k) := by infer_instance
  have hmeasure : delta • rho ≤ delta • rho + central k :=
    Measure.le_add_right le_rfl
  exact (ENNReal.toReal_le_toReal
    (measure_ne_top (delta • rho) U)
    (measure_ne_top (delta • rho + central k) U)).2 (hmeasure U)




theorem d016899
    (rho : Measure _root_.GD.N0232.N0720.N1080.d014168) [IsFiniteMeasure rho]
    (delta : NNReal) (hdelta : 0 < delta)
    (hrho : _root_.GD.N0232.N0720.N1088.d016897 rho)
    (N : ℕ → ℝ) (hN : ∀ k, 3 ≤ N k) :
    _root_.GD.N0232.N0720.N1111.d016605
      (fun k ↦ delta • rho + _root_.GD.N0232.N0720.N1367.d016868 (N k) (hN k)) := by
  apply _root_.GD.N0232.N0720.N1088.d016898
    rho (fun k ↦ _root_.GD.N0232.N0720.N1367.d016868 (N k) (hN k))
      (fun k ↦ _root_.GD.N0232.N0720.N1367.d016869 (hN k)) delta hdelta hrho



theorem d016900
    {m₀ m₁ j₀ j₁ : ℝ} (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) :
    (j₀ + j₁) ^ 2 / (m₀ + m₁) ≤
      j₀ ^ 2 / m₀ + j₁ ^ 2 / m₁ := by
  have hm : 0 < m₀ + m₁ := add_pos hm₀ hm₁
  apply (div_le_iff₀ hm).2
  have hprod : 0 < m₀ * m₁ := mul_pos hm₀ hm₁
  rw [show j₀ ^ 2 / m₀ + j₁ ^ 2 / m₁ =
      (m₁ * j₀ ^ 2 + m₀ * j₁ ^ 2) / (m₀ * m₁) by
        field_simp [hm₀.ne', hm₁.ne']]
  rw [show ((m₁ * j₀ ^ 2 + m₀ * j₁ ^ 2) / (m₀ * m₁)) *
      (m₀ + m₁) =
      ((m₀ + m₁) * (m₁ * j₀ ^ 2 + m₀ * j₁ ^ 2)) /
        (m₀ * m₁) by ring]
  rw [le_div_iff₀ hprod]
  nlinarith [sq_nonneg (m₁ * j₀ - m₀ * j₁)]









theorem d016901
    {delta m₀ m₁ j₀ j₁ : ℝ}
    (hdelta : 0 < delta) (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) :
    (j₀ + delta * j₁) ^ 2 / (m₀ + delta * m₁) ≤
      j₀ ^ 2 / m₀ + delta * (j₁ ^ 2 / m₁) := by
  calc
    (j₀ + delta * j₁) ^ 2 / (m₀ + delta * m₁) ≤
        j₀ ^ 2 / m₀ + (delta * j₁) ^ 2 / (delta * m₁) :=
      _root_.GD.N0232.N0720.N1088.d016900 hm₀ (mul_pos hdelta hm₁)
    _ = j₀ ^ 2 / m₀ + delta * (j₁ ^ 2 / m₁) := by
      field_simp [hdelta.ne', hm₁.ne']

end

end GD.N0232.N0720.N1088

#print axioms _root_.GD.N0232.N0720.N1088.d016895
#print axioms _root_.GD.N0232.N0720.N1088.d016889
#print axioms _root_.GD.N0232.N0720.N1088.d016894
#print axioms _root_.GD.N0232.N0720.N1088.d016896
#print axioms _root_.GD.N0232.N0720.N1088.d016898
#print axioms _root_.GD.N0232.N0720.N1088.d016899
#print axioms _root_.GD.N0232.N0720.N1088.d016901
