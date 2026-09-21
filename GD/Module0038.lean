import GD.Module0036
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic















open Filter MeasureTheory Set
open scoped BigOperators Topology NNReal ENNReal

namespace GD
namespace N0230
namespace N0674

noncomputable section

set_option linter.unusedSectionVars false





theorem d000452
    {x defect mass A cstar cshare : ℝ}
    (hx : 0 < x) (hxA : x < A)
    (hcstar : 0 < cstar) (hcshare : 0 < cshare)
    (hxi : cstar * defect ≤ x)
    (hcapacity : A / (1 + cshare * mass) ≤ x)
    (hmass : 0 ≤ mass) :
    defect ≤ x / cstar ∧
      (A - x) / (cshare * x) ≤ mass := by
  constructor
  · exact (le_div_iff₀ hcstar).2 (by simpa [mul_comm] using hxi)
  · have hdenom : 0 < 1 + cshare * mass := by positivity
    have hcapmul := (div_le_iff₀ hdenom).mp hcapacity
    have hcx : 0 < cshare * x := mul_pos hcshare hx
    apply (div_le_iff₀ hcx).2
    nlinarith




theorem d000453
    {total physical capacity cstar defect : ℝ}
    (hcstar : 0 ≤ cstar) (hdefect : 0 ≤ defect)
    (hdecomposition : total = physical + cstar * defect)
    (hcapacity : capacity ≤ physical) :
    capacity ≤ total := by
  rw [hdecomposition]
  exact hcapacity.trans (le_add_of_nonneg_right (mul_nonneg hcstar hdefect))




theorem d000454
    {x physical defect mass A cstar cshare : ℝ}
    (hx : 0 < x) (hxA : x < A)
    (hphysical : 0 ≤ physical) (hdefect : 0 ≤ defect)
    (hcstar : 0 < cstar) (hcshare : 0 < cshare)
    (hdecomposition : x = physical + cstar * defect)
    (hcapacity : A / (1 + cshare * mass) ≤ physical)
    (hmass : 0 ≤ mass) :
    defect ≤ x / cstar ∧
      (A - x) / (cshare * x) ≤ mass := by
  have hxi : cstar * defect ≤ x := by
    rw [hdecomposition]
    linarith
  have hcapacityTotal : A / (1 + cshare * mass) ≤ x :=
    _root_.GD.N0230.N0674.d000453 hcstar.le hdefect
      hdecomposition hcapacity
  exact _root_.GD.N0230.N0674.d000452 hx hxA hcstar hcshare
    hxi hcapacityTotal hmass



theorem d000455
    {gapIntegral budget defect comparisonEnergy referenceRisk : ℝ}
    (hidentity :
      gapIntegral = budget + defect - comparisonEnergy - referenceRisk)
    (hcomparisonEnergy : 0 ≤ comparisonEnergy)
    (hreferenceRisk : 0 ≤ referenceRisk) :
    gapIntegral ≤ budget + defect := by
  linarith


theorem d000456
    {interiorMass gapIntegral gapFloor : ℝ}
    (hgapFloor : 0 < gapFloor)
    (hinteriorMass : 0 ≤ interiorMass)
    (hweighted : gapFloor * interiorMass ≤ gapIntegral) :
    interiorMass ≤ gapIntegral / gapFloor := by
  exact (le_div_iff₀ hgapFloor).2 (by simpa [mul_comm] using hweighted)


theorem d000457
    {x mass interiorMass A cstar cshare budget gapFloor : ℝ}
    (hx : 0 < x) (hxA : x < A)
    (hcstar : 0 < cstar) (hcshare : 0 < cshare)
    (hgapFloor : 0 < gapFloor)
    (hbudget : 0 ≤ budget)
    (hmass : 0 ≤ mass) (hinteriorMass : 0 ≤ interiorMass)
    (hmassLower : (A - x) / (cshare * x) ≤ mass)
    (hinteriorUpper :
      interiorMass ≤ (budget + x / cstar) / gapFloor) :
    interiorMass / mass ≤
      cshare * x * (budget + x / cstar) /
        (gapFloor * (A - x)) := by
  have hA : 0 < A - x := sub_pos.mpr hxA
  have hlowerPos : 0 < (A - x) / (cshare * x) := by positivity
  have hmassPos : 0 < mass := lt_of_lt_of_le hlowerPos hmassLower
  have hupperNonneg : 0 ≤ (budget + x / cstar) / gapFloor := by
    positivity
  calc
    interiorMass / mass ≤
        ((budget + x / cstar) / gapFloor) / mass :=
      div_le_div_of_nonneg_right hinteriorUpper hmassPos.le
    _ ≤ ((budget + x / cstar) / gapFloor) /
        ((A - x) / (cshare * x)) :=
      div_le_div_of_nonneg_left hupperNonneg hlowerPos hmassLower
    _ = cshare * x * (budget + x / cstar) /
        (gapFloor * (A - x)) := by
      field_simp [hcstar.ne', hcshare.ne', hgapFloor.ne', hA.ne', hx.ne']



variable {I : Type*} [Fintype I]



def d000458 (weight : I → ℝ) : ℝ :=
  ∑ i, weight i


def d000459 (weight q : I → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ i, (weight i / 2) * (f (q i) + f (1 - q i))


def d000460 (weight q : I → ℝ) (f : ℝ → ℝ) : ℝ :=
  _root_.GD.N0230.N0674.d000459 weight q f / _root_.GD.N0230.N0674.d000458 weight


def d000461 (f : ℝ → ℝ) : ℝ :=
  (f 0 + f 1) / 2


def d000462 (x : ℝ) : ℝ :=
  min x (1 - x)

theorem d000463 {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ _root_.GD.N0230.N0674.d000462 x := by
  exact le_min hx.1 (sub_nonneg.mpr hx.2)



theorem d000464
    {f : ℝ → ℝ} {q L : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    |(f q + f (1 - q)) / 2 - _root_.GD.N0230.N0674.d000461 f| ≤
      L * _root_.GD.N0230.N0674.d000462 q := by
  by_cases hhalf : q ≤ 1 / 2
  · have hq0 : 0 ≤ q := hq.1
    have hq1 : 0 ≤ 1 - q := sub_nonneg.mpr hq.2
    have hmin : _root_.GD.N0230.N0674.d000462 q = q := by
      rw [_root_.GD.N0230.N0674.d000462, min_eq_left (by linarith)]
    have h0 := hlip q 0
    have h1 := hlip (1 - q) 1
    have habs0 : |q - 0| = q := by simpa using abs_of_nonneg hq0
    have habs1 : |(1 - q) - 1| = q := by
      rw [show (1 - q) - 1 = -q by ring, abs_neg, abs_of_nonneg hq0]
    rw [habs0] at h0
    rw [habs1] at h1
    rw [hmin]
    have htri :
        |(f q - f 0) + (f (1 - q) - f 1)| ≤
          |f q - f 0| + |f (1 - q) - f 1| := abs_add_le _ _
    have htwo :
        |(f q - f 0) + (f (1 - q) - f 1)| ≤ 2 * (L * q) := by
      linarith
    rw [_root_.GD.N0230.N0674.d000461]
    have hid :
        (f q + f (1 - q)) / 2 - (f 0 + f 1) / 2 =
          ((f q - f 0) + (f (1 - q) - f 1)) / 2 := by ring
    rw [hid, abs_div]
    norm_num
    linarith
  · have hqle : 1 - q ≤ q := by linarith
    have hqright : 0 ≤ 1 - q := sub_nonneg.mpr hq.2
    have hmin : _root_.GD.N0230.N0674.d000462 q = 1 - q := by
      simp only [_root_.GD.N0230.N0674.d000462, min_eq_right hqle]
    have h0 := hlip q 1
    have h1 := hlip (1 - q) 0
    have habs0 : |q - 1| = 1 - q := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have habs1 : |(1 - q) - 0| = 1 - q := by
      simpa using abs_of_nonneg hqright
    rw [habs0] at h0
    rw [habs1] at h1
    rw [hmin]
    have htri :
        |(f q - f 1) + (f (1 - q) - f 0)| ≤
          |f q - f 1| + |f (1 - q) - f 0| := abs_add_le _ _
    have htwo :
        |(f q - f 1) + (f (1 - q) - f 0)| ≤
          2 * (L * (1 - q)) := by
      linarith
    rw [_root_.GD.N0230.N0674.d000461]
    have hid :
        (f q + f (1 - q)) / 2 - (f 0 + f 1) / 2 =
          ((f q - f 1) + (f (1 - q) - f 0)) / 2 := by ring
    rw [hid, abs_div]
    norm_num
    linarith


theorem d000465
    (weight q : I → ℝ) (f : ℝ → ℝ) (L : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hmass : 0 < _root_.GD.N0230.N0674.d000458 weight) :
    |_root_.GD.N0230.N0674.d000460 weight q f - _root_.GD.N0230.N0674.d000461 f| ≤
      L * (∑ i, weight i * _root_.GD.N0230.N0674.d000462 (q i)) /
        _root_.GD.N0230.N0674.d000458 weight := by
  let pairError : I → ℝ := fun i ↦
    (f (q i) + f (1 - q i)) / 2 - _root_.GD.N0230.N0674.d000461 f
  have hrewrite :
      _root_.GD.N0230.N0674.d000460 weight q f - _root_.GD.N0230.N0674.d000461 f =
        (∑ i, weight i * pairError i) / _root_.GD.N0230.N0674.d000458 weight := by
    rw [_root_.GD.N0230.N0674.d000460]
    rw [show _root_.GD.N0230.N0674.d000459 weight q f / _root_.GD.N0230.N0674.d000458 weight - _root_.GD.N0230.N0674.d000461 f =
        (_root_.GD.N0230.N0674.d000459 weight q f -
          _root_.GD.N0230.N0674.d000461 f * _root_.GD.N0230.N0674.d000458 weight) / _root_.GD.N0230.N0674.d000458 weight by
      field_simp [hmass.ne']]
    congr 1
    simp only [_root_.GD.N0230.N0674.d000459, _root_.GD.N0230.N0674.d000458, pairError]
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hrewrite, abs_div, abs_of_pos hmass]
  apply (div_le_div_iff_of_pos_right hmass).2
  calc
    |∑ i, weight i * pairError i| ≤
        ∑ i, |weight i * pairError i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, weight i * |pairError i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hweight i)]
    _ ≤ ∑ i, weight i * (L * _root_.GD.N0230.N0674.d000462 (q i)) := by
      exact Finset.sum_le_sum fun i hi ↦
        mul_le_mul_of_nonneg_left
          (_root_.GD.N0230.N0674.d000464 (hq i) hL hlip)
          (hweight i)
    _ = L * ∑ i, weight i * _root_.GD.N0230.N0674.d000462 (q i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring




theorem d000466
    (weight q : ℕ → I → ℝ)
    (hweight : ∀ n i, 0 ≤ weight n i)
    (hq : ∀ n i, q n i ∈ Set.Icc (0 : ℝ) 1)
    (hmass : ∀ n, 0 < _root_.GD.N0230.N0674.d000458 (weight n))
    (hmoment : Tendsto
      (fun n ↦ (∑ i, weight n i * _root_.GD.N0230.N0674.d000462 (q n i)) /
        _root_.GD.N0230.N0674.d000458 (weight n)) atTop (nhds 0))
    (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    Tendsto (fun n ↦ _root_.GD.N0230.N0674.d000460 (weight n) (q n) f)
      atTop (nhds (_root_.GD.N0230.N0674.d000461 f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n ↦ norm_nonneg _
  · exact Filter.Eventually.of_forall fun n ↦ by
      simpa [Real.norm_eq_abs] using
        _root_.GD.N0230.N0674.d000465
          (weight n) (q n) f L (hweight n) (hq n) hL hlip (hmass n)
  · convert hmoment.const_mul L using 1
    · funext n
      ring
    · simp




theorem d000467
    (N : ℕ → ℕ)
    (weight q : (n : ℕ) → Fin (N n) → ℝ)
    (hweight : ∀ n i, 0 ≤ weight n i)
    (hq : ∀ n i, q n i ∈ Set.Icc (0 : ℝ) 1)
    (hmass : ∀ n, 0 < _root_.GD.N0230.N0674.d000458 (weight n))
    (hmoment : Tendsto
      (fun n ↦
        (∑ i, weight n i * _root_.GD.N0230.N0674.d000462 (q n i)) /
          _root_.GD.N0230.N0674.d000458 (weight n)) atTop (nhds 0))
    (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    Tendsto (fun n ↦ _root_.GD.N0230.N0674.d000460 (weight n) (q n) f)
      atTop (nhds (_root_.GD.N0230.N0674.d000461 f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n ↦ norm_nonneg _
  · exact Filter.Eventually.of_forall fun n ↦ by
      simpa [Real.norm_eq_abs] using
        _root_.GD.N0230.N0674.d000465
          (weight n) (q n) f L (hweight n) (hq n) hL hlip (hmass n)
  · convert hmoment.const_mul L using 1
    · funext n
      ring
    · simp




def d000468 (budget gap : ℝ) : ℝ :=
  budget / (2 * gap)

theorem d000469
    {budget gap : ℝ} (hgap : gap ≠ 0) :
    _root_.GD.N0230.N0674.d000468 budget gap * gap = budget / 2 := by
  unfold _root_.GD.N0230.N0674.d000468
  field_simp

theorem d000470
    {budget gap : ℝ} (hbudget : budget ≠ 0) (hgap : gap ≠ 0) :
    1 / _root_.GD.N0230.N0674.d000468 budget gap = 2 * gap / budget := by
  unfold _root_.GD.N0230.N0674.d000468
  field_simp




theorem d000471
    {gap : ℕ → ℝ} {budget : ℝ}
    (hbudget : budget ≠ 0)
    (hgap : ∀ n, gap n ≠ 0)
    (hgapZero : Tendsto gap atTop (nhds 0)) :
    Tendsto (fun n ↦ 1 / _root_.GD.N0230.N0674.d000468 budget (gap n))
      atTop (nhds 0) := by
  have hscale := hgapZero.const_mul (2 / budget)
  convert hscale using 1
  · funext n
    rw [_root_.GD.N0230.N0674.d000470 hbudget (hgap n)]
    ring
  · ring

end

end N0674
end N0230
end GD

#print axioms _root_.GD.N0230.N0674.d000452
#print axioms _root_.GD.N0230.N0674.d000454
#print axioms _root_.GD.N0230.N0674.d000457
#print axioms _root_.GD.N0230.N0674.d000465
#print axioms _root_.GD.N0230.N0674.d000466
#print axioms _root_.GD.N0230.N0674.d000467
#print axioms _root_.GD.N0230.N0674.d000471
