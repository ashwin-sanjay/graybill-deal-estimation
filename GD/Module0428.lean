import Mathlib






















open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0141

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]




theorem d006682
    (μ y d l e : ℝ) :
    y + l * d - μ = (y + e * d - μ) + d * (l - e) := by
  ring


theorem d006683
    (μ y d l e ε q : ℝ) :
    y + l * d + ε * d * q - μ =
      (y + e * d - μ) + d * (l - e) + ε * d * q := by
  ring


def d006684 (P : Measure Ω) (err : Ω → ℝ) : ℝ :=
  ∫ ω, (err ω) ^ 2 ∂P


def d006685 (U D L : Ω → ℝ) (e : ℝ) : Ω → ℝ :=
  fun ω => U ω + D ω * (L ω - e)


def d006686 (U D L q : Ω → ℝ) (e ε : ℝ) : Ω → ℝ :=
  fun ω => _root_.GD.N0141.d006685 U D L e ω + ε * D ω * q ω


def d006687 (P : Measure Ω) (D L q : Ω → ℝ) (e : ℝ) : ℝ :=
  ∫ ω, D ω ^ 2 * (L ω - e) * q ω ∂P


def d006688 (P : Measure Ω) (D q : Ω → ℝ) : ℝ :=
  ∫ ω, D ω ^ 2 * q ω ^ 2 ∂P

lemma d006689
    (U D L q : Ω → ℝ) (e ε : ℝ) (ω : Ω) :
    _root_.GD.N0141.d006686 U D L q e ε ω ^ 2 - _root_.GD.N0141.d006685 U D L e ω ^ 2 =
      2 * ε * (U ω * (D ω * q ω))
        + 2 * ε * (D ω ^ 2 * (L ω - e) * q ω)
        + ε ^ 2 * (D ω ^ 2 * q ω ^ 2) := by
  unfold _root_.GD.N0141.d006686 _root_.GD.N0141.d006685
  ring




theorem d006690
    {P : Measure Ω} [IsProbabilityMeasure P]
    {U D L q : Ω → ℝ} {e ε : ℝ}
    (hBaseSq : Integrable (fun ω => _root_.GD.N0141.d006685 U D L e ω ^ 2) P)
    (hCorrectedSq :
      Integrable (fun ω => _root_.GD.N0141.d006686 U D L q e ε ω ^ 2) P)
    (hOracleCross : Integrable (fun ω => U ω * (D ω * q ω)) P)
    (hTrace :
      Integrable (fun ω => D ω ^ 2 * (L ω - e) * q ω) P)
    (hEnergy : Integrable (fun ω => D ω ^ 2 * q ω ^ 2) P)
    (hOrthogonality : ∫ ω, U ω * (D ω * q ω) ∂P = 0) :
    _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006686 U D L q e ε)
        - _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006685 U D L e) =
      2 * ε * _root_.GD.N0141.d006687 P D L q e + ε ^ 2 * _root_.GD.N0141.d006688 P D q := by
  rw [_root_.GD.N0141.d006684, _root_.GD.N0141.d006684, ← integral_sub hCorrectedSq hBaseSq]
  have hpw :
      (fun ω =>
          _root_.GD.N0141.d006686 U D L q e ε ω ^ 2
            - _root_.GD.N0141.d006685 U D L e ω ^ 2) =
        fun ω =>
          2 * ε * (U ω * (D ω * q ω))
            + 2 * ε * (D ω ^ 2 * (L ω - e) * q ω)
            + ε ^ 2 * (D ω ^ 2 * q ω ^ 2) := by
    funext ω
    exact _root_.GD.N0141.d006689 U D L q e ε ω
  rw [hpw]
  have hSplit₁ :
      (fun ω =>
          2 * ε * (U ω * (D ω * q ω))
            + 2 * ε * (D ω ^ 2 * (L ω - e) * q ω)
            + ε ^ 2 * (D ω ^ 2 * q ω ^ 2)) =
        (fun ω => 2 * ε * (U ω * (D ω * q ω))) +
          (fun ω => 2 * ε * (D ω ^ 2 * (L ω - e) * q ω)) +
          (fun ω => ε ^ 2 * (D ω ^ 2 * q ω ^ 2)) := by
    rfl
  rw [hSplit₁]
  rw [integral_add'
      ((hOracleCross.const_mul (2 * ε)).add
        (hTrace.const_mul (2 * ε)))
      (hEnergy.const_mul (ε ^ 2))]
  rw [integral_add'
      (hOracleCross.const_mul (2 * ε))
      (hTrace.const_mul (2 * ε))]
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    hOrthogonality]
  unfold _root_.GD.N0141.d006687 _root_.GD.N0141.d006688
  ring









theorem d006691
    {P : Measure Ω} [IsProbabilityMeasure P]
    {U D L q : Ω → ℝ} {e ε : ℝ}
    (hU : MemLp U 2 P)
    (hWeight : MemLp (fun ω => D ω * (L ω - e)) 2 P)
    (hCarrier : MemLp (fun ω => D ω * q ω) 2 P)
    (hOrthogonality : ∫ ω, U ω * (D ω * q ω) ∂P = 0) :
    _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006686 U D L q e ε)
        - _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006685 U D L e) =
      2 * ε * _root_.GD.N0141.d006687 P D L q e + ε ^ 2 * _root_.GD.N0141.d006688 P D q := by
  have hBase : MemLp (_root_.GD.N0141.d006685 U D L e) 2 P := by
    have h := hU.add hWeight
    rw [show _root_.GD.N0141.d006685 U D L e =
        U + (fun ω => D ω * (L ω - e)) by rfl]
    exact h
  have hScaledCarrier :
      MemLp (fun ω => ε * (D ω * q ω)) 2 P :=
    hCarrier.const_mul ε
  have hCorrected : MemLp (_root_.GD.N0141.d006686 U D L q e ε) 2 P := by
    have := hBase.add hScaledCarrier
    apply (memLp_congr_ae ?_).2 this
    filter_upwards [] with ω
    change
      _root_.GD.N0141.d006685 U D L e ω + ε * D ω * q ω =
        _root_.GD.N0141.d006685 U D L e ω + ε * (D ω * q ω)
    ring
  have hOracleCross :
      Integrable (fun ω => U ω * (D ω * q ω)) P := by
    have h :=
      MemLp.integrable_mul (p := 2) (q := 2) hU hCarrier
    rw [show (fun ω => U ω * (D ω * q ω)) =
        U * (fun ω => D ω * q ω) by rfl]
    exact h
  have hTrace :
      Integrable (fun ω => D ω ^ 2 * (L ω - e) * q ω) P := by
    have h :=
      MemLp.integrable_mul (p := 2) (q := 2) hWeight hCarrier
    have heq :
        ((fun ω => D ω * (L ω - e)) *
            (fun ω => D ω * q ω)) =
          (fun ω => D ω ^ 2 * (L ω - e) * q ω) := by
      funext ω
      simp only [Pi.mul_apply]
      ring
    rw [← heq]
    exact h
  have hEnergy : Integrable (fun ω => D ω ^ 2 * q ω ^ 2) P := by
    have h := hCarrier.integrable_sq
    have heq :
        (fun ω => (D ω * q ω) ^ 2) =
          (fun ω => D ω ^ 2 * q ω ^ 2) := by
      funext ω
      ring
    rw [← heq]
    exact h
  exact _root_.GD.N0141.d006690
    hBase.integrable_sq hCorrected.integrable_sq hOracleCross
    hTrace hEnergy hOrthogonality



theorem d006692
    {P : Measure Ω} [IsProbabilityMeasure P]
    {U D q : Ω → ℝ}
    (hIndep : IndepFun U (fun ω => D ω * q ω) P)
    (hU : AEStronglyMeasurable U P)
    (hCarrier : AEStronglyMeasurable (fun ω => D ω * q ω) P)
    (hCentered : ∫ ω, U ω ∂P = 0) :
    ∫ ω, U ω * (D ω * q ω) ∂P = 0 := by
  rw [hIndep.integral_fun_mul_eq_mul_integral hU hCarrier, hCentered,
    zero_mul]



theorem d006693
    {P : Measure Ω} [IsProbabilityMeasure P]
    {U D q : Ω → ℝ}
    (hIndep : IndepFun U (fun ω => (D ω, q ω)) P)
    (hU : AEStronglyMeasurable U P)
    (hD : Measurable D)
    (hq : Measurable q)
    (hCentered : ∫ ω, U ω ∂P = 0) :
    ∫ ω, U ω * (D ω * q ω) ∂P = 0 := by
  have hProductIndep :
      IndepFun U (fun ω => D ω * q ω) P := by
    have h := hIndep.comp measurable_id
      (measurable_fst.mul measurable_snd)
    simpa [Function.comp_def] using h
  exact _root_.GD.N0141.d006692 hProductIndep hU
    (hD.mul hq).aestronglyMeasurable hCentered


theorem d006694
    {P : Measure Ω} [IsProbabilityMeasure P]
    {U D L q : Ω → ℝ} {e ε : ℝ}
    (hU : MemLp U 2 P)
    (hWeight : MemLp (fun ω => D ω * (L ω - e)) 2 P)
    (hCarrier : MemLp (fun ω => D ω * q ω) 2 P)
    (hIndep : IndepFun U (fun ω => D ω * q ω) P)
    (hCentered : ∫ ω, U ω ∂P = 0) :
    _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006686 U D L q e ε)
        - _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006685 U D L e) =
      2 * ε * _root_.GD.N0141.d006687 P D L q e + ε ^ 2 * _root_.GD.N0141.d006688 P D q := by
  apply _root_.GD.N0141.d006691 hU hWeight hCarrier
  exact _root_.GD.N0141.d006692 hIndep
    hU.aestronglyMeasurable hCarrier.aestronglyMeasurable hCentered


theorem d006695
    {P : Measure Ω} (D q : Ω → ℝ) :
    0 ≤ _root_.GD.N0141.d006688 P D q := by
  unfold _root_.GD.N0141.d006688
  exact integral_nonneg fun ω => mul_nonneg (sq_nonneg _) (sq_nonneg _)



theorem d006696
    {ε η T A M : ℝ}
    (hε : 0 < ε)
    (hT : T ≤ -η)
    (hA : A ≤ M)
    (hCapacity : ε * M < 2 * η) :
    2 * ε * T + ε ^ 2 * A < 0 := by
  nlinarith [sq_nonneg ε, mul_nonneg (le_of_lt hε) (sub_nonneg.mpr hA)]



theorem d006697
    {P : Measure Ω} [IsProbabilityMeasure P]
    {U D L q : Ω → ℝ} {e ε η M : ℝ}
    (hIdentity :
      _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006686 U D L q e ε)
          - _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006685 U D L e) =
        2 * ε * _root_.GD.N0141.d006687 P D L q e + ε ^ 2 * _root_.GD.N0141.d006688 P D q)
    (hε : 0 < ε)
    (hTraceMargin : _root_.GD.N0141.d006687 P D L q e ≤ -η)
    (hEnergyBound : _root_.GD.N0141.d006688 P D q ≤ M)
    (hCapacity : ε * M < 2 * η) :
    _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006686 U D L q e ε) <
      _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006685 U D L e) := by
  have hneg :
      2 * ε * _root_.GD.N0141.d006687 P D L q e
          + ε ^ 2 * _root_.GD.N0141.d006688 P D q < 0 :=
    _root_.GD.N0141.d006696 hε hTraceMargin hEnergyBound hCapacity
  linarith

end

end GD.N0141
