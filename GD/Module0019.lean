import GD.Module0015

























open MeasureTheory
open scoped BigOperators

namespace GD
namespace N0230
namespace N0617

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false


def d000163
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  1 + ∑ i, weight i * likelihood i ω


def d000164
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, weight i * likelihood i ω * center i


def d000165
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, weight i * likelihood i ω * center i ^ 2



def d000166
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ) (ω : Ω) : ℝ :=
  _root_.GD.N0230.N0617.d000164 weight likelihood center ω /
    _root_.GD.N0230.N0617.d000163 weight likelihood ω


def d000167
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ) (ω : Ω) : ℝ :=
  _root_.GD.N0230.N0617.d000164 weight likelihood center ω ^ 2 /
    _root_.GD.N0230.N0617.d000163 weight likelihood ω


theorem d000168
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihood : ∀ i ω, 0 ≤ likelihood i ω) (ω : Ω) :
    1 ≤ _root_.GD.N0230.N0617.d000163 weight likelihood ω := by
  unfold _root_.GD.N0230.N0617.d000163
  have hsum : 0 ≤ ∑ i, weight i * likelihood i ω :=
    Finset.sum_nonneg fun i _ ↦
      mul_nonneg (hweight i) (hlikelihood i ω)
  linarith


theorem d000169
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihood : ∀ i ω, 0 ≤ likelihood i ω) (ω : Ω) :
    0 < _root_.GD.N0230.N0617.d000163 weight likelihood ω :=
  lt_of_lt_of_le zero_lt_one
    (_root_.GD.N0230.N0617.d000168 weight likelihood hweight hlikelihood ω)



private theorem d000170
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ) (q : ℝ) (ω : Ω) :
    ∑ i, weight i * likelihood i ω * (q - center i) ^ 2 =
      q ^ 2 * (∑ i, weight i * likelihood i ω) -
        2 * q * _root_.GD.N0230.N0617.d000164 weight likelihood center ω +
          _root_.GD.N0230.N0617.d000165 weight likelihood center ω := by
  unfold _root_.GD.N0230.N0617.d000164 _root_.GD.N0230.N0617.d000165
  calc
    ∑ i, weight i * likelihood i ω * (q - center i) ^ 2 =
        ∑ i, (q ^ 2 * (weight i * likelihood i ω) -
          2 * q * (weight i * likelihood i ω * center i) +
          weight i * likelihood i ω * center i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = q ^ 2 * (∑ i, weight i * likelihood i ω) -
        2 * q * (∑ i, weight i * likelihood i ω * center i) +
          ∑ i, weight i * likelihood i ω * center i ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum]


theorem d000171
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihood : ∀ i ω, 0 ≤ likelihood i ω)
    (q : ℝ) (ω : Ω) :
    q ^ 2 +
        ∑ i, weight i * likelihood i ω * (q - center i) ^ 2 =
      _root_.GD.N0230.N0617.d000163 weight likelihood ω *
          (q - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2 +
        _root_.GD.N0230.N0617.d000165 weight likelihood center ω -
          _root_.GD.N0230.N0617.d000167 weight likelihood center ω := by
  have hmass := _root_.GD.N0230.N0617.d000169
    weight likelihood hweight hlikelihood ω
  rw [_root_.GD.N0230.N0617.d000170]
  unfold _root_.GD.N0230.N0617.d000166 _root_.GD.N0230.N0617.d000167
  field_simp [hmass.ne']
  unfold _root_.GD.N0230.N0617.d000163 _root_.GD.N0230.N0617.d000164
  ring


theorem d000172
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihood : ∀ i ω, 0 ≤ likelihood i ω) (ω : Ω) :
    0 ≤ _root_.GD.N0230.N0617.d000167 weight likelihood center ω := by
  unfold _root_.GD.N0230.N0617.d000167
  exact div_nonneg (sq_nonneg _)
    (_root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood ω).le



theorem d000173
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihood : ∀ i ω, 0 ≤ likelihood i ω) (ω : Ω) :
    _root_.GD.N0230.N0617.d000167 weight likelihood center ω ≤
      _root_.GD.N0230.N0617.d000165 weight likelihood center ω := by
  let a : ι → ℝ := fun i ↦ weight i * likelihood i ω
  have ha : ∀ i, 0 ≤ a i := fun i ↦
    mul_nonneg (hweight i) (hlikelihood i ω)
  have hsecond : 0 ≤ ∑ i, a i * center i ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (ha i) (sq_nonneg _)
  have hcs :
      (∑ i, a i * center i) ^ 2 ≤
        (∑ i, a i) * ∑ i, a i * center i ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (R := ℝ) (ι := ι)
      (r := fun i ↦ a i * center i)
      (f := fun i ↦ a i)
      (g := fun i ↦ a i * center i ^ 2)
    · intro i hi
      exact ha i
    · intro i hi
      exact mul_nonneg (ha i) (sq_nonneg _)
    · intro i hi
      show (a i * center i) ^ 2 ≤ a i * (a i * center i ^ 2)
      exact le_of_eq (by ring)
  have hmass : 0 < _root_.GD.N0230.N0617.d000163 weight likelihood ω :=
    _root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood ω
  have hmassExpansion :
      _root_.GD.N0230.N0617.d000163 weight likelihood ω = 1 + ∑ i, a i := by
    rfl
  have hproduct :
      (∑ i, a i * center i) ^ 2 ≤
        _root_.GD.N0230.N0617.d000163 weight likelihood ω *
          ∑ i, a i * center i ^ 2 := by
    rw [hmassExpansion]
    nlinarith
  unfold _root_.GD.N0230.N0617.d000167 _root_.GD.N0230.N0617.d000164
    _root_.GD.N0230.N0617.d000165
  change (∑ i, a i * center i) ^ 2 /
      _root_.GD.N0230.N0617.d000163 weight likelihood ω ≤
    ∑ i, a i * center i ^ 2
  exact (div_le_iff₀ hmass).2 (by
    simpa only [mul_comm] using hproduct)





theorem d000174
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihood : ∀ i ω, 0 ≤ likelihood i ω)
    (i : ι) (ω : Ω) :
    (weight i * likelihood i ω) /
          (1 + weight i * likelihood i ω) * center i ^ 2 ≤
      _root_.GD.N0230.N0617.d000165 weight likelihood center ω -
        _root_.GD.N0230.N0617.d000167 weight likelihood center ω := by
  let a : ℝ := weight i * likelihood i ω
  let q : ℝ := _root_.GD.N0230.N0617.d000166 weight likelihood center ω
  have ha : 0 ≤ a := mul_nonneg (hweight i) (hlikelihood i ω)
  have hden : 0 < 1 + a := by linarith
  have halgebra :
      a / (1 + a) * center i ^ 2 ≤
        q ^ 2 + a * (q - center i) ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [sq_nonneg ((1 + a) * q - a * center i)]
  have hatom :
      a * (q - center i) ^ 2 ≤
        ∑ j, weight j * likelihood j ω * (q - center j) ^ 2 := by
    simpa only [a] using Finset.single_le_sum
      (fun j _ ↦ mul_nonneg
        (mul_nonneg (hweight j) (hlikelihood j ω))
        (sq_nonneg (q - center j)))
      (Finset.mem_univ i)
  have hcompletion := _root_.GD.N0230.N0617.d000171
    weight likelihood center hweight hlikelihood q ω
  have hminimum :
      q ^ 2 + ∑ j, weight j * likelihood j ω * (q - center j) ^ 2 =
        _root_.GD.N0230.N0617.d000165 weight likelihood center ω -
          _root_.GD.N0230.N0617.d000167 weight likelihood center ω := by
    simpa only [q, sub_self, pow_two, mul_zero, zero_add] using hcompletion
  calc
    (weight i * likelihood i ω) /
          (1 + weight i * likelihood i ω) * center i ^ 2 =
        a / (1 + a) * center i ^ 2 := by rfl
    _ ≤ q ^ 2 + a * (q - center i) ^ 2 := halgebra
    _ ≤ q ^ 2 + ∑ j, weight j * likelihood j ω *
          (q - center j) ^ 2 := by linarith
    _ = _root_.GD.N0230.N0617.d000165 weight likelihood center ω -
          _root_.GD.N0230.N0617.d000167 weight likelihood center ω := hminimum




theorem d000175
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihood : ∀ i ω, 0 ≤ likelihood i ω) (ω : Ω) :
    _root_.GD.N0230.N0617.d000166 weight likelihood center ω ^ 2 ≤
      ∑ i, center i ^ 2 := by
  let a : ι → ℝ := fun i ↦ weight i * likelihood i ω
  let S : ℝ := ∑ i, center i ^ 2
  have ha : ∀ i, 0 ≤ a i := fun i ↦
    mul_nonneg (hweight i) (hlikelihood i ω)
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hcenterLe : ∀ i, center i ^ 2 ≤ S := by
    intro i
    unfold S
    exact Finset.single_le_sum
      (fun j _ ↦ sq_nonneg (center j)) (Finset.mem_univ i)
  have hsecondLe :
      (∑ i, a i * center i ^ 2) ≤ S * ∑ i, a i := by
    calc
      (∑ i, a i * center i ^ 2) ≤ ∑ i, a i * S := by
        exact Finset.sum_le_sum fun i hi ↦
          mul_le_mul_of_nonneg_left (hcenterLe i) (ha i)
      _ = S * ∑ i, a i := by
        calc
          (∑ i, a i * S) = (∑ i, a i) * S := by
            simpa using (Finset.sum_mul Finset.univ a S).symm
          _ = S * ∑ i, a i := mul_comm _ _
  have hmass : 0 < _root_.GD.N0230.N0617.d000163 weight likelihood ω :=
    _root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood ω
  have hsumMass : (∑ i, a i) ≤ _root_.GD.N0230.N0617.d000163 weight likelihood ω := by
    unfold _root_.GD.N0230.N0617.d000163 a
    linarith
  have hsecondMass :
      (∑ i, a i * center i ^ 2) ≤
        S * _root_.GD.N0230.N0617.d000163 weight likelihood ω :=
    hsecondLe.trans
      (mul_le_mul_of_nonneg_left hsumMass hS)
  have hmomentSq :
      _root_.GD.N0230.N0617.d000164 weight likelihood center ω ^ 2 ≤
        _root_.GD.N0230.N0617.d000163 weight likelihood ω *
          (∑ i, a i * center i ^ 2) := by
    have hcorrection := _root_.GD.N0230.N0617.d000173
      weight likelihood center hweight hlikelihood ω
    unfold _root_.GD.N0230.N0617.d000167 _root_.GD.N0230.N0617.d000165 at hcorrection
    change _root_.GD.N0230.N0617.d000164 weight likelihood center ω ^ 2 /
        _root_.GD.N0230.N0617.d000163 weight likelihood ω ≤
      ∑ i, a i * center i ^ 2 at hcorrection
    exact (by
      simpa only [mul_comm] using (div_le_iff₀ hmass).mp hcorrection)
  have hmomentSqBound :
      _root_.GD.N0230.N0617.d000164 weight likelihood center ω ^ 2 ≤
        S * _root_.GD.N0230.N0617.d000163 weight likelihood ω ^ 2 := by
    calc
      _root_.GD.N0230.N0617.d000164 weight likelihood center ω ^ 2 ≤
          _root_.GD.N0230.N0617.d000163 weight likelihood ω *
            (∑ i, a i * center i ^ 2) := hmomentSq
      _ ≤ _root_.GD.N0230.N0617.d000163 weight likelihood ω *
          (S * _root_.GD.N0230.N0617.d000163 weight likelihood ω) :=
        mul_le_mul_of_nonneg_left hsecondMass hmass.le
      _ = S * _root_.GD.N0230.N0617.d000163 weight likelihood ω ^ 2 := by ring
  unfold _root_.GD.N0230.N0617.d000166
  rw [div_pow]
  exact (div_le_iff₀ (sq_pos_of_pos hmass)).2 (by
    simpa only [mul_comm] using hmomentSqBound)


theorem d000176
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihood : ∀ i ω, 0 ≤ likelihood i ω) (ω : Ω) :
    |_root_.GD.N0230.N0617.d000166 weight likelihood center ω| ≤
      Real.sqrt (∑ i, center i ^ 2) :=
  Real.abs_le_sqrt
    (_root_.GD.N0230.N0617.d000175
      weight likelihood center hweight hlikelihood ω)


theorem d000177
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (hlikelihood : ∀ i, Measurable (likelihood i)) :
    Measurable (_root_.GD.N0230.N0617.d000163 weight likelihood) := by
  unfold _root_.GD.N0230.N0617.d000163
  fun_prop


theorem d000178
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ)
    (hlikelihood : ∀ i, Measurable (likelihood i)) :
    Measurable (_root_.GD.N0230.N0617.d000164 weight likelihood center) := by
  unfold _root_.GD.N0230.N0617.d000164
  fun_prop


theorem d000179
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ)
    (hlikelihood : ∀ i, Measurable (likelihood i)) :
    Measurable (_root_.GD.N0230.N0617.d000166 weight likelihood center) := by
  unfold _root_.GD.N0230.N0617.d000166
  exact (_root_.GD.N0230.N0617.d000178 weight likelihood center hlikelihood).div
    (_root_.GD.N0230.N0617.d000177 weight likelihood hlikelihood)


theorem d000180
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ)
    (hlikelihood : ∀ i, Measurable (likelihood i)) :
    Measurable (_root_.GD.N0230.N0617.d000167 weight likelihood center) := by
  unfold _root_.GD.N0230.N0617.d000167
  exact ((_root_.GD.N0230.N0617.d000178
    weight likelihood center hlikelihood).pow_const 2).div
      (_root_.GD.N0230.N0617.d000177 weight likelihood hlikelihood)




theorem d000181
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihoodNonneg : ∀ i ω, 0 ≤ likelihood i ω)
    (hlikelihoodMeas : ∀ i, Measurable (likelihood i)) :
    MemLp (_root_.GD.N0230.N0617.d000166 weight likelihood center) 2 μ := by
  let B : ℝ := Real.sqrt (∑ i, center i ^ 2)
  apply memLp_of_bounded (a := -B) (b := B)
  · filter_upwards with ω
    exact abs_le.mp (_root_.GD.N0230.N0617.d000176
      weight likelihood center hweight hlikelihoodNonneg ω)
  · exact (_root_.GD.N0230.N0617.d000179
      weight likelihood center hlikelihoodMeas).aestronglyMeasurable


theorem d000182
    (μ : Measure Ω) (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ)
    (hlikelihoodInt : ∀ i, Integrable (likelihood i) μ) :
    Integrable (_root_.GD.N0230.N0617.d000165 weight likelihood center) μ := by
  unfold _root_.GD.N0230.N0617.d000165
  apply integrable_finsetSum
  intro i hi
  have h := (hlikelihoodInt i).const_mul (weight i * center i ^ 2)
  refine h.congr ?_
  filter_upwards with ω
  ring



theorem d000183
    (μ : Measure Ω) (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihoodNonneg : ∀ i ω, 0 ≤ likelihood i ω)
    (hlikelihoodMeas : ∀ i, Measurable (likelihood i))
    (hlikelihoodInt : ∀ i, Integrable (likelihood i) μ) :
    Integrable (_root_.GD.N0230.N0617.d000167 weight likelihood center) μ := by
  apply Integrable.mono'
    (_root_.GD.N0230.N0617.d000182
      μ weight likelihood center hlikelihoodInt)
    (_root_.GD.N0230.N0617.d000180
      weight likelihood center hlikelihoodMeas).aestronglyMeasurable
  filter_upwards with ω
  have hnonneg := _root_.GD.N0230.N0617.d000172
    weight likelihood center hweight hlikelihoodNonneg ω
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact _root_.GD.N0230.N0617.d000173
      weight likelihood center hweight hlikelihoodNonneg ω


theorem d000184
    (μ : Measure Ω) (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ) (q : Ω → ℝ)
    (hriskInt : ∀ i,
      Integrable (fun ω ↦ likelihood i ω * (q ω - center i) ^ 2) μ) :
    Integrable
      (fun ω ↦ ∑ i,
        weight i * likelihood i ω * (q ω - center i) ^ 2) μ := by
  apply integrable_finsetSum
  intro i hi
  simpa only [mul_assoc] using
    (hriskInt i).const_mul (weight i)



theorem d000185
    (μ : Measure Ω) (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ) (q : Ω → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihoodNonneg : ∀ i ω, 0 ≤ likelihood i ω)
    (hlikelihoodMeas : ∀ i, Measurable (likelihood i))
    (hlikelihoodInt : ∀ i, Integrable (likelihood i) μ)
    (hqSq : Integrable (fun ω ↦ q ω ^ 2) μ)
    (hriskInt : ∀ i,
      Integrable (fun ω ↦ likelihood i ω * (q ω - center i) ^ 2) μ) :
    Integrable (fun ω ↦
      _root_.GD.N0230.N0617.d000163 weight likelihood ω *
        (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2) μ := by
  have hweightedRisk := _root_.GD.N0230.N0617.d000184
    μ weight likelihood center q hriskInt
  have hsecond := _root_.GD.N0230.N0617.d000182
    μ weight likelihood center hlikelihoodInt
  have hcorrection := _root_.GD.N0230.N0617.d000183
    μ weight likelihood center hweight hlikelihoodNonneg
      hlikelihoodMeas hlikelihoodInt
  have hrepresentation :
      (fun ω ↦ _root_.GD.N0230.N0617.d000163 weight likelihood ω *
        (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2) =
      (fun ω ↦ q ω ^ 2 +
          (∑ i, weight i * likelihood i ω *
            (q ω - center i) ^ 2) -
          _root_.GD.N0230.N0617.d000165 weight likelihood center ω +
          _root_.GD.N0230.N0617.d000167 weight likelihood center ω) := by
    funext ω
    have h := _root_.GD.N0230.N0617.d000171
      weight likelihood center hweight hlikelihoodNonneg (q ω) ω
    linarith
  rw [hrepresentation]
  exact ((hqSq.add hweightedRisk).sub hsecond).add hcorrection



def d000186
    (μ : Measure Ω) (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center cap : ι → ℝ) : ℝ :=
  (∑ i, weight i * (center i ^ 2 - cap i)) -
    ∫ ω, _root_.GD.N0230.N0617.d000167 weight likelihood center ω ∂μ



theorem d000187
    (μ : Measure Ω) (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center : ι → ℝ) (q : Ω → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihoodNonneg : ∀ i ω, 0 ≤ likelihood i ω)
    (hlikelihoodMeas : ∀ i, Measurable (likelihood i))
    (hlikelihoodInt : ∀ i, Integrable (likelihood i) μ)
    (hqSq : Integrable (fun ω ↦ q ω ^ 2) μ)
    (hriskInt : ∀ i,
      Integrable (fun ω ↦ likelihood i ω * (q ω - center i) ^ 2) μ) :
    (∫ ω, q ω ^ 2 ∂μ) +
        ∑ i, weight i *
          (∫ ω, likelihood i ω * (q ω - center i) ^ 2 ∂μ) =
      (∫ ω, _root_.GD.N0230.N0617.d000163 weight likelihood ω *
          (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2 ∂μ) +
        ∑ i, weight i * center i ^ 2 * (∫ ω, likelihood i ω ∂μ) -
          ∫ ω, _root_.GD.N0230.N0617.d000167 weight likelihood center ω ∂μ := by
  have hweightedRisk := _root_.GD.N0230.N0617.d000184
    μ weight likelihood center q hriskInt
  have hsecond := _root_.GD.N0230.N0617.d000182
    μ weight likelihood center hlikelihoodInt
  have hcorrection := _root_.GD.N0230.N0617.d000183
    μ weight likelihood center hweight hlikelihoodNonneg
      hlikelihoodMeas hlikelihoodInt
  have hdistance := _root_.GD.N0230.N0617.d000185
    μ weight likelihood center q hweight hlikelihoodNonneg
      hlikelihoodMeas hlikelihoodInt hqSq hriskInt
  have hpoint : ∀ᵐ ω ∂μ,
      q ω ^ 2 +
          ∑ i, weight i * likelihood i ω * (q ω - center i) ^ 2 =
        _root_.GD.N0230.N0617.d000163 weight likelihood ω *
            (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2 +
          _root_.GD.N0230.N0617.d000165 weight likelihood center ω -
            _root_.GD.N0230.N0617.d000167 weight likelihood center ω :=
    ae_of_all μ fun ω ↦ _root_.GD.N0230.N0617.d000171
      weight likelihood center hweight hlikelihoodNonneg (q ω) ω
  have hweightedRiskIntegral :
      (∫ ω, ∑ i, weight i * likelihood i ω *
          (q ω - center i) ^ 2 ∂μ) =
        ∑ i, weight i *
          (∫ ω, likelihood i ω * (q ω - center i) ^ 2 ∂μ) := by
    rw [integral_finsetSum Finset.univ (fun i _ ↦ by
      convert (hriskInt i).const_mul (weight i) using 1
      funext ω
      ring)]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∫ ω, weight i * likelihood i ω * (q ω - center i) ^ 2 ∂μ) =
          ∫ ω, weight i *
            (likelihood i ω * (q ω - center i) ^ 2) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ fun ω ↦ by ring
      _ = weight i *
          ∫ ω, likelihood i ω * (q ω - center i) ^ 2 ∂μ :=
        integral_const_mul (μ := μ) (weight i)
          (fun ω ↦ likelihood i ω * (q ω - center i) ^ 2)
  have hsecondIntegral :
      (∫ ω, _root_.GD.N0230.N0617.d000165
          weight likelihood center ω ∂μ) =
        ∑ i, weight i * center i ^ 2 *
          (∫ ω, likelihood i ω ∂μ) := by
    unfold _root_.GD.N0230.N0617.d000165
    rw [integral_finsetSum Finset.univ (fun i _ ↦ by
      convert (hlikelihoodInt i).const_mul
        (weight i * center i ^ 2) using 1
      funext ω
      ring)]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∫ ω, weight i * likelihood i ω * center i ^ 2 ∂μ) =
          ∫ ω, (weight i * center i ^ 2) * likelihood i ω ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ fun ω ↦ by ring
      _ = weight i * center i ^ 2 *
          ∫ ω, likelihood i ω ∂μ :=
        integral_const_mul (μ := μ) (weight i * center i ^ 2)
          (likelihood i)
  calc
    (∫ ω, q ω ^ 2 ∂μ) +
        ∑ i, weight i *
          (∫ ω, likelihood i ω * (q ω - center i) ^ 2 ∂μ) =
        ∫ ω, q ω ^ 2 +
          ∑ i, weight i * likelihood i ω *
            (q ω - center i) ^ 2 ∂μ := by
      rw [integral_add hqSq hweightedRisk, hweightedRiskIntegral]
    _ = ∫ ω,
        _root_.GD.N0230.N0617.d000163 weight likelihood ω *
            (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2 +
          _root_.GD.N0230.N0617.d000165 weight likelihood center ω -
            _root_.GD.N0230.N0617.d000167 weight likelihood center ω ∂μ :=
      integral_congr_ae hpoint
    _ = (∫ ω, _root_.GD.N0230.N0617.d000163 weight likelihood ω *
          (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2 ∂μ) +
        ∫ ω, _root_.GD.N0230.N0617.d000165 weight likelihood center ω ∂μ -
          ∫ ω, _root_.GD.N0230.N0617.d000167 weight likelihood center ω ∂μ := by
      have hsub := integral_sub (hdistance.add hsecond) hcorrection
      have hadd := integral_add hdistance hsecond
      calc
        _ = ∫ ω,
            ((fun ω ↦ _root_.GD.N0230.N0617.d000163 weight likelihood ω *
                (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2) +
              _root_.GD.N0230.N0617.d000165 weight likelihood center) ω -
              _root_.GD.N0230.N0617.d000167 weight likelihood center ω ∂μ := by rfl
        _ = (∫ ω,
            ((fun ω ↦ _root_.GD.N0230.N0617.d000163 weight likelihood ω *
                (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2) +
              _root_.GD.N0230.N0617.d000165 weight likelihood center) ω ∂μ) -
              ∫ ω, _root_.GD.N0230.N0617.d000167 weight likelihood center ω ∂μ := hsub
        _ = _ := congrArg
          (fun z : ℝ ↦ z -
            ∫ ω, _root_.GD.N0230.N0617.d000167 weight likelihood center ω ∂μ) hadd
    _ = (∫ ω, _root_.GD.N0230.N0617.d000163 weight likelihood ω *
          (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2 ∂μ) +
        ∑ i, weight i * center i ^ 2 * (∫ ω, likelihood i ω ∂μ) -
          ∫ ω, _root_.GD.N0230.N0617.d000167 weight likelihood center ω ∂μ := by
      rw [hsecondIntegral]





theorem d000188
    (μ : Measure Ω) (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center cap : ι → ℝ) (q : Ω → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihoodNonneg : ∀ i ω, 0 ≤ likelihood i ω)
    (hlikelihoodMeas : ∀ i, Measurable (likelihood i))
    (hlikelihoodInt : ∀ i, Integrable (likelihood i) μ)
    (hlikelihoodMass : ∀ i, ∫ ω, likelihood i ω ∂μ = 1)
    (hqSq : Integrable (fun ω ↦ q ω ^ 2) μ)
    (hriskInt : ∀ i,
      Integrable (fun ω ↦ likelihood i ω * (q ω - center i) ^ 2) μ) :
    (∫ ω, q ω ^ 2 ∂μ) -
        (_root_.GD.N0230.N0617.d000186 μ weight likelihood center cap +
          ∫ ω, _root_.GD.N0230.N0617.d000163 weight likelihood ω *
            (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2
              ∂μ) =
      ∑ i, weight i *
        (cap i - ∫ ω, likelihood i ω * (q ω - center i) ^ 2 ∂μ) := by
  have hexact := _root_.GD.N0230.N0617.d000187
    μ weight likelihood center q hweight hlikelihoodNonneg
      hlikelihoodMeas hlikelihoodInt hqSq hriskInt
  simp_rw [hlikelihoodMass, mul_one] at hexact
  unfold _root_.GD.N0230.N0617.d000186
  have hleftExpand :
      (∑ i, weight i * (center i ^ 2 - cap i)) =
        (∑ i, weight i * center i ^ 2) -
          ∑ i, weight i * cap i := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hrightExpand :
      (∑ i, weight i *
        (cap i - ∫ ω, likelihood i ω * (q ω - center i) ^ 2 ∂μ)) =
        (∑ i, weight i * cap i) -
          ∑ i, weight i *
            (∫ ω, likelihood i ω * (q ω - center i) ^ 2 ∂μ) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hleftExpand, hrightExpand]
  linarith



theorem d000189
    (μ : Measure Ω) (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center cap : ι → ℝ) (q : Ω → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihoodNonneg : ∀ i ω, 0 ≤ likelihood i ω)
    (hlikelihoodMeas : ∀ i, Measurable (likelihood i))
    (hlikelihoodInt : ∀ i, Integrable (likelihood i) μ)
    (hlikelihoodMass : ∀ i, ∫ ω, likelihood i ω ∂μ = 1)
    (hqSq : Integrable (fun ω ↦ q ω ^ 2) μ)
    (hriskInt : ∀ i,
      Integrable (fun ω ↦ likelihood i ω * (q ω - center i) ^ 2) μ)
    (hriskCap : ∀ i,
      (∫ ω, likelihood i ω * (q ω - center i) ^ 2 ∂μ) ≤ cap i) :
    _root_.GD.N0230.N0617.d000186 μ weight likelihood center cap +
        (∫ ω, _root_.GD.N0230.N0617.d000163 weight likelihood ω *
          (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2 ∂μ) ≤
      ∫ ω, q ω ^ 2 ∂μ := by
  have hexact := _root_.GD.N0230.N0617.d000187
    μ weight likelihood center q hweight hlikelihoodNonneg
      hlikelihoodMeas hlikelihoodInt hqSq hriskInt
  have hweightedCap :
      ∑ i, weight i *
          (∫ ω, likelihood i ω * (q ω - center i) ^ 2 ∂μ) ≤
        ∑ i, weight i * cap i := by
    exact Finset.sum_le_sum fun i hi ↦
      mul_le_mul_of_nonneg_left (hriskCap i) (hweight i)
  simp_rw [hlikelihoodMass, mul_one] at hexact
  unfold _root_.GD.N0230.N0617.d000186
  have hcenterCap :
      (∑ i, weight i * (center i ^ 2 - cap i)) =
        (∑ i, weight i * center i ^ 2) -
          ∑ i, weight i * cap i := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hcenterCap]
  linarith



theorem d000190
    (μ : Measure Ω) (weight : ι → ℝ) (likelihood : ι → Ω → ℝ)
    (center cap : ι → ℝ) (q : Ω → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihoodNonneg : ∀ i ω, 0 ≤ likelihood i ω)
    (hlikelihoodMeas : ∀ i, Measurable (likelihood i))
    (hlikelihoodInt : ∀ i, Integrable (likelihood i) μ)
    (hlikelihoodMass : ∀ i, ∫ ω, likelihood i ω ∂μ = 1)
    (hqAEMeas : AEStronglyMeasurable q μ)
    (hqSq : Integrable (fun ω ↦ q ω ^ 2) μ)
    (hriskInt : ∀ i,
      Integrable (fun ω ↦ likelihood i ω * (q ω - center i) ^ 2) μ)
    (hriskCap : ∀ i,
      (∫ ω, likelihood i ω * (q ω - center i) ^ 2 ∂μ) ≤ cap i) :
    _root_.GD.N0230.N0617.d000186 μ weight likelihood center cap +
        (∫ ω, (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2 ∂μ) ≤
      ∫ ω, q ω ^ 2 ∂μ := by
  have hweighted :=
    _root_.GD.N0230.N0617.d000189
      μ weight likelihood center cap q hweight hlikelihoodNonneg
        hlikelihoodMeas hlikelihoodInt hlikelihoodMass hqSq hriskInt hriskCap
  have hdistance := _root_.GD.N0230.N0617.d000185
    μ weight likelihood center q hweight hlikelihoodNonneg
      hlikelihoodMeas hlikelihoodInt hqSq hriskInt
  have hplain : Integrable (fun ω ↦
      (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2) μ := by
    apply Integrable.mono' hdistance
    · exact ((hqAEMeas.aemeasurable.sub
          (_root_.GD.N0230.N0617.d000179
            weight likelihood center hlikelihoodMeas).aemeasurable).pow_const 2)
          |>.aestronglyMeasurable
    · filter_upwards with ω
      have hsq : 0 ≤
          (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2 :=
        sq_nonneg _
      have hmass := _root_.GD.N0230.N0617.d000168
        weight likelihood hweight hlikelihoodNonneg ω
      rw [Real.norm_eq_abs, abs_of_nonneg hsq]
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hmass hsq)
  have hmono :
      (∫ ω, (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2 ∂μ) ≤
        ∫ ω, _root_.GD.N0230.N0617.d000163 weight likelihood ω *
          (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2 ∂μ := by
    apply integral_mono hplain hdistance
    intro ω
    have hsq : 0 ≤
        (q ω - _root_.GD.N0230.N0617.d000166 weight likelihood center ω) ^ 2 :=
      sq_nonneg _
    have hmass := _root_.GD.N0230.N0617.d000168
      weight likelihood hweight hlikelihoodNonneg ω
    nlinarith
  linarith

end

end N0617
end N0230
end GD

#print axioms _root_.GD.N0230.N0617.d000171
#print axioms _root_.GD.N0230.N0617.d000173
#print axioms _root_.GD.N0230.N0617.d000174
#print axioms _root_.GD.N0230.N0617.d000175
#print axioms _root_.GD.N0230.N0617.d000181
#print axioms _root_.GD.N0230.N0617.d000183
#print axioms _root_.GD.N0230.N0617.d000187
#print axioms _root_.GD.N0230.N0617.d000188
#print axioms _root_.GD.N0230.N0617.d000189
#print axioms _root_.GD.N0230.N0617.d000190
