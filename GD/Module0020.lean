import GD.Module0019





















open MeasureTheory
open scoped BigOperators

namespace GD
namespace N0230
namespace N0618

noncomputable section

open _root_.GD.N0230.N0617

set_option linter.unusedSectionVars false

variable {Omega I : Type*} [MeasurableSpace Omega]
variable [Fintype I] [DecidableEq I]



def d000191
    (weight weight' : I → ℝ) (likelihood : I → Omega → ℝ)
    (omega : Omega) : ℝ :=
  ∑ i, |weight i - weight' i| * likelihood i omega




theorem d000192
    (weight weight' : I → ℝ) (likelihood : I → Omega → ℝ)
    (center : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweight' : ∀ i, 0 ≤ weight' i)
    (hlikelihood : ∀ i omega, 0 ≤ likelihood i omega) (omega : Omega) :
    _root_.GD.N0230.N0617.d000166 weight likelihood center omega -
        _root_.GD.N0230.N0617.d000166 weight' likelihood center omega =
      (∑ i, (weight i - weight' i) * likelihood i omega *
        (center i - _root_.GD.N0230.N0617.d000166 weight' likelihood center omega)) /
        _root_.GD.N0230.N0617.d000163 weight likelihood omega := by
  have hmass : _root_.GD.N0230.N0617.d000163 weight likelihood omega ≠ 0 :=
    (_root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood omega).ne'
  have hmass' : _root_.GD.N0230.N0617.d000163 weight' likelihood omega ≠ 0 :=
    (_root_.GD.N0230.N0617.d000169 weight' likelihood hweight' hlikelihood omega).ne'
  have hmoment' :
      _root_.GD.N0230.N0617.d000164 weight' likelihood center omega =
        _root_.GD.N0230.N0617.d000166 weight' likelihood center omega *
          _root_.GD.N0230.N0617.d000163 weight' likelihood omega := by
    unfold _root_.GD.N0230.N0617.d000166
    field_simp [hmass']
  apply (eq_div_iff hmass).2
  rw [sub_mul]
  have hfirst :
      _root_.GD.N0230.N0617.d000166 weight likelihood center omega *
          _root_.GD.N0230.N0617.d000163 weight likelihood omega =
        _root_.GD.N0230.N0617.d000164 weight likelihood center omega := by
    unfold _root_.GD.N0230.N0617.d000166
    field_simp [hmass]
  rw [hfirst]
  rw [show _root_.GD.N0230.N0617.d000164 weight likelihood center omega -
      _root_.GD.N0230.N0617.d000166 weight' likelihood center omega *
        _root_.GD.N0230.N0617.d000163 weight likelihood omega =
      (_root_.GD.N0230.N0617.d000164 weight likelihood center omega -
        _root_.GD.N0230.N0617.d000164 weight' likelihood center omega) -
      _root_.GD.N0230.N0617.d000166 weight' likelihood center omega *
        (_root_.GD.N0230.N0617.d000163 weight likelihood omega -
          _root_.GD.N0230.N0617.d000163 weight' likelihood omega) by
        rw [hmoment']
        ring]
  unfold _root_.GD.N0230.N0617.d000164 _root_.GD.N0230.N0617.d000163
  rw [← Finset.sum_sub_distrib]
  rw [show
      (1 + ∑ i, weight i * likelihood i omega) -
          (1 + ∑ i, weight' i * likelihood i omega) =
        ∑ i, (weight i * likelihood i omega -
          weight' i * likelihood i omega) by
      rw [Finset.sum_sub_distrib]
      ring]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem d000193
    (weight weight' : I → ℝ) (likelihood : I → Omega → ℝ)
    (hlikelihood : ∀ i omega, 0 ≤ likelihood i omega) (omega : Omega) :
    0 ≤ _root_.GD.N0230.N0618.d000191 weight weight' likelihood omega := by
  unfold _root_.GD.N0230.N0618.d000191
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (abs_nonneg _) (hlikelihood i omega)



theorem d000194
    (weight weight' : I → ℝ) (likelihood : I → Omega → ℝ)
    (hlikelihood : ∀ i omega, 0 ≤ likelihood i omega) (omega : Omega) :
    |_root_.GD.N0230.N0617.d000163 weight likelihood omega -
        _root_.GD.N0230.N0617.d000163 weight' likelihood omega| ≤
      _root_.GD.N0230.N0618.d000191 weight weight' likelihood omega := by
  unfold _root_.GD.N0230.N0617.d000163 _root_.GD.N0230.N0618.d000191
  rw [show
      (1 + ∑ i, weight i * likelihood i omega) -
          (1 + ∑ i, weight' i * likelihood i omega) =
        (∑ i, weight i * likelihood i omega) -
          ∑ i, weight' i * likelihood i omega by ring]
  rw [← Finset.sum_sub_distrib]
  rw [show
      (∑ i, (weight i * likelihood i omega -
          weight' i * likelihood i omega)) =
        ∑ i, (weight i - weight' i) * likelihood i omega by
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  calc
    |∑ i, (weight i - weight' i) * likelihood i omega| ≤
        ∑ i, |(weight i - weight' i) * likelihood i omega| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |weight i - weight' i| * likelihood i omega := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hlikelihood i omega)]



theorem d000195
    (weight weight' : I → ℝ) (likelihood : I → Omega → ℝ)
    (center : I → ℝ) (B : ℝ)
    (hlikelihood : ∀ i omega, 0 ≤ likelihood i omega)
    (hcenter : ∀ i, |center i| ≤ B) (omega : Omega) :
    |_root_.GD.N0230.N0617.d000164 weight likelihood center omega -
        _root_.GD.N0230.N0617.d000164 weight' likelihood center omega| ≤
      B * _root_.GD.N0230.N0618.d000191 weight weight' likelihood omega := by
  unfold _root_.GD.N0230.N0617.d000164 _root_.GD.N0230.N0618.d000191
  rw [← Finset.sum_sub_distrib]
  rw [show
      (∑ i, (weight i * likelihood i omega * center i -
          weight' i * likelihood i omega * center i)) =
        ∑ i, (weight i - weight' i) * likelihood i omega * center i by
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  calc
    |∑ i, (weight i - weight' i) * likelihood i omega * center i| ≤
        ∑ i, |(weight i - weight' i) * likelihood i omega * center i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |weight i - weight' i| * likelihood i omega * |center i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_mul, abs_of_nonneg (hlikelihood i omega)]
    _ ≤ ∑ i, |weight i - weight' i| * likelihood i omega * B := by
      exact Finset.sum_le_sum fun i hi ↦
        mul_le_mul_of_nonneg_left (hcenter i)
          (mul_nonneg (abs_nonneg _) (hlikelihood i omega))
    _ = B * ∑ i, |weight i - weight' i| * likelihood i omega := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring



theorem d000196
    (weight : I → ℝ) (likelihood : I → Omega → ℝ)
    (center : I → ℝ) (B : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihood : ∀ i omega, 0 ≤ likelihood i omega)
    (hB : 0 ≤ B) (hcenter : ∀ i, |center i| ≤ B) (omega : Omega) :
    |_root_.GD.N0230.N0617.d000166 weight likelihood center omega| ≤ B := by
  have hmass := _root_.GD.N0230.N0617.d000169
    weight likelihood hweight hlikelihood omega
  have hsumNonneg :
      0 ≤ ∑ i, weight i * likelihood i omega :=
    Finset.sum_nonneg fun i _ ↦
      mul_nonneg (hweight i) (hlikelihood i omega)
  have hmoment :
      |_root_.GD.N0230.N0617.d000164 weight likelihood center omega| ≤
        B * ∑ i, weight i * likelihood i omega := by
    unfold _root_.GD.N0230.N0617.d000164
    calc
      |∑ i, weight i * likelihood i omega * center i| ≤
          ∑ i, |weight i * likelihood i omega * center i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, weight i * likelihood i omega * |center i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_mul, abs_of_nonneg (hweight i),
          abs_of_nonneg (hlikelihood i omega)]
      _ ≤ ∑ i, weight i * likelihood i omega * B := by
        exact Finset.sum_le_sum fun i hi ↦
          mul_le_mul_of_nonneg_left (hcenter i)
            (mul_nonneg (hweight i) (hlikelihood i omega))
      _ = B * ∑ i, weight i * likelihood i omega := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  unfold _root_.GD.N0230.N0617.d000166
  rw [abs_div, abs_of_pos hmass]
  apply (div_le_iff₀ hmass).2
  calc
    |_root_.GD.N0230.N0617.d000164 weight likelihood center omega| ≤
        B * ∑ i, weight i * likelihood i omega := hmoment
    _ ≤ B * _root_.GD.N0230.N0617.d000163 weight likelihood omega := by
      unfold _root_.GD.N0230.N0617.d000163
      nlinarith



theorem d000197
    (weight weight' : I → ℝ) (likelihood : I → Omega → ℝ)
    (center : I → ℝ) (B : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweight' : ∀ i, 0 ≤ weight' i)
    (hlikelihood : ∀ i omega, 0 ≤ likelihood i omega)
    (hB : 0 ≤ B) (hcenter : ∀ i, |center i| ≤ B) (omega : Omega) :
    |_root_.GD.N0230.N0617.d000166 weight likelihood center omega -
        _root_.GD.N0230.N0617.d000166 weight' likelihood center omega| ≤
      2 * B * _root_.GD.N0230.N0618.d000191 weight weight' likelihood omega := by
  let M := _root_.GD.N0230.N0617.d000163 weight likelihood omega
  let M' := _root_.GD.N0230.N0617.d000163 weight' likelihood omega
  let q := _root_.GD.N0230.N0617.d000166 weight likelihood center omega
  let q' := _root_.GD.N0230.N0617.d000166 weight' likelihood center omega
  let A := _root_.GD.N0230.N0618.d000191 weight weight' likelihood omega
  have hM : 0 < M := _root_.GD.N0230.N0617.d000169
    weight likelihood hweight hlikelihood omega
  have hM' : 0 < M' := _root_.GD.N0230.N0617.d000169
    weight' likelihood hweight' hlikelihood omega
  have hMone : 1 ≤ M := _root_.GD.N0230.N0617.d000168
    weight likelihood hweight hlikelihood omega
  have hA : 0 ≤ A := _root_.GD.N0230.N0618.d000193
    weight weight' likelihood hlikelihood omega
  have hq' : |q'| ≤ B := _root_.GD.N0230.N0618.d000196
    weight' likelihood center B hweight' hlikelihood hB hcenter omega
  have hmoment := _root_.GD.N0230.N0618.d000195
    weight weight' likelihood center B hlikelihood hcenter omega
  have hmass := _root_.GD.N0230.N0618.d000194
    weight weight' likelihood hlikelihood omega
  have hid :
      q - q' =
        ((_root_.GD.N0230.N0617.d000164 weight likelihood center omega -
            _root_.GD.N0230.N0617.d000164 weight' likelihood center omega) -
          q' * (M - M')) / M := by
    have hmass0 : _root_.GD.N0230.N0617.d000163 weight likelihood omega ≠ 0 :=
      (_root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood omega).ne'
    have hmass0' : _root_.GD.N0230.N0617.d000163 weight' likelihood omega ≠ 0 :=
      (_root_.GD.N0230.N0617.d000169 weight' likelihood hweight' hlikelihood omega).ne'
    dsimp [q, q', M, M']
    unfold _root_.GD.N0230.N0617.d000166
    field_simp [hmass0, hmass0']
    ring
  rw [hid, abs_div, abs_of_pos hM]
  apply (div_le_iff₀ hM).2
  calc
    |(_root_.GD.N0230.N0617.d000164 weight likelihood center omega -
          _root_.GD.N0230.N0617.d000164 weight' likelihood center omega) -
        q' * (M - M')| ≤
        |_root_.GD.N0230.N0617.d000164 weight likelihood center omega -
          _root_.GD.N0230.N0617.d000164 weight' likelihood center omega| +
          |q' * (M - M')| := abs_sub _ _
    _ = |_root_.GD.N0230.N0617.d000164 weight likelihood center omega -
          _root_.GD.N0230.N0617.d000164 weight' likelihood center omega| +
          |q'| * |M - M'| := by rw [abs_mul]
    _ ≤ B * A + B * A := by
      exact add_le_add hmoment
        (mul_le_mul hq' hmass (abs_nonneg _) hB)
    _ = 2 * B * A := by ring
    _ ≤ (2 * B * A) * M := by
      exact le_mul_of_one_le_right
        (mul_nonneg (mul_nonneg (by norm_num) hB) hA) hMone




theorem d000198
    (weight weight' : I → ℝ) (likelihood : I → Omega → ℝ)
    (center : I → ℝ) (B : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweight' : ∀ i, 0 ≤ weight' i)
    (hlikelihood : ∀ i omega, 0 ≤ likelihood i omega)
    (hB : 0 ≤ B) (hcenter : ∀ i, |center i| ≤ B) (omega : Omega) :
    (_root_.GD.N0230.N0617.d000166 weight likelihood center omega -
        _root_.GD.N0230.N0617.d000166 weight' likelihood center omega) ^ 2 ≤
      4 * B ^ 2 *
        _root_.GD.N0230.N0618.d000191 weight weight' likelihood omega := by
  let q := _root_.GD.N0230.N0617.d000166 weight likelihood center omega
  let q' := _root_.GD.N0230.N0617.d000166 weight' likelihood center omega
  let A := _root_.GD.N0230.N0618.d000191 weight weight' likelihood omega
  have hA : 0 ≤ A := _root_.GD.N0230.N0618.d000193
    weight weight' likelihood hlikelihood omega
  have hlocal : |q - q'| ≤ 2 * B * A :=
    _root_.GD.N0230.N0618.d000197
      weight weight' likelihood center B hweight hweight'
        hlikelihood hB hcenter omega
  have hq : |q| ≤ B := _root_.GD.N0230.N0618.d000196
    weight likelihood center B hweight hlikelihood hB hcenter omega
  have hq' : |q'| ≤ B := _root_.GD.N0230.N0618.d000196
    weight' likelihood center B hweight' hlikelihood hB hcenter omega
  have hglobal : |q - q'| ≤ 2 * B := by
    calc
      |q - q'| ≤ |q| + |q'| := abs_sub q q'
      _ ≤ B + B := add_le_add hq hq'
      _ = 2 * B := by ring
  rw [← sq_abs (q - q'), pow_two]
  calc
    |q - q'| * |q - q'| ≤ (2 * B) * (2 * B * A) :=
      mul_le_mul hglobal hlocal (abs_nonneg _)
        (mul_nonneg (by positivity) hB)
    _ = 4 * B ^ 2 * A := by ring



theorem d000199
    (mu : Measure Omega) (weight weight' : I → ℝ)
    (likelihood : I → Omega → ℝ)
    (hlikelihoodInt : ∀ i, Integrable (likelihood i) mu) :
    Integrable (_root_.GD.N0230.N0618.d000191 weight weight' likelihood) mu := by
  unfold _root_.GD.N0230.N0618.d000191
  apply integrable_finsetSum
  intro i hi
  exact (hlikelihoodInt i).const_mul |weight i - weight' i|



theorem d000200
    (mu : Measure Omega) (weight weight' : I → ℝ)
    (likelihood : I → Omega → ℝ)
    (hlikelihoodInt : ∀ i, Integrable (likelihood i) mu)
    (hlikelihoodIntegral : ∀ i, ∫ omega, likelihood i omega ∂mu = 1) :
    ∫ omega, _root_.GD.N0230.N0618.d000191 weight weight' likelihood omega ∂mu =
      ∑ i, |weight i - weight' i| := by
  unfold _root_.GD.N0230.N0618.d000191
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul, hlikelihoodIntegral i, mul_one]
  · intro i hi
    exact (hlikelihoodInt i).const_mul |weight i - weight' i|






theorem d000201
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (weight weight' : I → ℝ) (likelihood : I → Omega → ℝ)
    (center : I → ℝ) (B : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweight' : ∀ i, 0 ≤ weight' i)
    (hlikelihood : ∀ i omega, 0 ≤ likelihood i omega)
    (hlikelihoodMeas : ∀ i, Measurable (likelihood i))
    (hlikelihoodInt : ∀ i, Integrable (likelihood i) mu)
    (hlikelihoodIntegral : ∀ i, ∫ omega, likelihood i omega ∂mu = 1)
    (hB : 0 ≤ B) (hcenter : ∀ i, |center i| ≤ B) :
    ∫ omega,
        (_root_.GD.N0230.N0617.d000166 weight likelihood center omega -
          _root_.GD.N0230.N0617.d000166 weight' likelihood center omega) ^ 2 ∂mu ≤
      4 * B ^ 2 * ∑ i, |weight i - weight' i| := by
  have hleft : Integrable (fun omega ↦
      (_root_.GD.N0230.N0617.d000166 weight likelihood center omega -
        _root_.GD.N0230.N0617.d000166 weight' likelihood center omega) ^ 2) mu :=
    ((_root_.GD.N0230.N0617.d000181 mu weight likelihood center
        hweight hlikelihood hlikelihoodMeas).sub
      (_root_.GD.N0230.N0617.d000181 mu weight' likelihood center
        hweight' hlikelihood hlikelihoodMeas)).integrable_sq
  have hdisc := _root_.GD.N0230.N0618.d000199
    mu weight weight' likelihood hlikelihoodInt
  have hright : Integrable (fun omega ↦
      4 * B ^ 2 * _root_.GD.N0230.N0618.d000191
        weight weight' likelihood omega) mu :=
    hdisc.const_mul (4 * B ^ 2)
  calc
    ∫ omega,
        (_root_.GD.N0230.N0617.d000166 weight likelihood center omega -
          _root_.GD.N0230.N0617.d000166 weight' likelihood center omega) ^ 2 ∂mu ≤
        ∫ omega, 4 * B ^ 2 *
          _root_.GD.N0230.N0618.d000191 weight weight' likelihood omega ∂mu := by
      exact integral_mono hleft hright fun omega ↦
        _root_.GD.N0230.N0618.d000198
          weight weight' likelihood center B hweight hweight'
            hlikelihood hB hcenter omega
    _ = 4 * B ^ 2 *
        ∫ omega, _root_.GD.N0230.N0618.d000191
          weight weight' likelihood omega ∂mu := by
      rw [integral_const_mul]
    _ = 4 * B ^ 2 * ∑ i, |weight i - weight' i| := by
      rw [_root_.GD.N0230.N0618.d000200
        mu weight weight' likelihood hlikelihoodInt hlikelihoodIntegral]

end

end N0618
end N0230
end GD

#print axioms _root_.GD.N0230.N0618.d000192
#print axioms _root_.GD.N0230.N0618.d000201
