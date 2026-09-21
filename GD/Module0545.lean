import GD.Module0544
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0218
noncomputable section
open _root_.GD.N0208.N0455
open _root_.GD.N0221


def d008109 (s : ℝ) : ℝ := Real.exp s / (1 + Real.exp s) ^ 2

theorem d008110 (s : ℝ) : 0 < _root_.GD.N0218.d008109 s := by
  unfold _root_.GD.N0218.d008109
  positivity

@[fun_prop] theorem d008111 : Measurable _root_.GD.N0218.d008109 := by
  unfold _root_.GD.N0218.d008109
  fun_prop

theorem d008112 (s : ℝ) :
    _root_.GD.N0218.d008109 s = Real.sigmoid s * (1 - Real.sigmoid s) := by
  rw [Real.sigmoid_def, Real.exp_neg]
  unfold _root_.GD.N0218.d008109
  have hp := Real.exp_pos s
  field_simp
  ring

theorem d008113 (s : ℝ) : _root_.GD.N0218.d008109 (-s) = _root_.GD.N0218.d008109 s := by
  rw [_root_.GD.N0218.d008112, _root_.GD.N0218.d008112, Real.sigmoid_neg]
  ring

theorem d008114 (s : ℝ) :
    HasDerivAt Real.sigmoid (_root_.GD.N0218.d008109 s) s := by
  rw [_root_.GD.N0218.d008112]
  exact Real.hasDerivAt_sigmoid s

theorem d008115 : (∫ s : ℝ, _root_.GD.N0218.d008109 s) = 1 := by
  have hhalf : (∫ s : ℝ in Ioi 0, _root_.GD.N0218.d008109 s) = 1 / 2 := by
    have h := integral_Ioi_of_hasDerivAt_of_nonneg'
      (fun s (_ : s ∈ Ici (0 : ℝ)) => _root_.GD.N0218.d008114 s)
      (fun s (_ : s ∈ Ioi (0 : ℝ)) => (_root_.GD.N0218.d008110 s).le)
      Real.tendsto_sigmoid_atTop
    norm_num at h ⊢
    exact h
  have he (s : ℝ) : _root_.GD.N0218.d008109 s = _root_.GD.N0218.d008109 |s| := by
    rcases le_total 0 s with hs | hs
    · rw [abs_of_nonneg hs]
    · rw [abs_of_nonpos hs, _root_.GD.N0218.d008113]
  calc
    _ = ∫ s : ℝ, _root_.GD.N0218.d008109 |s| := integral_congr_ae (ae_of_all _ he)
    _ = 2 * ∫ s : ℝ in Ioi 0, _root_.GD.N0218.d008109 s := integral_comp_abs
    _ = 1 := by rw [hhalf]; norm_num

theorem d008116 : Integrable _root_.GD.N0218.d008109 := by
  by_contra hn
  have hz := integral_undef hn
  rw [_root_.GD.N0218.d008115] at hz
  norm_num at hz

theorem d008117 :
    (∫⁻ s : ℝ, ENNReal.ofReal (_root_.GD.N0218.d008109 s)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal _root_.GD.N0218.d008116
    (ae_of_all _ (fun s => (_root_.GD.N0218.d008110 s).le)), _root_.GD.N0218.d008115]
  norm_num

def d008118 (K s : ℝ) : ℝ := _root_.GD.N0218.d008109 s * (_root_.GD.N0208.N0455.d007937 K s) ^ 2

theorem d008119 (K s : ℝ) : 0 ≤ _root_.GD.N0208.N0455.d007937 K s ∧ _root_.GD.N0208.N0455.d007937 K s ≤ 1 := by
  unfold _root_.GD.N0208.N0455.d007937
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

@[fun_prop] theorem d008120 (K : ℝ) :
    Measurable (_root_.GD.N0218.d008118 K) := by
  unfold _root_.GD.N0218.d008118
  exact _root_.GD.N0218.d008111.mul ((_root_.GD.N0208.N0455.d007938 K).pow_const 2)

theorem d008121 (K s : ℝ) : 0 ≤ _root_.GD.N0218.d008118 K s := by
  exact mul_nonneg (_root_.GD.N0218.d008110 s).le (sq_nonneg _)

theorem d008122 (K s : ℝ) : _root_.GD.N0218.d008118 K s ≤ _root_.GD.N0218.d008109 s := by
  have hc := _root_.GD.N0218.d008119 K s
  have hs : (_root_.GD.N0208.N0455.d007937 K s) ^ 2 ≤ 1 := by nlinarith
  simpa only [_root_.GD.N0218.d008118, mul_one] using
    mul_le_mul_of_nonneg_left hs (_root_.GD.N0218.d008110 s).le

theorem d008123 (K : ℝ) :
    (∫⁻ s : ℝ, ENNReal.ofReal (_root_.GD.N0218.d008118 K s)) ≤ 1 := by
  calc
    _ ≤ ∫⁻ s : ℝ, ENNReal.ofReal (_root_.GD.N0218.d008109 s) :=
      lintegral_mono (fun s => ENNReal.ofReal_le_ofReal (_root_.GD.N0218.d008122 K s))
    _ = 1 := _root_.GD.N0218.d008117



theorem d008124 (K N : ℝ) (hN : 0 < N) :
    (∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
      ENNReal.ofReal (_root_.GD.N0218.d008118 K s /
        (2 * Real.pi * Real.cosh ((v + w) / 2))) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) ≤
      ENNReal.ofReal (256 / (Real.pi * N)) :=
  _root_.GD.N0221.d008107 N hN (_root_.GD.N0218.d008118 K)
    (_root_.GD.N0218.d008120 K) (_root_.GD.N0218.d008121 K)
    (_root_.GD.N0218.d008123 K)



theorem d008125 (K : ℝ → ℝ) :
    Tendsto (fun N : ℝ => ∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
      ENNReal.ofReal (_root_.GD.N0218.d008118 (K N) s /
        (2 * Real.pi * Real.cosh ((v + w) / 2))) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2)) atTop (𝓝 0) := by
  have hh : Tendsto (fun N : ℝ => (256 / Real.pi) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto (fun N : ℝ => ENNReal.ofReal (256 / (Real.pi * N)))
      atTop (𝓝 0) := by
    have heq (N : ℝ) : 256 / (Real.pi * N) = (256 / Real.pi) / N := by ring
    simpa only [heq, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
  exact _root_.GD.N0218.d008124 (K N) N hN


theorem d008126 (K N : ℝ) :
    (∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
      ENNReal.ofReal (_root_.GD.N0218.d008109 s /
        (2 * Real.pi * Real.cosh ((v + w) / 2))) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 K s * _root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 K s * _root_.GD.N0208.N0455.d007937 N w) ^ 2)) =
    ∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
      ENNReal.ofReal (_root_.GD.N0218.d008118 K s /
        (2 * Real.pi * Real.cosh ((v + w) / 2))) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 N w) ^ 2) := by
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro v
  apply lintegral_congr
  intro w
  rw [← ENNReal.ofReal_mul (div_nonneg (_root_.GD.N0218.d008110 s).le (by positivity)),
    ← ENNReal.ofReal_mul (div_nonneg (_root_.GD.N0218.d008121 K s) (by positivity))]
  congr 1
  unfold _root_.GD.N0218.d008118
  ring

theorem d008127 (K N : ℝ) (hN : 0 < N) :
    (∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
      ENNReal.ofReal (_root_.GD.N0218.d008109 s /
        (2 * Real.pi * Real.cosh ((v + w) / 2))) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 K s * _root_.GD.N0208.N0455.d007937 N v - _root_.GD.N0208.N0455.d007937 K s * _root_.GD.N0208.N0455.d007937 N w) ^ 2)) ≤
      ENNReal.ofReal (256 / (Real.pi * N)) := by
  rw [_root_.GD.N0218.d008126]
  exact _root_.GD.N0218.d008124 K N hN

theorem d008128 (K : ℝ → ℝ) :
    Tendsto (fun N : ℝ => ∫⁻ s : ℝ, ∫⁻ v : ℝ, ∫⁻ w : ℝ,
      ENNReal.ofReal (_root_.GD.N0218.d008109 s /
        (2 * Real.pi * Real.cosh ((v + w) / 2))) *
        ENNReal.ofReal ((_root_.GD.N0208.N0455.d007937 (K N) s * _root_.GD.N0208.N0455.d007937 N v -
          _root_.GD.N0208.N0455.d007937 (K N) s * _root_.GD.N0208.N0455.d007937 N w) ^ 2)) atTop (𝓝 0) := by
  simp_rw [_root_.GD.N0218.d008126]
  exact _root_.GD.N0218.d008125 K

end
end GD.N0218

#print axioms _root_.GD.N0218.d008112
#print axioms _root_.GD.N0218.d008113
#print axioms _root_.GD.N0218.d008114
#print axioms _root_.GD.N0218.d008115
#print axioms _root_.GD.N0218.d008116
#print axioms _root_.GD.N0218.d008117
#print axioms _root_.GD.N0218.d008123
#print axioms _root_.GD.N0218.d008124
#print axioms _root_.GD.N0218.d008125
#print axioms _root_.GD.N0218.d008126
#print axioms _root_.GD.N0218.d008127
#print axioms _root_.GD.N0218.d008128
