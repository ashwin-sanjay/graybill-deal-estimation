import GD.Module0014
import GD.Module0133
















open MeasureTheory
open scoped ENNReal

namespace GD
namespace N0230
namespace N0670

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0718

variable {Omega : Type*} [MeasurableSpace Omega]


def d001646 {mu0 : Measure Omega}
    (p q : _root_.GD.N0230.N0602.d000116 mu0) : _root_.GD.N0230.N0602.d000116 mu0 :=
  (1 / 2 : ℝ) • (p - q)





theorem d001647
    {mu0 mu : Measure Omega} (hmu : mu ≪ mu0)
    (target : ℝ) (p q : _root_.GD.N0230.N0602.d000116 mu0) :
    _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target (_root_.GD.N0230.N0718.d001528 p q) +
        _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu 0 (_root_.GD.N0230.N0670.d001646 p q) =
      ENNReal.ofReal (1 / 2 : ℝ) *
          _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target p +
        ENNReal.ofReal (1 / 2 : ℝ) *
          _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target q := by
  have hmid0 : ∀ᵐ omega ∂mu0,
      (_root_.GD.N0230.N0718.d001528 p q : _root_.GD.N0230.N0602.d000116 mu0) omega =
        (1 / 2 : ℝ) * p omega + (1 / 2 : ℝ) * q omega := by
    filter_upwards [Lp.coeFn_add ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • q),
      Lp.coeFn_smul (1 / 2 : ℝ) p,
      Lp.coeFn_smul (1 / 2 : ℝ) q] with omega hadd hp hq
    simp only [_root_.GD.N0230.N0718.d001528, hadd, hp, hq, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
  have hdiff0 : ∀ᵐ omega ∂mu0,
      (_root_.GD.N0230.N0670.d001646 p q : _root_.GD.N0230.N0602.d000116 mu0) omega =
        (1 / 2 : ℝ) * (p omega - q omega) := by
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (p - q),
      Lp.coeFn_sub p q] with omega hsmul hsub
    simp only [_root_.GD.N0230.N0670.d001646, hsmul, hsub, Pi.smul_apply, smul_eq_mul,
      Pi.sub_apply]
  have hmid := hmu.ae_le hmid0
  have hdiff := hmu.ae_le hdiff0
  have hmidMeas := _root_.GD.N0230.N0602.d000119 hmu target
    (_root_.GD.N0230.N0718.d001528 p q)
  have hdiffMeas := _root_.GD.N0230.N0602.d000119 hmu 0
    (_root_.GD.N0230.N0670.d001646 p q)
  have hpMeas := _root_.GD.N0230.N0602.d000119 hmu target p
  have hqMeas := _root_.GD.N0230.N0602.d000119 hmu target q
  unfold _root_.GD.N0230.N0602.d000117
  calc
    (∫⁻ omega,
          ENNReal.ofReal (((_root_.GD.N0230.N0718.d001528 p q : _root_.GD.N0230.N0602.d000116 mu0) omega - target) ^ 2)
        ∂mu) +
        ∫⁻ omega,
          ENNReal.ofReal (((_root_.GD.N0230.N0670.d001646 p q : _root_.GD.N0230.N0602.d000116 mu0) omega - 0) ^ 2)
        ∂mu =
        ∫⁻ omega,
          (ENNReal.ofReal
              (((_root_.GD.N0230.N0718.d001528 p q : _root_.GD.N0230.N0602.d000116 mu0) omega - target) ^ 2) +
            ENNReal.ofReal
              (((_root_.GD.N0230.N0670.d001646 p q : _root_.GD.N0230.N0602.d000116 mu0) omega - 0) ^ 2)) ∂mu := by
      rw [lintegral_add_left' hmidMeas]
    _ = ∫⁻ omega,
          (ENNReal.ofReal (1 / 2 : ℝ) *
              ENNReal.ofReal ((p omega - target) ^ 2) +
            ENNReal.ofReal (1 / 2 : ℝ) *
              ENNReal.ofReal ((q omega - target) ^ 2)) ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [hmid, hdiff] with omega hmidOmega hdiffOmega
      rw [hmidOmega, hdiffOmega]
      simp only [sub_zero]
      rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (sq_nonneg _))
          (mul_nonneg (by norm_num) (sq_nonneg _))]
      congr 1
      ring
    _ = ENNReal.ofReal (1 / 2 : ℝ) *
          ∫⁻ omega, ENNReal.ofReal ((p omega - target) ^ 2) ∂mu +
        ENNReal.ofReal (1 / 2 : ℝ) *
          ∫⁻ omega, ENNReal.ofReal ((q omega - target) ^ 2) ∂mu := by
      rw [lintegral_add_left']
      · rw [lintegral_const_mul'' _ hpMeas,
          lintegral_const_mul'' _ hqMeas]
      · exact hpMeas.const_mul _


theorem d001648
    {mu0 mu : Measure Omega} (p q : _root_.GD.N0230.N0602.d000116 mu0) :
    0 ≤ _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu 0 (_root_.GD.N0230.N0670.d001646 p q) :=
  bot_le


theorem d001649
    {mu0 mu : Measure Omega} (hmu : mu ≪ mu0)
    (target : ℝ) (p q : _root_.GD.N0230.N0602.d000116 mu0)
    (hp : _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target p ≠ ⊤)
    (hq : _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target q ≠ ⊤) :
    (_root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target
        (_root_.GD.N0230.N0718.d001528 p q)).toReal +
        (_root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu 0
          (_root_.GD.N0230.N0670.d001646 p q)).toReal =
      ((_root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target p).toReal +
        (_root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target q).toReal) / 2 := by
  have hEq := _root_.GD.N0230.N0670.d001647 hmu target p q
  have hmid : _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target
      (_root_.GD.N0230.N0718.d001528 p q) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _
      (_root_.GD.N0230.N0602.d000121 hmu target p q
        (by norm_num) (by norm_num) (by norm_num))
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq⟩
  have htax : _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu 0
      (_root_.GD.N0230.N0670.d001646 p q) ≠ ⊤ := by
    have hle : _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu 0
        (_root_.GD.N0230.N0670.d001646 p q) ≤
        ENNReal.ofReal (1 / 2 : ℝ) *
            _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target p +
          ENNReal.ofReal (1 / 2 : ℝ) *
            _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu target q := by
      rw [← hEq]
      exact le_add_left le_rfl
    apply ne_top_of_le_ne_top _ hle
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq⟩
  have hEqReal := congrArg ENNReal.toReal hEq
  rw [ENNReal.toReal_add hmid htax,
    ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hEqReal
  norm_num at hEqReal ⊢
  linarith

end

end N0670
end N0230
end GD

#print axioms _root_.GD.N0230.N0670.d001647
#print axioms _root_.GD.N0230.N0670.d001649
