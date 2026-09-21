import GD.Module0147












open Filter MeasureTheory
open scoped ENNReal

namespace GD
namespace N0230
namespace N0671

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0670

variable {Omega : Type*} [MeasurableSpace Omega]



theorem d001650
    {mu0 mu : Measure Omega} (hmu : mu ≪ mu0) (hmu0 : mu0 ≪ mu)
    {p q : _root_.GD.N0230.N0602.d000116 mu0}
    (hzero : _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu 0
      (_root_.GD.N0230.N0670.d001646 p q) = 0) :
    p = q := by
  have hmeas := _root_.GD.N0230.N0602.d000119 hmu 0
    (_root_.GD.N0230.N0670.d001646 p q)
  have hzeroIntegrand :
      (fun omega ↦ ENNReal.ofReal
        (((_root_.GD.N0230.N0670.d001646 p q : _root_.GD.N0230.N0602.d000116 mu0) omega - 0) ^ 2))
        =ᵐ[mu] fun _ ↦ 0 := by
    exact (lintegral_eq_zero_iff' hmeas).1 hzero
  have hhalfMu :
      (fun omega ↦ (_root_.GD.N0230.N0670.d001646 p q : _root_.GD.N0230.N0602.d000116 mu0) omega)
        =ᵐ[mu] fun _ ↦ 0 := by
    filter_upwards [hzeroIntegrand] with omega homega
    have hle :
        (((_root_.GD.N0230.N0670.d001646 p q : _root_.GD.N0230.N0602.d000116 mu0) omega) ^ 2) ≤ 0 := by
      simpa only [sub_zero] using ENNReal.ofReal_eq_zero.mp homega
    exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
  have hhalfMu0 :
      (fun omega ↦ (_root_.GD.N0230.N0670.d001646 p q : _root_.GD.N0230.N0602.d000116 mu0) omega)
        =ᵐ[mu0] fun _ ↦ 0 :=
    hmu0.ae_le hhalfMu
  have hhalf : _root_.GD.N0230.N0670.d001646 p q = 0 := by
    apply Lp.ext
    exact hhalfMu0.trans (Lp.coeFn_zero ℝ 2 mu0).symm
  have hpqZero : p - q = 0 := by
    have hsmul : (1 / 2 : ℝ) • (p - q) = 0 := by
      simpa [_root_.GD.N0230.N0670.d001646] using hhalf
    exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)
  exact sub_eq_zero.mp hpqZero



theorem d001651
    {mu0 mu : Measure Omega} (hmu : mu ≪ mu0) (hmu0 : mu0 ≪ mu)
    {p q : _root_.GD.N0230.N0602.d000116 mu0} (hpq : p ≠ q) :
    0 < _root_.GD.N0230.N0602.d000117 (μ₀ := mu0) mu 0
      (_root_.GD.N0230.N0670.d001646 p q) := by
  exact bot_lt_iff_ne_bot.2 fun hzero ↦
    hpq (_root_.GD.N0230.N0671.d001650
      hmu hmu0 hzero)

end

end N0671
end N0230
end GD

#print axioms _root_.GD.N0230.N0671.d001650
#print axioms _root_.GD.N0230.N0671.d001651
