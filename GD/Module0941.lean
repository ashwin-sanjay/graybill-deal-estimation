import GD.Module0940
import Mathlib.Tactic

















open MeasureTheory ProbabilityTheory

namespace GD
namespace N0232
namespace N0720
namespace N1213

noncomputable section

open _root_.GD.N0107 _root_.GD.N0137
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1425


def d014727
    (m n : ℕ) (mu sigma tau : ℝ) :
    _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n → _root_.GD.N0232.N0720.N1436.d013217 :=
  fun omega =>
    (_root_.GD.N0107.d009039 m n mu sigma tau
        (_root_.GD.N0107.d009046 m n sigma tau) omega,
      _root_.GD.N0107.d009040 m n mu sigma tau
        (_root_.GD.N0107.d009046 m n sigma tau) omega)

@[fun_prop] theorem d014728
    (m n : ℕ) (mu sigma tau : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1213.d014727 m n mu sigma tau) := by
  exact measurable_snd.comp
    (_root_.GD.N0107.d009041 m n mu sigma tau
      (_root_.GD.N0107.d009046 m n sigma tau)
      (_root_.GD.N0107.d009045 m n sigma tau))




theorem d014729
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (phi : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hphi : Measurable phi) :
    (∫ omega,
        _root_.GD.N0107.d009038 m n mu sigma tau
              (_root_.GD.N0107.d009046 m n sigma tau)
              (_root_.GD.N0107.d009045 m n sigma tau) omega ^ 2 *
          phi (_root_.GD.N0232.N0720.N1213.d014727 m n mu sigma tau omega)
      ∂_root_.GD.N0107.d009030 m n mu sigma tau) =
      _root_.GD.N0107.d009045 m n sigma tau *
        ∫ x, phi x
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n
            (_root_.GD.N0107.d009046 m n sigma tau) := by
  have ht0 : 0 < _root_.GD.N0107.d009046 m n sigma tau :=
    _root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau
  have ht1 : _root_.GD.N0107.d009046 m n sigma tau < 1 :=
    _root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau
  have hsource := _root_.GD.N0107.d009052
    m n hm hn mu sigma tau hsigma htau phi hphi
  have hprojective :=
    _root_.GD.N0232.N0720.N1425.d014723
      hm hn ht0 ht1 phi hphi
  have hprojective' :
      _root_.GD.N0120.d008809
          (((m - 1 : ℕ) : ℝ) / 2)
          (((n - 1 : ℕ) : ℝ) / 2)
          (_root_.GD.N0107.d009046 m n sigma tau) phi =
        ∫ x, phi x
          ∂_root_.GD.N0232.N0720.N1436.d013289 m n
            (_root_.GD.N0107.d009046 m n sigma tau) := by
    simpa [_root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208] using hprojective
  rw [hprojective'] at hsource
  simpa [_root_.GD.N0232.N0720.N1213.d014727] using hsource


def d014730
    (m n : ℕ) (mu sigma tau : ℝ) :
    Measure (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :=
  (_root_.GD.N0107.d009030 m n mu sigma tau).withDensity
    (fun omega => ENNReal.ofReal
      (_root_.GD.N0107.d009038 m n mu sigma tau
          (_root_.GD.N0107.d009046 m n sigma tau)
          (_root_.GD.N0107.d009045 m n sigma tau) omega ^ 2))




theorem d014731
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    Measure.map (_root_.GD.N0232.N0720.N1213.d014727 m n mu sigma tau)
        (_root_.GD.N0232.N0720.N1213.d014730 m n mu sigma tau) =
      ENNReal.ofReal (_root_.GD.N0107.d009045 m n sigma tau) •
        _root_.GD.N0232.N0720.N1436.d013289 m n
          (_root_.GD.N0107.d009046 m n sigma tau) := by
  let t := _root_.GD.N0107.d009046 m n sigma tau
  let Sigma := _root_.GD.N0107.d009045 m n sigma tau
  let D := _root_.GD.N0107.d009038 m n mu sigma tau t Sigma
  let P := _root_.GD.N0107.d009030 m n mu sigma tau
  have ht0 : 0 < t :=
    _root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau
  have ht1 : t < 1 :=
    _root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau
  have hSigma : 0 < Sigma :=
    _root_.GD.N0107.d009049 (by omega) (by omega) hsigma htau
  have hD : MemLp D 2 P := by
    have hcarrier :=
      (_root_.GD.N0107.d012748
        m n hm hn mu sigma tau hsigma htau
        (fun _ : _root_.GD.N0232.N0720.N1436.d013217 => (1 : ℝ)) measurable_const
        (B := 1) (by norm_num) (fun _ => by norm_num)).2
    simpa [D, P, t, Sigma] using hcarrier
  have hDmeas : Measurable D := by
    exact measurable_fst.comp
      (_root_.GD.N0107.d009041 m n mu sigma tau t Sigma)
  letI : IsFiniteMeasure (_root_.GD.N0232.N0720.N1213.d014730 m n mu sigma tau) := by
    unfold _root_.GD.N0232.N0720.N1213.d014730
    exact isFiniteMeasure_withDensity_ofReal
      hD.integrable_sq.hasFiniteIntegral
  letI : IsFiniteMeasure
      (_root_.GD.N0232.N0720.N1436.d013289 m n t) :=
    _root_.GD.N0232.N0720.N1434.d013560
      hm hn ht0 ht1
  letI : IsFiniteMeasure
      (ENNReal.ofReal Sigma • _root_.GD.N0232.N0720.N1436.d013289 m n t) :=
    Measure.smul_finite _ (by simp)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map
    (_root_.GD.N0232.N0720.N1213.d014728 m n mu sigma tau).aemeasurable
    f.continuous.aestronglyMeasurable]
  unfold _root_.GD.N0232.N0720.N1213.d014730
  rw [integral_withDensity_eq_integral_toReal_smul
    (hDmeas.pow_const 2).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  rw [integral_smul_measure,
    ENNReal.toReal_ofReal hSigma.le]
  exact _root_.GD.N0232.N0720.N1213.d014729
    m n hm hn mu sigma tau hsigma htau f
      f.continuous.measurable





def d014732 (S p : ℝ) : ℝ :=
  Real.sqrt (S * (1 - p))



def d014733 (S p : ℝ) : ℝ :=
  Real.sqrt (S * p)

theorem d014734
    {S p : ℝ} (hS : 0 < S) (hp1 : p < 1) :
    0 < _root_.GD.N0232.N0720.N1213.d014732 S p := by
  exact Real.sqrt_pos.2 (mul_pos hS (sub_pos.2 hp1))

theorem d014735
    {S p : ℝ} (hS : 0 < S) (hp0 : 0 < p) :
    0 < _root_.GD.N0232.N0720.N1213.d014733 S p := by
  exact Real.sqrt_pos.2 (mul_pos hS hp0)



theorem d014736
    {S p : ℝ} (hS : 0 < S) (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0107.d009045 2 2
        (_root_.GD.N0232.N0720.N1213.d014732 S p) (_root_.GD.N0232.N0720.N1213.d014733 S p) = S / 2 := by
  have hx : (_root_.GD.N0232.N0720.N1213.d014732 S p) ^ 2 = S * (1 - p) := by
    unfold _root_.GD.N0232.N0720.N1213.d014732
    exact Real.sq_sqrt (mul_nonneg hS.le (sub_nonneg.2 hp1.le))
  have hy : (_root_.GD.N0232.N0720.N1213.d014733 S p) ^ 2 = S * p := by
    unfold _root_.GD.N0232.N0720.N1213.d014733
    exact Real.sq_sqrt (mul_nonneg hS.le hp0.le)
  unfold _root_.GD.N0107.d009045 _root_.GD.N0107.d009043 _root_.GD.N0107.d009044
  rw [hx, hy]
  ring



theorem d014737
    {S p : ℝ} (hS : 0 < S) (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0107.d009046 2 2
        (_root_.GD.N0232.N0720.N1213.d014732 S p) (_root_.GD.N0232.N0720.N1213.d014733 S p) = p := by
  rw [_root_.GD.N0107.d009046,
    _root_.GD.N0232.N0720.N1213.d014736 hS hp0 hp1]
  have hy : (_root_.GD.N0232.N0720.N1213.d014733 S p) ^ 2 = S * p := by
    unfold _root_.GD.N0232.N0720.N1213.d014733
    exact Real.sq_sqrt (mul_nonneg hS.le hp0.le)
  unfold _root_.GD.N0107.d009044
  rw [hy]
  field_simp [hS.ne'] <;> norm_num




theorem d014738
    (mu S p : ℝ) (hS : 0 < S) (hp0 : 0 < p) (hp1 : p < 1)
    (phi : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hphi : Measurable phi) :
    (∫ omega,
        _root_.GD.N0107.d009038 2 2 mu
              (_root_.GD.N0232.N0720.N1213.d014732 S p) (_root_.GD.N0232.N0720.N1213.d014733 S p)
              p (S / 2) omega ^ 2 *
          phi
            (_root_.GD.N0107.d009039 2 2 mu
                (_root_.GD.N0232.N0720.N1213.d014732 S p) (_root_.GD.N0232.N0720.N1213.d014733 S p) p omega,
              _root_.GD.N0107.d009040 2 2 mu
                (_root_.GD.N0232.N0720.N1213.d014732 S p) (_root_.GD.N0232.N0720.N1213.d014733 S p) p omega)
      ∂_root_.GD.N0107.d009030 2 2 mu
        (_root_.GD.N0232.N0720.N1213.d014732 S p) (_root_.GD.N0232.N0720.N1213.d014733 S p)) =
      (S / 2) * ∫ x, phi x ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 p := by
  have hsigma : 0 < _root_.GD.N0232.N0720.N1213.d014732 S p :=
    _root_.GD.N0232.N0720.N1213.d014734 hS hp1
  have htau : 0 < _root_.GD.N0232.N0720.N1213.d014733 S p :=
    _root_.GD.N0232.N0720.N1213.d014735 hS hp0
  have h := _root_.GD.N0232.N0720.N1213.d014729
    2 2 (by omega) (by omega) mu
      (_root_.GD.N0232.N0720.N1213.d014732 S p) (_root_.GD.N0232.N0720.N1213.d014733 S p)
      hsigma htau phi hphi
  unfold _root_.GD.N0232.N0720.N1213.d014727 at h
  simp only [_root_.GD.N0232.N0720.N1213.d014737 hS hp0 hp1,
    _root_.GD.N0232.N0720.N1213.d014736 hS hp0 hp1] at h
  exact h


theorem d014739
    (mu S p : ℝ) (hS : 0 < S) (hp0 : 0 < p) (hp1 : p < 1) :
    Measure.map
        (_root_.GD.N0232.N0720.N1213.d014727 2 2 mu
          (_root_.GD.N0232.N0720.N1213.d014732 S p) (_root_.GD.N0232.N0720.N1213.d014733 S p))
        (_root_.GD.N0232.N0720.N1213.d014730 2 2 mu
          (_root_.GD.N0232.N0720.N1213.d014732 S p) (_root_.GD.N0232.N0720.N1213.d014733 S p)) =
      ENNReal.ofReal (S / 2) • _root_.GD.N0232.N0720.N1436.d013289 2 2 p := by
  have h :=
    _root_.GD.N0232.N0720.N1213.d014731
      2 2 (by omega) (by omega) mu
      (_root_.GD.N0232.N0720.N1213.d014732 S p) (_root_.GD.N0232.N0720.N1213.d014733 S p)
      (_root_.GD.N0232.N0720.N1213.d014734 hS hp1)
      (_root_.GD.N0232.N0720.N1213.d014735 hS hp0)
  simpa only [_root_.GD.N0232.N0720.N1213.d014737 hS hp0 hp1,
    _root_.GD.N0232.N0720.N1213.d014736 hS hp0 hp1] using h

end

end N1213
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1213.d014729
#print axioms _root_.GD.N0232.N0720.N1213.d014731
#print axioms _root_.GD.N0232.N0720.N1213.d014738
#print axioms _root_.GD.N0232.N0720.N1213.d014739
