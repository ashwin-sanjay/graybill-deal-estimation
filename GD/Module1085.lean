import GD.Module1084
import Mathlib.MeasureTheory.Function.UniformIntegrable

























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1176

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0232.N0720.N1485
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1175
open _root_.GD.N0232.N0720.N1491




@[simp] theorem d017396
    (k : ℕ) (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    _root_.GD.N0232.N0720.N1491.d017379 k theta ^ 2 = _root_.GD.N0232.N0720.N1491.d017379 k theta := by
  by_cases htheta : theta ∈ _root_.GD.N0232.N0720.N1485.d017359 k
  · simp [_root_.GD.N0232.N0720.N1491.d017379, htheta]
  · simp [_root_.GD.N0232.N0720.N1491.d017379, htheta]



theorem d017397
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    0 ≤ _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1491.d017379 k) x := by
  simpa only [_root_.GD.N0232.N0720.N1176.d017396] using
    _root_.GD.N0232.N0720.N1173.d015941 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1491.d017379 k) x





theorem d017398
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    0 ≤ _root_.GD.N0232.N0720.N1175.d016001 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1491.d017379 k) x := by
  exact div_nonneg (sq_nonneg _)
    (_root_.GD.N0232.N0720.N1176.d017397 k x)










theorem d017399
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (weight : ℕ → _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hdata : ∀ n, _root_.GD.N0232.N0720.N1175.d016005 rho (weight n))
    (hui : UnifIntegrable
      (fun n x ↦ _root_.GD.N0232.N0720.N1175.d016001 rho (weight n) x)
      1 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hpoint : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0720.N1175.d016001 rho (weight n) x)
        atTop (nhds 0)) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1173.d015956 rho (weight n))
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  let f : ℕ → _root_.GD.N0232.N0720.N1173.d015936 → ℝ :=
    fun n x ↦ _root_.GD.N0232.N0720.N1175.d016001 rho (weight n) x
  have hf_integrable : ∀ n, Integrable (f n) (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    intro n
    exact (hdata n).d016007
  have hLp : Tendsto
      (fun n ↦ eLpNorm (f n - (0 : _root_.GD.N0232.N0720.N1173.d015936 → ℝ))
        1 (_root_.GD.N0232.N0720.N1080.d014172 2 2)) atTop (nhds 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae
      (μ := _root_.GD.N0232.N0720.N1080.d014172 2 2) le_rfl ENNReal.one_ne_top
      (fun n ↦ (hf_integrable n).aestronglyMeasurable)
      (MemLp.zero : MemLp (0 : _root_.GD.N0232.N0720.N1173.d015936 → ℝ) 1
        (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    · simpa only [f] using hui
    · simpa only [f, Pi.zero_apply] using hpoint
  have hintegral : Tendsto
      (fun n ↦ ∫ x, f n x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2)
      atTop (nhds 0) := by
    have h := tendsto_integral_of_L1'
      (μ := _root_.GD.N0232.N0720.N1080.d014172 2 2)
      (0 : _root_.GD.N0232.N0720.N1173.d015936 → ℝ)
      (aestronglyMeasurable_zero :
        AEStronglyMeasurable (0 : _root_.GD.N0232.N0720.N1173.d015936 → ℝ)
          (_root_.GD.N0232.N0720.N1080.d014172 2 2))
      (F := f)
      (Filter.Eventually.of_forall hf_integrable)
      hLp
    simpa using h
  simpa only [f, (hdata _).d016006] using hintegral








theorem d017400
    (hdata : ∀ k, _root_.GD.N0232.N0720.N1175.d016005
      _root_.GD.N0232.N0720.N1493.d016104 (_root_.GD.N0232.N0720.N1491.d017379 k))
    (hui : UnifIntegrable
      (fun k x ↦ _root_.GD.N0232.N0720.N1175.d016001
        _root_.GD.N0232.N0720.N1493.d016104 (_root_.GD.N0232.N0720.N1491.d017379 k) x)
      1 (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1173.d015956 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1491.d017379 k))
      atTop (nhds 0) := by
  apply _root_.GD.N0232.N0720.N1176.d017399
    _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1491.d017379 hdata hui
  filter_upwards [_root_.GD.N0232.N0720.N1491.d017395] with x hx
  exact hx.2.2.2

end

end N1176
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1176.d017399
#print axioms _root_.GD.N0232.N0720.N1176.d017400
