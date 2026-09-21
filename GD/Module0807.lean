import GD.Module0019
import GD.Module0805
import GD.Module0731



open Filter MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0719
namespace N0965

noncomputable section

open _root_.GD.N0230.N0591
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0932 _root_.GD.N0232.N0719.N0828

variable {k : ℕ} {sizes : Fin k → ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

private noncomputable local instance d012265 :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010813 _root_.GD.N0232.N0719.d009182
  infer_instance

def d012266 (k : ℕ) (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N0932.d009219 k sizes θ.location θ.scale

theorem d012267 (k : ℕ) (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    0 ≤ _root_.GD.N0232.N0719.N0965.d012266 k sizes θ ω :=
  _root_.GD.N0232.N0719.N0932.d009221 k sizes θ.location θ.scale ω

theorem d012268 (k : ℕ) (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    Measurable (_root_.GD.N0232.N0719.N0965.d012266 k sizes θ) :=
  _root_.GD.N0232.N0719.N0932.d009220 k sizes θ.location θ.scale

theorem d012269 (k : ℕ) (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    Integrable (_root_.GD.N0232.N0719.N0965.d012266 k sizes θ) (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  _root_.GD.N0232.N0719.N0828.d010987 k sizes θ.location θ.scale θ.scale_pos

theorem d012270 (k : ℕ) (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (∫ ω, _root_.GD.N0232.N0719.N0965.d012266 k sizes θ ω ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) = 1 :=
  _root_.GD.N0232.N0719.N0828.d010988 k sizes θ.location θ.scale θ.scale_pos

theorem d012271 (k : ℕ) (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010812 k sizes θ = (_root_.GD.N0232.N0719.N0859.d010813 k sizes).withDensity
      (fun ω ↦ ENNReal.ofReal (_root_.GD.N0232.N0719.N0965.d012266 k sizes θ ω)) :=
  _root_.GD.N0232.N0719.N0932.d009223 k sizes θ.location θ.scale θ.scale_pos

theorem d012272
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p ≠ ⊤) :
    Integrable (fun ω ↦ (p ω - θ.location) ^ 2) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  have hm := _root_.GD.N0230.N0602.d000119
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ) θ.location p
  have hi := integrable_toReal_of_lintegral_ne_top hm hp
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hi


def d012273
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (i : ι) (omega : _root_.GD.N0232.N0719.d009173 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0965.d012266 k sizes (packet i) omega


def d012274 (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (i : ι) : ℝ :=
  (packet i).location


def d012275
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ) :
    _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  _root_.GD.N0230.N0617.d000163 weight (_root_.GD.N0232.N0719.N0965.d012273 packet)


def d012276
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ) :
    _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  _root_.GD.N0230.N0617.d000166 weight (_root_.GD.N0232.N0719.N0965.d012273 packet) (_root_.GD.N0232.N0719.N0965.d012274 packet)


def d012277
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ) :
    _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0719.N0965.d012273 packet) (_root_.GD.N0232.N0719.N0965.d012274 packet)



def d012278 (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) : ℝ :=
  Real.sqrt (∑ i, (packet i).location ^ 2)

theorem d012279
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (i : ι) (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    0 ≤ _root_.GD.N0232.N0719.N0965.d012273 packet i omega :=
  _root_.GD.N0232.N0719.N0965.d012267 k sizes (packet i) omega

theorem d012280
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (i : ι) :
    Measurable (_root_.GD.N0232.N0719.N0965.d012273 (k := k) (sizes := sizes) packet i) :=
  _root_.GD.N0232.N0719.N0965.d012268 k sizes (packet i)

theorem d012281
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (i : ι) :
    Integrable (_root_.GD.N0232.N0719.N0965.d012273 packet i) (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  _root_.GD.N0232.N0719.N0965.d012269 k sizes (packet i)

theorem d012282
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (i : ι) :
    (∫ omega, _root_.GD.N0232.N0719.N0965.d012273 packet i omega ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) = 1 :=
  _root_.GD.N0232.N0719.N0965.d012270 k sizes (packet i)

theorem d012283
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0965.d012276
      (k := k) (sizes := sizes) packet weight) := by
  exact _root_.GD.N0230.N0617.d000179
    weight (_root_.GD.N0232.N0719.N0965.d012273 packet) (_root_.GD.N0232.N0719.N0965.d012274 packet)
      (_root_.GD.N0232.N0719.N0965.d012280 packet)

theorem d012284
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    |_root_.GD.N0232.N0719.N0965.d012276 packet weight omega| ≤
      _root_.GD.N0232.N0719.N0965.d012278 packet := by
  exact _root_.GD.N0230.N0617.d000176
    weight (_root_.GD.N0232.N0719.N0965.d012273 packet) (_root_.GD.N0232.N0719.N0965.d012274 packet)
      hweight (_root_.GD.N0232.N0719.N0965.d012279 packet) omega

theorem d012285
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    MemLp (_root_.GD.N0232.N0719.N0965.d012276 packet weight) 2
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  exact _root_.GD.N0230.N0617.d000181
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes) weight (_root_.GD.N0232.N0719.N0965.d012273 packet) (_root_.GD.N0232.N0719.N0965.d012274 packet)
      hweight (_root_.GD.N0232.N0719.N0965.d012279 packet)
      (_root_.GD.N0232.N0719.N0965.d012280 packet)



def d012286
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  MemLp.toLp (_root_.GD.N0232.N0719.N0965.d012276 packet weight)
    (_root_.GD.N0232.N0719.N0965.d012285 packet weight hweight)

theorem d012287
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    (fun omega ↦ _root_.GD.N0232.N0719.N0965.d012286 packet weight hweight omega) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] _root_.GD.N0232.N0719.N0965.d012276 packet weight :=
  (_root_.GD.N0232.N0719.N0965.d012285 packet weight hweight).coeFn_toLp



theorem d012288
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0719.N0896.d011103 k sizes
      (_root_.GD.N0232.N0719.N0965.d012286 packet weight hweight) := by
  intro theta
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
    unfold _root_.GD.N0232.N0719.N0859.d010812
    infer_instance
  let B := _root_.GD.N0232.N0719.N0965.d012278 packet
  have herror : MemLp
      (fun omega ↦ _root_.GD.N0232.N0719.N0965.d012276 packet weight omega -
        theta.location) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
    apply memLp_of_bounded
        (a := -B - theta.location) (b := B - theta.location)
    · filter_upwards [] with omega
      have hbound := abs_le.mp
        (_root_.GD.N0232.N0719.N0965.d012284 packet weight hweight omega)
      constructor <;> linarith
    · exact (_root_.GD.N0232.N0719.N0965.d012283 packet weight).sub
        measurable_const |>.aestronglyMeasurable
  have heq :
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N0965.d012286 packet weight hweight) =
        ENNReal.ofReal
          (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
            (fun omega ↦ _root_.GD.N0232.N0719.N0965.d012276 packet weight omega -
              theta.location)) := by
    unfold _root_.GD.N0232.N0719.N0965.d012286
    exact _root_.GD.N0232.N0719.N0859.d010822 k sizes
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta) theta.location
      (_root_.GD.N0232.N0719.N0965.d012276 packet weight)
      (_root_.GD.N0232.N0719.N0965.d012285 packet weight hweight) herror
  rw [heq]
  exact ENNReal.ofReal_ne_top



theorem d012289
    (theta : (_root_.GD.N0232.N0719.N0859.d010809 k)) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hfinite : _root_.GD.N0232.N0719.N0859.d010821 k sizes theta q ≠ ⊤) :
    Integrable (fun omega ↦
      _root_.GD.N0232.N0719.N0965.d012266 k sizes theta omega *
        (q omega - theta.location) ^ 2) (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  let mu := _root_.GD.N0232.N0719.N0859.d010813 k sizes
  let rho : _root_.GD.N0232.N0719.d009173 k sizes → ℝ≥0∞ := fun omega ↦
    ENNReal.ofReal (_root_.GD.N0232.N0719.N0965.d012266 k sizes theta omega)
  have hrisk := _root_.GD.N0232.N0719.N0965.d012272 theta q hfinite
  have hrhoMeas : Measurable rho :=
    (_root_.GD.N0232.N0719.N0965.d012268 k sizes theta).ennreal_ofReal
  have hrhoFinite : ∀ᵐ omega ∂mu, rho omega < ∞ := by
    filter_upwards with omega
    exact ENNReal.ofReal_lt_top
  have hphysical : Integrable
      (fun omega ↦ (q omega - theta.location) ^ 2)
      (mu.withDensity rho) := by
    rw [← _root_.GD.N0232.N0719.N0965.d012271 k sizes theta]
    exact hrisk
  have hweighted : Integrable
      (fun omega ↦ (q omega - theta.location) ^ 2 * (rho omega).toReal)
      mu :=
    (integrable_withDensity_iff (μ := mu) hrhoMeas hrhoFinite).1 hphysical
  refine hweighted.congr ?_
  filter_upwards with omega
  rw [ENNReal.toReal_ofReal
    (_root_.GD.N0232.N0719.N0965.d012267 k sizes theta omega)]
  ring



theorem d012290
    (theta : (_root_.GD.N0232.N0719.N0859.d010809 k)) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hfinite : _root_.GD.N0232.N0719.N0859.d010821 k sizes theta q ≠ ⊤) :
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal =
      ∫ omega, _root_.GD.N0232.N0719.N0965.d012266 k sizes theta omega *
        (q omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
  have herrorInt := _root_.GD.N0232.N0719.N0965.d012272 theta q hfinite
  have hriskReal :
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal =
        ∫ omega, (q omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta := by
    unfold _root_.GD.N0232.N0719.N0859.d010821 _root_.GD.N0230.N0602.d000117
    rw [← ofReal_integral_eq_lintegral_ofReal herrorInt
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
    rw [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _)]
  calc
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal =
        ∫ omega, (q omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta :=
      hriskReal
    _ = ∫ omega, _root_.GD.N0232.N0719.N0965.d012266 k sizes theta omega *
          (q omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
      simpa [_root_.GD.N0230.N0591.d000133] using
        (_root_.GD.N0230.N0591.d000135
          (_root_.GD.N0232.N0719.N0965.d012266 k sizes theta)
          (fun omega ↦ (q omega - theta.location) ^ 2)
          (_root_.GD.N0232.N0719.N0965.d012271 k sizes theta)
          (_root_.GD.N0232.N0719.N0965.d012268 k sizes theta)
          (_root_.GD.N0232.N0719.N0965.d012267 k sizes theta))


def d012291
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) : ℝ :=
  ‖q‖ ^ 2 +
    ∑ i, weight i * (_root_.GD.N0232.N0719.N0859.d010821 k sizes (packet i) q).toReal


def d012292
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ) : ℝ :=
  (∑ i, weight i * (packet i).location ^ 2) -
    ∫ omega, _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0719.N0965.d012273 packet)
      (_root_.GD.N0232.N0719.N0965.d012274 packet) omega ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes



theorem d012293
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0719.N0965.d012292 (k := k) (sizes := sizes) packet weight =
      ∫ omega,
        _root_.GD.N0230.N0617.d000165 weight (_root_.GD.N0232.N0719.N0965.d012273 packet)
            (_root_.GD.N0232.N0719.N0965.d012274 packet) omega -
          _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0719.N0965.d012273 packet)
            (_root_.GD.N0232.N0719.N0965.d012274 packet) omega
        ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
  have hsecond := _root_.GD.N0230.N0617.d000182
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes) weight (_root_.GD.N0232.N0719.N0965.d012273 packet)
      (_root_.GD.N0232.N0719.N0965.d012274 packet) (_root_.GD.N0232.N0719.N0965.d012281 packet)
  have hcorrection := _root_.GD.N0230.N0617.d000183
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes) weight (_root_.GD.N0232.N0719.N0965.d012273 packet)
      (_root_.GD.N0232.N0719.N0965.d012274 packet) hweight (_root_.GD.N0232.N0719.N0965.d012279 packet)
      (_root_.GD.N0232.N0719.N0965.d012280 packet)
      (_root_.GD.N0232.N0719.N0965.d012281 packet)
  have hsecondIntegral :
      (∫ omega, _root_.GD.N0230.N0617.d000165 weight (_root_.GD.N0232.N0719.N0965.d012273 packet)
          (_root_.GD.N0232.N0719.N0965.d012274 packet) omega ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) =
        ∑ i, weight i * (packet i).location ^ 2 := by
    unfold _root_.GD.N0230.N0617.d000165
    rw [integral_finsetSum Finset.univ (fun i _ ↦ by
      convert (_root_.GD.N0232.N0719.N0965.d012281 (k := k) (sizes := sizes) packet i).const_mul
        (weight i * _root_.GD.N0232.N0719.N0965.d012274 packet i ^ 2) using 1
      funext omega
      ring)]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∫ omega, weight i * _root_.GD.N0232.N0719.N0965.d012273 packet i omega *
          _root_.GD.N0232.N0719.N0965.d012274 packet i ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) =
          weight i * _root_.GD.N0232.N0719.N0965.d012274 packet i ^ 2 *
            ∫ omega, _root_.GD.N0232.N0719.N0965.d012273 packet i omega ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with omega
        ring
      _ = weight i * (packet i).location ^ 2 := by
        rw [_root_.GD.N0232.N0719.N0965.d012282]
        simp [_root_.GD.N0232.N0719.N0965.d012274]
  unfold _root_.GD.N0232.N0719.N0965.d012292
  rw [integral_sub hsecond hcorrection, hsecondIntegral]


theorem d012294
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    ‖q‖ ^ 2 = ∫ omega, (q omega) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
  rw [← real_inner_self_eq_norm_sq q, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with omega
  simp only [RCLike.inner_apply, conj_trivial, pow_two]




theorem d012295
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hqFinite : ∀ i, _root_.GD.N0232.N0719.N0859.d010821 k sizes (packet i) q ≠ ⊤) :
    _root_.GD.N0232.N0719.N0965.d012291 (k := k) (sizes := sizes) packet weight q =
      (∫ omega, _root_.GD.N0232.N0719.N0965.d012275 packet weight omega *
          (q omega - _root_.GD.N0232.N0719.N0965.d012276 packet weight omega) ^ 2
            ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) +
        _root_.GD.N0232.N0719.N0965.d012292 (k := k) (sizes := sizes) packet weight := by
  have hexact := _root_.GD.N0230.N0617.d000187
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes) weight (_root_.GD.N0232.N0719.N0965.d012273 packet)
      (_root_.GD.N0232.N0719.N0965.d012274 packet) (fun omega ↦ q omega)
      hweight (_root_.GD.N0232.N0719.N0965.d012279 packet)
      (_root_.GD.N0232.N0719.N0965.d012280 packet)
      (_root_.GD.N0232.N0719.N0965.d012281 packet)
      (Lp.memLp q).integrable_sq
      (fun i ↦ _root_.GD.N0232.N0719.N0965.d012289
        (packet i) q (hqFinite i))
  rw [← _root_.GD.N0232.N0719.N0965.d012294 q] at hexact
  have hriskEq (i : ι) :
      (∫ omega, _root_.GD.N0232.N0719.N0965.d012273 packet i omega *
          (q omega - _root_.GD.N0232.N0719.N0965.d012274 packet i) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) =
        (_root_.GD.N0232.N0719.N0859.d010821 k sizes (packet i) q).toReal :=
    (_root_.GD.N0232.N0719.N0965.d012290
      (packet i) q (hqFinite i)).symm
  simp_rw [hriskEq] at hexact
  simp_rw [_root_.GD.N0232.N0719.N0965.d012282] at hexact
  simp only [_root_.GD.N0232.N0719.N0965.d012291, _root_.GD.N0232.N0719.N0965.d012292,
    _root_.GD.N0232.N0719.N0965.d012275, _root_.GD.N0232.N0719.N0965.d012276, _root_.GD.N0232.N0719.N0965.d012274,
    mul_one] at hexact ⊢
  linarith


theorem d012296
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    (∫ omega, _root_.GD.N0232.N0719.N0965.d012275 packet weight omega *
        (_root_.GD.N0232.N0719.N0965.d012286 packet weight hweight omega -
          _root_.GD.N0232.N0719.N0965.d012276 packet weight omega) ^ 2
          ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) = 0 := by
  calc
    (∫ omega, _root_.GD.N0232.N0719.N0965.d012275 packet weight omega *
        (_root_.GD.N0232.N0719.N0965.d012286 packet weight hweight omega -
          _root_.GD.N0232.N0719.N0965.d012276 packet weight omega) ^ 2
          ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) =
        ∫ _omega, (0 : ℝ) ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0232.N0719.N0965.d012287
          packet weight hweight] with omega hcompletion
      simp only [hcompletion, sub_self, pow_two, mul_zero]
    _ = 0 := by simp


theorem d012297
    (packet : ι → (_root_.GD.N0232.N0719.N0859.d010809 k)) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0719.N0965.d012291 (k := k) (sizes := sizes) packet weight
        (_root_.GD.N0232.N0719.N0965.d012286 (k := k) (sizes := sizes)
          packet weight hweight) =
      _root_.GD.N0232.N0719.N0965.d012292 (k := k) (sizes := sizes) packet weight := by
  rw [_root_.GD.N0232.N0719.N0965.d012295
      (k := k) (sizes := sizes) packet weight hweight
      (_root_.GD.N0232.N0719.N0965.d012286 (k := k) (sizes := sizes)
        packet weight hweight)
      (fun i ↦ _root_.GD.N0232.N0719.N0965.d012288
        (k := k) (sizes := sizes) packet weight hweight (packet i)),
    _root_.GD.N0232.N0719.N0965.d012296
      (k := k) (sizes := sizes),
    zero_add]


end
end N0965
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0965.d012288
#print axioms _root_.GD.N0232.N0719.N0965.d012293
#print axioms _root_.GD.N0232.N0719.N0965.d012295
#print axioms _root_.GD.N0232.N0719.N0965.d012297
