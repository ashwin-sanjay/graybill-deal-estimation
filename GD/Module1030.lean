import GD.Module0019
import GD.Module1028
import GD.Module0932
import GD.Module0961




















open Filter MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1126

noncomputable section

open _root_.GD.N0230.N0591
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

private noncomputable local instance d016412 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance


def d016413
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (i : ι) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1499.d015001 m n (packet i) omega


def d016414 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (i : ι) : ℝ :=
  (packet i).location


def d016415
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  _root_.GD.N0230.N0617.d000163 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)


def d016416
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  _root_.GD.N0230.N0617.d000166 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)


def d016417
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)



def d016418 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  Real.sqrt (∑ i, (packet i).location ^ 2)

theorem d016419
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (i : ι) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1126.d016413 packet i omega :=
  _root_.GD.N0232.N0720.N1499.d015003 m n (packet i) omega

theorem d016420
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (i : ι) :
    Measurable (_root_.GD.N0232.N0720.N1126.d016413 (m := m) (n := n) packet i) :=
  _root_.GD.N0232.N0720.N1499.d015002 m n (packet i)

theorem d016421
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (i : ι) :
    Integrable (_root_.GD.N0232.N0720.N1126.d016413 packet i) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1484.d015103 m n (packet i)

theorem d016422
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (i : ι) :
    (∫ omega, _root_.GD.N0232.N0720.N1126.d016413 packet i omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 1 :=
  _root_.GD.N0232.N0720.N1484.d015104 m n (packet i)

theorem d016423
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1126.d016416
      (m := m) (n := n) packet weight) := by
  exact _root_.GD.N0230.N0617.d000179
    weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
      (_root_.GD.N0232.N0720.N1126.d016420 packet)

theorem d016424
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    |_root_.GD.N0232.N0720.N1126.d016416 packet weight omega| ≤
      _root_.GD.N0232.N0720.N1126.d016418 packet := by
  exact _root_.GD.N0230.N0617.d000176
    weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
      hweight (_root_.GD.N0232.N0720.N1126.d016419 packet) omega

theorem d016425
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    MemLp (_root_.GD.N0232.N0720.N1126.d016416 packet weight) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  exact _root_.GD.N0230.N0617.d000181
    (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
      hweight (_root_.GD.N0232.N0720.N1126.d016419 packet)
      (_root_.GD.N0232.N0720.N1126.d016420 packet)



def d016426
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1126.d016416 packet weight)
    (_root_.GD.N0232.N0720.N1126.d016425 packet weight hweight)

theorem d016427
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    (fun omega ↦ _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight omega) =ᵐ[
      _root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1126.d016416 packet weight :=
  (_root_.GD.N0232.N0720.N1126.d016425 packet weight hweight).coeFn_toLp



theorem d016428
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight) := by
  intro theta
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    unfold _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  let B := _root_.GD.N0232.N0720.N1126.d016418 packet
  have herror : MemLp
      (fun omega ↦ _root_.GD.N0232.N0720.N1126.d016416 packet weight omega -
        theta.location) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    apply memLp_of_bounded
        (a := -B - theta.location) (b := B - theta.location)
    · filter_upwards [] with omega
      have hbound := abs_le.mp
        (_root_.GD.N0232.N0720.N1126.d016424 packet weight hweight omega)
      constructor <;> linarith
    · exact (_root_.GD.N0232.N0720.N1126.d016423 packet weight).sub
        measurable_const |>.aestronglyMeasurable
  have heq :
      _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight) =
        ENNReal.ofReal
          (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
            (fun omega ↦ _root_.GD.N0232.N0720.N1126.d016416 packet weight omega -
              theta.location)) := by
    unfold _root_.GD.N0232.N0720.N1126.d016426
    exact _root_.GD.N0232.N0720.N1080.d014183 m n
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta) theta.location
      (_root_.GD.N0232.N0720.N1126.d016416 packet weight)
      (_root_.GD.N0232.N0720.N1126.d016425 packet weight hweight) herror
  rw [heq]
  exact ENNReal.ofReal_ne_top



theorem d016429
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta q ≠ ⊤) :
    Integrable (fun omega ↦
      _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
        (q omega - theta.location) ^ 2) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  let mu := _root_.GD.N0232.N0720.N1080.d014172 m n
  let rho : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ≥0∞ := fun omega ↦
    ENNReal.ofReal (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega)
  have hrisk := _root_.GD.N0232.N0720.N1078.d016376 m n theta q hfinite
  have hrhoMeas : Measurable rho :=
    (_root_.GD.N0232.N0720.N1499.d015002 m n theta).ennreal_ofReal
  have hrhoFinite : ∀ᵐ omega ∂mu, rho omega < ∞ := by
    filter_upwards with omega
    exact ENNReal.ofReal_lt_top
  have hphysical : Integrable
      (fun omega ↦ (q omega - theta.location) ^ 2)
      (mu.withDensity rho) := by
    rw [← _root_.GD.N0232.N0720.N1499.d015006 m n theta]
    exact hrisk
  have hweighted : Integrable
      (fun omega ↦ (q omega - theta.location) ^ 2 * (rho omega).toReal)
      mu :=
    (integrable_withDensity_iff (μ := mu) hrhoMeas hrhoFinite).1 hphysical
  refine hweighted.congr ?_
  filter_upwards with omega
  rw [ENNReal.toReal_ofReal
    (_root_.GD.N0232.N0720.N1499.d015003 m n theta omega)]
  ring



theorem d016430
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta q ≠ ⊤) :
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta q).toReal =
      ∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
        (q omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  have herrorInt := _root_.GD.N0232.N0720.N1078.d016376 m n theta q hfinite
  have hriskReal :
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta q).toReal =
        ∫ omega, (q omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
    unfold _root_.GD.N0232.N0720.N1080.d014182 _root_.GD.N0230.N0602.d000117
    rw [← ofReal_integral_eq_lintegral_ofReal herrorInt
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
    rw [ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _)]
  calc
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta q).toReal =
        ∫ omega, (q omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta :=
      hriskReal
    _ = ∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
          (q omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
      simpa [_root_.GD.N0230.N0591.d000133] using
        (_root_.GD.N0230.N0591.d000135
          (_root_.GD.N0232.N0720.N1499.d015001 m n theta)
          (fun omega ↦ (q omega - theta.location) ^ 2)
          (_root_.GD.N0232.N0720.N1499.d015006 m n theta)
          (_root_.GD.N0232.N0720.N1499.d015002 m n theta)
          (_root_.GD.N0232.N0720.N1499.d015003 m n theta))


def d016431
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (i : ι) : ℝ :=
  (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal



def d016432
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) : ℝ :=
  _root_.GD.N0230.N0617.d000186 (_root_.GD.N0232.N0720.N1080.d014172 m n) weight
    (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) (_root_.GD.N0232.N0720.N1126.d016431 s packet)

private theorem d016433
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖q‖ ^ 2 = ∫ omega, (q omega) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  rw [← real_inner_self_eq_norm_sq q, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with omega
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

private theorem d016434
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 =
      ∫ omega, (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  rw [← real_inner_self_eq_norm_sq
    (q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub q
      (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight),
    _root_.GD.N0232.N0720.N1126.d016427 packet weight hweight] with
      omega hsub hcompletion
  rw [hsub, Pi.sub_apply, hcompletion]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]





theorem d016435
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    ‖q‖ ^ 2 -
        (_root_.GD.N0232.N0720.N1126.d016432 s packet weight +
          ∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
            (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
              ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ∑ i, weight i *
        ((_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal) := by
  have hqFinite : _root_.GD.N0232.N0720.N1159.d014637 m n q :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s q hq
  have hexact :=
    _root_.GD.N0230.N0617.d000188
      (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
        (_root_.GD.N0232.N0720.N1126.d016414 packet) (_root_.GD.N0232.N0720.N1126.d016431 s packet)
        (fun omega ↦ q omega) hweight (_root_.GD.N0232.N0720.N1126.d016419 packet)
        (_root_.GD.N0232.N0720.N1126.d016420 packet)
        (_root_.GD.N0232.N0720.N1126.d016421 packet)
        (_root_.GD.N0232.N0720.N1126.d016422 packet)
        (Lp.memLp q).integrable_sq
        (fun i ↦ _root_.GD.N0232.N0720.N1126.d016429
          (packet i) q (hqFinite (packet i)))
  rw [← _root_.GD.N0232.N0720.N1126.d016433 q] at hexact
  have hriskEq (i : ι) :
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016413 packet i omega *
          (q omega - _root_.GD.N0232.N0720.N1126.d016414 packet i) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
        (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal := by
    exact (_root_.GD.N0232.N0720.N1126.d016430
      (packet i) q (hqFinite (packet i))).symm
  simp_rw [hriskEq] at hexact
  simpa only [_root_.GD.N0232.N0720.N1126.d016432, _root_.GD.N0232.N0720.N1126.d016415,
    _root_.GD.N0232.N0720.N1126.d016416, _root_.GD.N0232.N0720.N1126.d016431] using hexact



theorem d016436
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    _root_.GD.N0232.N0720.N1126.d016432 s packet weight +
        ‖q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 ≤
      ‖q‖ ^ 2 := by
  have hqFinite : _root_.GD.N0232.N0720.N1159.d014637 m n q :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s q hq
  have hriskCap : ∀ i,
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016413 packet i omega *
          (q omega - _root_.GD.N0232.N0720.N1126.d016414 packet i) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
        _root_.GD.N0232.N0720.N1126.d016431 s packet i := by
    intro i
    change (∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n (packet i) omega *
        (q omega - (packet i).location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
      (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) s.value).toReal
    rw [← _root_.GD.N0232.N0720.N1126.d016430
      (packet i) q (hqFinite (packet i))]
    exact ENNReal.toReal_mono (s.finiteRisk (packet i)) (hq (packet i))
  have hreserve := _root_.GD.N0230.N0617.d000190
    (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet) (_root_.GD.N0232.N0720.N1126.d016431 s packet)
      (fun omega ↦ q omega) hweight (_root_.GD.N0232.N0720.N1126.d016419 packet)
      (_root_.GD.N0232.N0720.N1126.d016420 packet)
      (_root_.GD.N0232.N0720.N1126.d016421 packet)
      (_root_.GD.N0232.N0720.N1126.d016422 packet)
      (Lp.aestronglyMeasurable q) (Lp.memLp q).integrable_sq
      (fun i ↦ _root_.GD.N0232.N0720.N1126.d016429
        (packet i) q (hqFinite (packet i))) hriskCap
  rw [← _root_.GD.N0232.N0720.N1126.d016433 q] at hreserve
  change _root_.GD.N0232.N0720.N1126.d016432 s packet weight +
      (∫ omega,
        (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤ ‖q‖ ^ 2 at hreserve
  rw [← _root_.GD.N0232.N0720.N1126.d016434
    packet weight hweight q] at hreserve
  exact hreserve



theorem d016437
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1126.d016432 s packet weight +
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value -
          _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  exact _root_.GD.N0232.N0720.N1126.d016436
    s packet weight hweight (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1

end

end N1126
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1126.d016428
#print axioms _root_.GD.N0232.N0720.N1126.d016429
#print axioms _root_.GD.N0232.N0720.N1126.d016430
#print axioms _root_.GD.N0232.N0720.N1126.d016435
#print axioms _root_.GD.N0232.N0720.N1126.d016436
#print axioms _root_.GD.N0232.N0720.N1126.d016437
