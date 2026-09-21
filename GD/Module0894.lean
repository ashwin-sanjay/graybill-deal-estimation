import GD.Module0619
import GD.Module0880
import GD.Module0893

























open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace GD
namespace N0232
namespace N0720
namespace N1218

noncomputable section

open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1092
open _root_.GD.N0232.N0720.N1155
open _root_.GD.N0232.N0720.N1157
open _root_.GD.N0232.N0720.N1438
open _root_.GD.N0232.N0720.N1442





def d013885
    (rho : Measure ℝ) (kernel : ℝ → ℝ) : ℝ :=
  (∫ z, z * kernel z ∂rho) / ∫ z, kernel z ∂rho



theorem d013886
    {rho : Measure ℝ} {kernel : ℝ → ℝ} {a b : ℝ}
    (hkernel : Integrable kernel rho)
    (hmoment : Integrable (fun z ↦ z * kernel z) rho)
    (hkernelNonneg : ∀ᵐ z ∂rho, 0 ≤ kernel z)
    (hsupport : ∀ᵐ z ∂rho, z ∈ Icc a b)
    (hevidence : 0 < ∫ z, kernel z ∂rho) :
    _root_.GD.N0232.N0720.N1218.d013885 rho kernel ∈ Icc a b := by
  have hlowerInt :
      a * (∫ z, kernel z ∂rho) ≤ ∫ z, z * kernel z ∂rho := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hkernel.const_mul a) hmoment
    filter_upwards [hkernelNonneg, hsupport] with z hk hz
    exact mul_le_mul_of_nonneg_right hz.1 hk
  have hupperInt :
      (∫ z, z * kernel z ∂rho) ≤ b * ∫ z, kernel z ∂rho := by
    rw [← integral_const_mul]
    apply integral_mono_ae hmoment (hkernel.const_mul b)
    filter_upwards [hkernelNonneg, hsupport] with z hk hz
    exact mul_le_mul_of_nonneg_right hz.2 hk
  unfold _root_.GD.N0232.N0720.N1218.d013885
  exact ⟨(le_div_iff₀ hevidence).2 hlowerInt,
    (div_le_iff₀ hevidence).2 hupperInt⟩

variable {ι : Type*} [Fintype ι] [Nonempty ι]


def d013887
    (mass fraction kernel : ι → ℝ) : ℝ :=
  (∑ i, mass i * kernel i * fraction i) /
    ∑ i, mass i * kernel i



theorem d013888
    {mass fraction kernel : ι → ℝ} {a b : ℝ}
    (hmass : ∀ i, 0 < mass i) (hkernel : ∀ i, 0 < kernel i)
    (hfraction : ∀ i, fraction i ∈ Icc a b) :
    _root_.GD.N0232.N0720.N1218.d013887 mass fraction kernel ∈ Icc a b := by
  let weight : ι → ℝ := fun i ↦ mass i * kernel i
  have hweight : ∀ i, 0 < weight i := fun i ↦ mul_pos (hmass i) (hkernel i)
  have htotal : 0 < ∑ i, weight i :=
    Finset.sum_pos (fun i _ ↦ hweight i) Finset.univ_nonempty
  have hlower : a * (∑ i, weight i) ≤
      ∑ i, weight i * fraction i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hfraction i).1 (hweight i).le
  have hupper : (∑ i, weight i * fraction i) ≤
      b * ∑ i, weight i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hfraction i).2 (hweight i).le
  unfold _root_.GD.N0232.N0720.N1218.d013887
  change
    (∑ i, weight i * fraction i) / ∑ i, weight i ∈ Icc a b
  exact ⟨(le_div_iff₀ htotal).2 hlower, (div_le_iff₀ htotal).2 hupper⟩






def d013889
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (contrast coefficient : Ω → ℝ) (z : ℝ) : ℝ :=
  ∫ omega, contrast omega ^ 2 * (coefficient omega - z) ^ 2 ∂P



theorem d013890
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {contrast coefficient : Ω → ℝ} {a z : ℝ}
    (hcontrast : Integrable (fun omega ↦ contrast omega ^ 2) P)
    (hexcess : Integrable
      (fun omega ↦ contrast omega ^ 2 * (coefficient omega - z) ^ 2) P)
    (hsecond : (∫ omega, contrast omega ^ 2 ∂P) = 1)
    (hcoefficient : ∀ᵐ omega ∂P, a ≤ coefficient omega)
    (hz : z ≤ a) :
    (a - z) ^ 2 ≤ _root_.GD.N0232.N0720.N1218.d013889 P contrast coefficient z := by
  have hmono :
      (∫ omega, (a - z) ^ 2 * contrast omega ^ 2 ∂P) ≤
        ∫ omega, contrast omega ^ 2 * (coefficient omega - z) ^ 2 ∂P := by
    apply integral_mono_ae (hcontrast.const_mul ((a - z) ^ 2)) hexcess
    filter_upwards [hcoefficient] with omega homega
    have hsquare : (a - z) ^ 2 ≤ (coefficient omega - z) ^ 2 := by
      nlinarith [sq_nonneg (coefficient omega - a)]
    nlinarith [sq_nonneg (contrast omega)]
  rw [integral_const_mul, hsecond, mul_one] at hmono
  exact hmono



theorem d013891
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {contrast coefficient : Ω → ℝ} {b z : ℝ}
    (hcontrast : Integrable (fun omega ↦ contrast omega ^ 2) P)
    (hexcess : Integrable
      (fun omega ↦ contrast omega ^ 2 * (coefficient omega - z) ^ 2) P)
    (hsecond : (∫ omega, contrast omega ^ 2 ∂P) = 1)
    (hcoefficient : ∀ᵐ omega ∂P, coefficient omega ≤ b)
    (hz : b ≤ z) :
    (z - b) ^ 2 ≤ _root_.GD.N0232.N0720.N1218.d013889 P contrast coefficient z := by
  have hmono :
      (∫ omega, (z - b) ^ 2 * contrast omega ^ 2 ∂P) ≤
        ∫ omega, contrast omega ^ 2 * (coefficient omega - z) ^ 2 ∂P := by
    apply integral_mono_ae (hcontrast.const_mul ((z - b) ^ 2)) hexcess
    filter_upwards [hcoefficient] with omega homega
    have hsquare : (z - b) ^ 2 ≤ (coefficient omega - z) ^ 2 := by
      nlinarith [sq_nonneg (b - coefficient omega)]
    nlinarith [sq_nonneg (contrast omega)]
  rw [integral_const_mul, hsecond, mul_one] at hmono
  exact hmono


def d013892
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (contrast coefficient : Ω → ℝ) (z : ℝ) : ℝ :=
  z * (1 - z) + _root_.GD.N0232.N0720.N1218.d013889 P contrast coefficient z





theorem d013893
    {alpha beta u : ℝ} (hbeta : beta ≠ 0) (hu : u ≠ 0)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0)) :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (p n)) u)
      atTop (nhds 0) := by
  have honeSub : Tendsto (fun n ↦ 1 - p n) atTop (nhds 1) := by
    convert tendsto_const_nhds.sub hp using 1
    ring_nf
  have hodds : Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1091.d012762 alpha beta (p n))
      atTop (nhds 0) := by
    unfold _root_.GD.N0232.N0720.N1091.d012762
    have hnum : Tendsto (fun n ↦ alpha * p n) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hp
    have hden : Tendsto (fun n ↦ beta * (1 - p n))
        atTop (nhds beta) := by
      simpa using tendsto_const_nhds.mul honeSub
    have hquot := hnum.div hden hbeta
    have hfun :
        (fun n ↦ alpha * p n) / (fun n ↦ beta * (1 - p n)) =
          (fun n ↦ alpha * p n / (beta * (1 - p n))) := by
      funext n
      rfl
    rw [hfun] at hquot
    simpa only [zero_div] using hquot
  unfold _root_.GD.N0232.N0720.N1091.d012763
  have hnum : Tendsto
      (fun n ↦ _root_.GD.N0232.N0720.N1091.d012762 alpha beta (p n) * (1 - u))
      atTop (nhds 0) := by
    simpa using hodds.mul_const (1 - u)
  have hden : Tendsto
      (fun n ↦ u + _root_.GD.N0232.N0720.N1091.d012762 alpha beta (p n) * (1 - u))
      atTop (nhds u) := by
    simpa using tendsto_const_nhds.add (hodds.mul_const (1 - u))
  have hquot := hnum.div hden hu
  have hfun :
      (fun n ↦ _root_.GD.N0232.N0720.N1091.d012762 alpha beta (p n) * (1 - u)) /
          (fun n ↦ u + _root_.GD.N0232.N0720.N1091.d012762 alpha beta (p n) * (1 - u)) =
        (fun n ↦ _root_.GD.N0232.N0720.N1091.d012762 alpha beta (p n) * (1 - u) /
          (u + _root_.GD.N0232.N0720.N1091.d012762 alpha beta (p n) * (1 - u))) := by
    funext n
    rfl
  rw [hfun] at hquot
  simpa only [zero_div] using hquot




theorem d013894
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p n))
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure (betaMeasure alpha beta) :=
    isProbabilityMeasureBeta halpha hbeta
  have hsupport := _root_.GD.N0232.N0720.N1092.d013031 alpha beta
  unfold _root_.GD.N0232.N0720.N1091.d012790
  have htendsto : Tendsto
      (fun n ↦ ∫ u,
        (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (p n)) u - p n) ^ 2
          ∂betaMeasure alpha beta)
      atTop (nhds (∫ _u : ℝ, (0 : ℝ) ∂betaMeasure alpha beta)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _u : ℝ ↦ (1 : ℝ))
    · exact Filter.Eventually.of_forall fun n ↦
        (((_root_.GD.N0232.N0720.N1091.d012771 _).sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · filter_upwards with n
      filter_upwards [hsupport] with u hu
      have hlambda := _root_.GD.N0232.N0720.N1091.d012778 halpha hbeta (hp0 n) (hp1 n)
      have hw := _root_.GD.N0232.N0720.N1091.d012780 hlambda hu.1 hu.2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have habs :
          |_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (p n)) u - p n| < 1 := by
        rw [abs_lt]
        constructor <;> linarith [hw.1, hw.2, hp0 n, hp1 n]
      have hsquare :
          |_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (p n)) u - p n| ^ 2 <
            (1 : ℝ) ^ 2 := (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).2 habs
      simpa [sq_abs] using hsquare.le
    · exact integrable_const 1
    · filter_upwards [hsupport] with u hu
      have hpoint := ((_root_.GD.N0232.N0720.N1218.d013893
        (alpha := alpha) hbeta.ne' hu.1.ne' hp).sub hp).pow 2
      simpa using hpoint
  simpa using htendsto


theorem d013895
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 1))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p n))
      atTop (nhds 0) := by
  let q : ℕ → ℝ := fun n ↦ 1 - p n
  have hq : Tendsto q atTop (nhds 0) := by
    convert tendsto_const_nhds.sub hp using 1
    ring_nf
  have hq0 : ∀ n, 0 < q n := fun n ↦ sub_pos.mpr (hp1 n)
  have hq1 : ∀ n, q n < 1 := fun n ↦ by dsimp [q]; linarith [hp0 n]
  have hleft := _root_.GD.N0232.N0720.N1218.d013894 hbeta halpha hq hq0 hq1
  apply hleft.congr'
  exact Filter.Eventually.of_forall fun n ↦
    (_root_.GD.N0232.N0720.N1438.d013603 halpha hbeta (hp0 n) (hp1 n)).symm





theorem d013896
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {contrast : Ω → ℝ} {coefficient : ℕ → Ω → ℝ}
    {alpha beta a : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (ha : 0 < a) {p : ℕ → ℝ}
    (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1)
    (hcontrast : Integrable (fun omega ↦ contrast omega ^ 2) P)
    (hsecond : (∫ omega, contrast omega ^ 2 ∂P) = 1)
    (hcoefficient : ∀ n, ∀ᵐ omega ∂P, a ≤ coefficient n omega)
    (hexcess : ∀ n, Integrable (fun omega ↦
      contrast omega ^ 2 * (coefficient n omega - p n) ^ 2) P) :
    ∀ᶠ n in atTop,
      _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p n) <
        _root_.GD.N0232.N0720.N1218.d013889 P contrast (coefficient n) (p n) := by
  have hregret := _root_.GD.N0232.N0720.N1218.d013894 halpha hbeta hp hp0 hp1
  have hfloor : Tendsto (fun n ↦ (a - p n) ^ 2) atTop (nhds (a ^ 2)) := by
    convert (tendsto_const_nhds.sub hp).pow 2 using 1
    ring_nf
  have hregretSmall := hregret.eventually_lt_const
    (by nlinarith [sq_pos_of_pos ha] : 0 < a ^ 2 / 2)
  have hfloorLarge := hfloor.eventually_const_lt
    (by nlinarith [sq_pos_of_pos ha] : a ^ 2 / 2 < a ^ 2)
  have hpBelow : ∀ᶠ n in atTop, p n ≤ a := by
    have h := hp.eventually_lt_const ha
    exact h.mono fun n hn ↦ hn.le
  filter_upwards [hregretSmall, hfloorLarge, hpBelow] with n hr hf hpa
  have henergy := _root_.GD.N0232.N0720.N1218.d013890
    hcontrast (hexcess n) hsecond (hcoefficient n) hpa
  exact lt_of_lt_of_le (by linarith) henergy


theorem d013897
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {contrast : Ω → ℝ} {coefficient : ℕ → Ω → ℝ}
    {alpha beta b : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hb : b < 1) {p : ℕ → ℝ}
    (hp : Tendsto p atTop (nhds 1))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1)
    (hcontrast : Integrable (fun omega ↦ contrast omega ^ 2) P)
    (hsecond : (∫ omega, contrast omega ^ 2 ∂P) = 1)
    (hcoefficient : ∀ n, ∀ᵐ omega ∂P, coefficient n omega ≤ b)
    (hexcess : ∀ n, Integrable (fun omega ↦
      contrast omega ^ 2 * (coefficient n omega - p n) ^ 2) P) :
    ∀ᶠ n in atTop,
      _root_.GD.N0232.N0720.N1091.d012790 alpha beta (p n) <
        _root_.GD.N0232.N0720.N1218.d013889 P contrast (coefficient n) (p n) := by
  have hregret := _root_.GD.N0232.N0720.N1218.d013895 halpha hbeta hp hp0 hp1
  have hfloor : Tendsto (fun n ↦ (p n - b) ^ 2) atTop (nhds ((1 - b) ^ 2)) := by
    convert (hp.sub tendsto_const_nhds).pow 2 using 1
  have hgap : 0 < 1 - b := sub_pos.mpr hb
  have hregretSmall := hregret.eventually_lt_const
    (by nlinarith [sq_pos_of_pos hgap] : 0 < (1 - b) ^ 2 / 2)
  have hfloorLarge := hfloor.eventually_const_lt
    (by nlinarith [sq_pos_of_pos hgap] : (1 - b) ^ 2 / 2 < (1 - b) ^ 2)
  have hpAbove : ∀ᶠ n in atTop, b ≤ p n := by
    have h := hp.eventually_const_lt hb
    exact h.mono fun n hn ↦ hn.le
  filter_upwards [hregretSmall, hfloorLarge, hpAbove] with n hr hf hbp
  have henergy := _root_.GD.N0232.N0720.N1218.d013891
    hcontrast (hexcess n) hsecond (hcoefficient n) hbp
  exact lt_of_lt_of_le (by linarith) henergy


theorem d013898
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {contrast : Ω → ℝ} {coefficient : ℕ → Ω → ℝ}
    {alpha beta a : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (ha : 0 < a) {p : ℕ → ℝ}
    (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1)
    (hcontrast : Integrable (fun omega ↦ contrast omega ^ 2) P)
    (hsecond : (∫ omega, contrast omega ^ 2 ∂P) = 1)
    (hcoefficient : ∀ n, ∀ᵐ omega ∂P, a ≤ coefficient n omega)
    (hexcess : ∀ n, Integrable (fun omega ↦
      contrast omega ^ 2 * (coefficient n omega - p n) ^ 2) P) :
    ∀ᶠ n in atTop,
      _root_.GD.N0232.N0720.N1442.d013867 alpha beta (p n) <
        _root_.GD.N0232.N0720.N1218.d013892 P contrast (coefficient n) (p n) := by
  filter_upwards [_root_.GD.N0232.N0720.N1218.d013896
    halpha hbeta ha hp hp0 hp1 hcontrast hsecond hcoefficient hexcess] with n hn
  unfold _root_.GD.N0232.N0720.N1442.d013867 _root_.GD.N0232.N0720.N1442.d013866 _root_.GD.N0232.N0720.N1218.d013892
  linarith


theorem d013899
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {contrast : Ω → ℝ} {coefficient : ℕ → Ω → ℝ}
    {alpha beta b : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hb : b < 1) {p : ℕ → ℝ}
    (hp : Tendsto p atTop (nhds 1))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1)
    (hcontrast : Integrable (fun omega ↦ contrast omega ^ 2) P)
    (hsecond : (∫ omega, contrast omega ^ 2 ∂P) = 1)
    (hcoefficient : ∀ n, ∀ᵐ omega ∂P, coefficient n omega ≤ b)
    (hexcess : ∀ n, Integrable (fun omega ↦
      contrast omega ^ 2 * (coefficient n omega - p n) ^ 2) P) :
    ∀ᶠ n in atTop,
      _root_.GD.N0232.N0720.N1442.d013867 alpha beta (p n) <
        _root_.GD.N0232.N0720.N1218.d013892 P contrast (coefficient n) (p n) := by
  filter_upwards [_root_.GD.N0232.N0720.N1218.d013897
    halpha hbeta hb hp hp0 hp1 hcontrast hsecond hcoefficient hexcess] with n hn
  unfold _root_.GD.N0232.N0720.N1442.d013867 _root_.GD.N0232.N0720.N1442.d013866 _root_.GD.N0232.N0720.N1218.d013892
  linarith








theorem d013900
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {contrast : Ω → ℝ}
    {mass fraction : ι → ℝ} {kernel : ℕ → Ω → ι → ℝ}
    {alpha beta a b : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (ha : 0 < a) (hmass : ∀ i, 0 < mass i)
    (hkernel : ∀ n omega i, 0 < kernel n omega i)
    (hfraction : ∀ i, fraction i ∈ Icc a b)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 0))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1)
    (hcontrast : Integrable (fun omega ↦ contrast omega ^ 2) P)
    (hsecond : (∫ omega, contrast omega ^ 2 ∂P) = 1)
    (hexcess : ∀ n, Integrable (fun omega ↦ contrast omega ^ 2 *
      (_root_.GD.N0232.N0720.N1218.d013887 mass fraction (kernel n omega) -
        p n) ^ 2) P) :
    ∀ᶠ n in atTop,
      _root_.GD.N0232.N0720.N1442.d013867 alpha beta (p n) <
        _root_.GD.N0232.N0720.N1218.d013892 P contrast
          (fun omega ↦ _root_.GD.N0232.N0720.N1218.d013887
            mass fraction (kernel n omega)) (p n) := by
  apply _root_.GD.N0232.N0720.N1218.d013898
    halpha hbeta ha hp hp0 hp1 hcontrast hsecond
  · intro n
    exact Filter.Eventually.of_forall fun omega ↦
      (_root_.GD.N0232.N0720.N1218.d013888 hmass
        (hkernel n omega) hfraction).1
  · exact hexcess



theorem d013901
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {contrast : Ω → ℝ}
    {mass fraction : ι → ℝ} {kernel : ℕ → Ω → ι → ℝ}
    {alpha beta a b : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hb : b < 1) (hmass : ∀ i, 0 < mass i)
    (hkernel : ∀ n omega i, 0 < kernel n omega i)
    (hfraction : ∀ i, fraction i ∈ Icc a b)
    {p : ℕ → ℝ} (hp : Tendsto p atTop (nhds 1))
    (hp0 : ∀ n, 0 < p n) (hp1 : ∀ n, p n < 1)
    (hcontrast : Integrable (fun omega ↦ contrast omega ^ 2) P)
    (hsecond : (∫ omega, contrast omega ^ 2 ∂P) = 1)
    (hexcess : ∀ n, Integrable (fun omega ↦ contrast omega ^ 2 *
      (_root_.GD.N0232.N0720.N1218.d013887 mass fraction (kernel n omega) -
        p n) ^ 2) P) :
    ∀ᶠ n in atTop,
      _root_.GD.N0232.N0720.N1442.d013867 alpha beta (p n) <
        _root_.GD.N0232.N0720.N1218.d013892 P contrast
          (fun omega ↦ _root_.GD.N0232.N0720.N1218.d013887
            mass fraction (kernel n omega)) (p n) := by
  apply _root_.GD.N0232.N0720.N1218.d013899
    halpha hbeta hb hp hp0 hp1 hcontrast hsecond
  · intro n
    exact Filter.Eventually.of_forall fun omega ↦
      (_root_.GD.N0232.N0720.N1218.d013888 hmass
        (hkernel n omega) hfraction).2
  · exact hexcess

end

end N1218
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1218.d013886
#print axioms _root_.GD.N0232.N0720.N1218.d013888
#print axioms _root_.GD.N0232.N0720.N1218.d013890
#print axioms _root_.GD.N0232.N0720.N1218.d013891
#print axioms _root_.GD.N0232.N0720.N1218.d013894
#print axioms _root_.GD.N0232.N0720.N1218.d013895
#print axioms _root_.GD.N0232.N0720.N1218.d013898
#print axioms _root_.GD.N0232.N0720.N1218.d013899
#print axioms _root_.GD.N0232.N0720.N1218.d013900
#print axioms _root_.GD.N0232.N0720.N1218.d013901
