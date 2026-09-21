import GD.Module0277
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv


















open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace GD.N0232.N0720.N1413

open _root_.GD.N0232.N0720.N1415

noncomputable section


def d004095 (a b center : ℝ) : ℝ :=
  1 + |a| + |b| + |center|

theorem d004096 (a b center : ℝ) :
    0 < _root_.GD.N0232.N0720.N1413.d004095 a b center := by
  unfold _root_.GD.N0232.N0720.N1413.d004095
  positivity


def d004097 (a b center : ℝ) : ℝ :=
  1 / (2 * _root_.GD.N0232.N0720.N1413.d004095 a b center)

theorem d004098 (a b center : ℝ) :
    0 < _root_.GD.N0232.N0720.N1413.d004097 a b center := by
  unfold _root_.GD.N0232.N0720.N1413.d004097
  exact div_pos (by norm_num) (mul_pos (by norm_num) (_root_.GD.N0232.N0720.N1413.d004096 a b center))

private theorem d004099 (a b center : ℝ) (x : Icc a b) :
    |(x : ℝ) - center| ≤ _root_.GD.N0232.N0720.N1413.d004095 a b center := by
  have hx : |(x : ℝ)| ≤ |a| + |b| := by
    apply abs_le.mpr
    constructor
    · linarith [x.2.1, neg_abs_le a, abs_nonneg b]
    · linarith [x.2.2, le_abs_self b, abs_nonneg a]
  calc
    |(x : ℝ) - center| ≤ |(x : ℝ)| + |center| := abs_sub _ _
    _ ≤ _root_.GD.N0232.N0720.N1413.d004095 a b center := by unfold _root_.GD.N0232.N0720.N1413.d004095; linarith

private theorem d004100 (a b center : ℝ) {t : ℝ}
    (ht : |t| < _root_.GD.N0232.N0720.N1413.d004097 a b center) (x : Icc a b) :
    0 < 1 - t * ((x : ℝ) - center) := by
  have hB := _root_.GD.N0232.N0720.N1413.d004096 a b center
  have hrad : _root_.GD.N0232.N0720.N1413.d004097 a b center * _root_.GD.N0232.N0720.N1413.d004095 a b center = (1 / 2 : ℝ) := by
    unfold _root_.GD.N0232.N0720.N1413.d004097
    field_simp [ne_of_gt hB]
  have hprod : |t * ((x : ℝ) - center)| < (1 / 2 : ℝ) := by
    rw [abs_mul]
    calc
      |t| * |(x : ℝ) - center| ≤ |t| * _root_.GD.N0232.N0720.N1413.d004095 a b center :=
        mul_le_mul_of_nonneg_left (_root_.GD.N0232.N0720.N1413.d004099 a b center x) (abs_nonneg t)
      _ < _root_.GD.N0232.N0720.N1413.d004097 a b center * _root_.GD.N0232.N0720.N1413.d004095 a b center :=
        mul_lt_mul_of_pos_right ht hB
      _ = (1 / 2 : ℝ) := hrad
  linarith [(abs_lt.mp hprod).2]

private theorem d004101 (a b center : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (-(_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) (_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) :
    |t| < _root_.GD.N0232.N0720.N1413.d004097 a b center := by
  exact (abs_lt).2
    ⟨(neg_lt_neg (half_lt_self (_root_.GD.N0232.N0720.N1413.d004098 a b center))).trans ht.1,
      ht.2.trans (half_lt_self (_root_.GD.N0232.N0720.N1413.d004098 a b center))⟩


def d004102 (q : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (q + (i : ℝ))

@[simp] theorem d004103 (q : ℝ) : _root_.GD.N0232.N0720.N1413.d004102 q 0 = 1 := by
  simp [_root_.GD.N0232.N0720.N1413.d004102]

theorem d004104 (q : ℝ) (n : ℕ) :
    _root_.GD.N0232.N0720.N1413.d004102 q (n + 1) = _root_.GD.N0232.N0720.N1413.d004102 q n * (q + (n : ℝ)) := by
  simp [_root_.GD.N0232.N0720.N1413.d004102, Finset.prod_range_succ]


def d004105 (a b center q : ℝ) (j n : ℕ) (t : ℝ) (x : Icc a b) : ℝ :=
  _root_.GD.N0232.N0720.N1413.d004102 q n * ((x : ℝ) - center) ^ (n + j) *
    (1 - t * ((x : ℝ) - center)) ^ (-q - (n : ℝ))

private theorem d004106 (a b center q : ℝ) (j n : ℕ)
    {t : ℝ} (ht : |t| < _root_.GD.N0232.N0720.N1413.d004097 a b center) (x : Icc a b) :
    HasDerivAt (fun s ↦ _root_.GD.N0232.N0720.N1413.d004105 a b center q j n s x)
      (_root_.GD.N0232.N0720.N1413.d004105 a b center q j (n + 1) t x) t := by
  have hinner :
      HasDerivAt (fun s : ℝ ↦ 1 - s * ((x : ℝ) - center))
        (-((x : ℝ) - center)) t := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id t).mul_const ((x : ℝ) - center)).const_sub 1
  have hpow := hinner.rpow_const (p := -q - (n : ℝ))
    (Or.inl (ne_of_gt (_root_.GD.N0232.N0720.N1413.d004100 a b center ht x)))
  have hraw :=
    (hasDerivAt_const t (_root_.GD.N0232.N0720.N1413.d004102 q n * ((x : ℝ) - center) ^ (n + j))).mul hpow
  convert hraw using 1
  · ext <;> rfl
  · ext <;> rfl
  · funext s
    rfl
  · unfold _root_.GD.N0232.N0720.N1413.d004105
    rw [_root_.GD.N0232.N0720.N1413.d004104,
      show -q - ((n + 1 : ℕ) : ℝ) = -q - (n : ℝ) - 1 by push_cast; ring,
      show n + 1 + j = (n + j) + 1 by omega, pow_succ]
    ring

private theorem d004107 (a b center q : ℝ) (j n : ℕ)
    {t : ℝ} (ht : |t| < _root_.GD.N0232.N0720.N1413.d004097 a b center) :
    Continuous (_root_.GD.N0232.N0720.N1413.d004105 a b center q j n t) := by
  unfold _root_.GD.N0232.N0720.N1413.d004105
  apply Continuous.mul
  · fun_prop
  apply Continuous.rpow_const
  · fun_prop
  · intro x
    exact Or.inl (ne_of_gt (_root_.GD.N0232.N0720.N1413.d004100 a b center ht x))

private theorem d004108 (a b center q : ℝ) (j n : ℕ) :
    ContinuousOn
      (fun u : ℝ × Icc a b ↦ _root_.GD.N0232.N0720.N1413.d004105 a b center q j n u.1 u.2)
      (Icc (-(_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) (_root_.GD.N0232.N0720.N1413.d004097 a b center / 2) ×ˢ
        (Set.univ : Set (Icc a b))) := by
  unfold _root_.GD.N0232.N0720.N1413.d004105
  apply ContinuousOn.mul
  · fun_prop
  apply ContinuousOn.rpow_const
  · fun_prop
  · intro u hu
    apply Or.inl
    apply ne_of_gt
    apply _root_.GD.N0232.N0720.N1413.d004100 a b center
    exact ((abs_le).2 hu.1).trans_lt (half_lt_self (_root_.GD.N0232.N0720.N1413.d004098 a b center))

private theorem d004109 (a b center q : ℝ) (j n : ℕ)
    (mu : Measure (Icc a b)) [IsFiniteMeasure mu]
    {t : ℝ} (ht : |t| < _root_.GD.N0232.N0720.N1413.d004097 a b center) :
    Integrable (_root_.GD.N0232.N0720.N1413.d004105 a b center q j n t) mu :=
  (_root_.GD.N0232.N0720.N1413.d004107 a b center q j n ht).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact



theorem d004110 (a b center q : ℝ) (j n : ℕ)
    (mu : Measure (Icc a b)) [IsFiniteMeasure mu]
    {t : ℝ}
    (ht : t ∈ Ioo (-(_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) (_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) :
    HasDerivAt (fun s ↦ ∫ x, _root_.GD.N0232.N0720.N1413.d004105 a b center q j n s x ∂mu)
      (∫ x, _root_.GD.N0232.N0720.N1413.d004105 a b center q j (n + 1) t x ∂mu) t := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn
      (_root_.GD.N0232.N0720.N1413.d004108 a b center q j (n + 1))
  refine
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s x ↦ _root_.GD.N0232.N0720.N1413.d004105 a b center q j n s x)
      (F' := fun s x ↦ _root_.GD.N0232.N0720.N1413.d004105 a b center q j (n + 1) s x)
      (s := Ioo (-(_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) (_root_.GD.N0232.N0720.N1413.d004097 a b center / 2))
      (bound := fun _ : Icc a b ↦ C)
      (Ioo_mem_nhds ht.1 ht.2) ?_
      (_root_.GD.N0232.N0720.N1413.d004109 a b center q j n mu (_root_.GD.N0232.N0720.N1413.d004101 a b center ht))
      (_root_.GD.N0232.N0720.N1413.d004107 a b center q j (n + 1)
        (_root_.GD.N0232.N0720.N1413.d004101 a b center ht)).aestronglyMeasurable
      ?_ (integrable_const C) ?_).2
  · filter_upwards [isOpen_Ioo.eventually_mem ht] with s hs
    exact (_root_.GD.N0232.N0720.N1413.d004107 a b center q j n
      (_root_.GD.N0232.N0720.N1413.d004101 a b center hs)).aestronglyMeasurable
  · exact ae_of_all mu fun x s hs ↦
      hC (s, x) ⟨⟨hs.1.le, hs.2.le⟩, Set.mem_univ x⟩
  · exact ae_of_all mu fun x s hs ↦
      _root_.GD.N0232.N0720.N1413.d004106 a b center q j n (_root_.GD.N0232.N0720.N1413.d004101 a b center hs) x


def d004111 (a b center q : ℝ) (j : ℕ)
    (mu : Measure (Icc a b)) (t : ℝ) : ℝ :=
  ∫ x, ((x : ℝ) - center) ^ j *
    (1 - t * ((x : ℝ) - center)) ^ (-q) ∂mu


theorem d004112 (a b center q : ℝ) (j : ℕ)
    (mu : Measure (Icc a b)) [IsFiniteMeasure mu]
    {t : ℝ}
    (ht : t ∈ Ioo (-(_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) (_root_.GD.N0232.N0720.N1413.d004097 a b center / 2))
    (n : ℕ) :
    HasDerivAt (iteratedDeriv n (_root_.GD.N0232.N0720.N1413.d004111 a b center q j mu))
      (∫ x, _root_.GD.N0232.N0720.N1413.d004105 a b center q j (n + 1) t x ∂mu) t := by
  induction n generalizing t with
  | zero =>
      rw [iteratedDeriv_zero]
      have hfun : _root_.GD.N0232.N0720.N1413.d004111 a b center q j mu =
          fun s ↦ ∫ x, _root_.GD.N0232.N0720.N1413.d004105 a b center q j 0 s x ∂mu := by
        funext s
        simp [_root_.GD.N0232.N0720.N1413.d004111, _root_.GD.N0232.N0720.N1413.d004105]
      rw [hfun]
      exact _root_.GD.N0232.N0720.N1413.d004110 a b center q j 0 mu ht
  | succ n hn =>
      rw [iteratedDeriv_succ]
      have hderiv :
          deriv (iteratedDeriv n (_root_.GD.N0232.N0720.N1413.d004111 a b center q j mu)) =ᶠ[𝓝 t]
            fun s ↦ ∫ x, _root_.GD.N0232.N0720.N1413.d004105 a b center q j (n + 1) s x ∂mu := by
        filter_upwards [isOpen_Ioo.eventually_mem ht] with s hs
        exact (hn hs).deriv
      rw [EventuallyEq.hasDerivAt_iff hderiv]
      exact _root_.GD.N0232.N0720.N1413.d004110 a b center q j (n + 1) mu ht


theorem d004113
    (a b center q : ℝ) (j : ℕ)
    (mu : Measure (Icc a b)) [IsFiniteMeasure mu]
    {t : ℝ}
    (ht : t ∈ Ioo (-(_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) (_root_.GD.N0232.N0720.N1413.d004097 a b center / 2))
    (n : ℕ) :
    iteratedDeriv n (_root_.GD.N0232.N0720.N1413.d004111 a b center q j mu) t =
      ∫ x, _root_.GD.N0232.N0720.N1413.d004105 a b center q j n t x ∂mu := by
  cases n with
  | zero => simp [_root_.GD.N0232.N0720.N1413.d004111, _root_.GD.N0232.N0720.N1413.d004105]
  | succ n =>
      rw [iteratedDeriv_succ]
      exact (_root_.GD.N0232.N0720.N1413.d004112 a b center q j mu ht n).deriv


theorem d004114 (a b center q : ℝ) (j : ℕ)
    (mu : Measure (Icc a b)) [IsFiniteMeasure mu] (n : ℕ) :
    iteratedDeriv n (_root_.GD.N0232.N0720.N1413.d004111 a b center q j mu) 0 =
      _root_.GD.N0232.N0720.N1413.d004102 q n * _root_.GD.N0232.N0720.N1415.d004091 a b center mu (n + j) := by
  have hzero : (0 : ℝ) ∈
      Ioo (-(_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) (_root_.GD.N0232.N0720.N1413.d004097 a b center / 2) := by
    have hrad := _root_.GD.N0232.N0720.N1413.d004098 a b center
    constructor <;> linarith
  rw [_root_.GD.N0232.N0720.N1413.d004113 a b center q j mu hzero n]
  simp [_root_.GD.N0232.N0720.N1413.d004105, _root_.GD.N0232.N0720.N1415.d004091, integral_const_mul]



theorem d004115 (a b center q : ℝ) (j : ℕ)
    (mu : Measure (Icc a b)) [IsFiniteMeasure mu]
    {t : ℝ}
    (ht : t ∈ Ioo (-(_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) (_root_.GD.N0232.N0720.N1413.d004097 a b center / 2))
    (k : ℕ) : ContDiffAt ℝ k (_root_.GD.N0232.N0720.N1413.d004111 a b center q j mu) t := by
  have hsmooth : ContDiffOn ℝ (k : ℕ∞) (_root_.GD.N0232.N0720.N1413.d004111 a b center q j mu)
      (Ioo (-(_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) (_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) := by
    apply contDiffOn_of_differentiableOn_deriv
    intro n hn s hs
    have heq :
        iteratedDerivWithin n (_root_.GD.N0232.N0720.N1413.d004111 a b center q j mu)
            (Ioo (-(_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) (_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) =ᶠ[𝓝 s]
          iteratedDeriv n (_root_.GD.N0232.N0720.N1413.d004111 a b center q j mu) := by
      filter_upwards [isOpen_Ioo.eventually_mem hs] with u hu
      exact iteratedDerivWithin_of_isOpen isOpen_Ioo hu
    have hderiv := (EventuallyEq.hasDerivAt_iff heq).2
      (_root_.GD.N0232.N0720.N1413.d004112 a b center q j mu hs n)
    exact hderiv.differentiableAt.differentiableWithinAt
  exact hsmooth.contDiffAt (Ioo_mem_nhds ht.1 ht.2)



def d004116 (f : ℝ → ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n ↦ (n.factorial : ℝ)⁻¹ * iteratedDeriv n f 0

@[simp] theorem d004117 (f : ℝ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (_root_.GD.N0232.N0720.N1413.d004116 f) =
      (n.factorial : ℝ)⁻¹ * iteratedDeriv n f 0 :=
  PowerSeries.coeff_mk n _

theorem d004118 (c : ℝ) :
    _root_.GD.N0232.N0720.N1413.d004116 (fun _ ↦ c) = PowerSeries.C c := by
  ext n
  cases n with
  | zero => simp [_root_.GD.N0232.N0720.N1413.d004116, PowerSeries.coeff_C]
  | succ n => simp [_root_.GD.N0232.N0720.N1413.d004116, iteratedDeriv_const]

theorem d004119 {f g : ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffAt ℝ n f 0)
    (hg : ∀ n : ℕ, ContDiffAt ℝ n g 0) :
    _root_.GD.N0232.N0720.N1413.d004116 (f + g) = _root_.GD.N0232.N0720.N1413.d004116 f + _root_.GD.N0232.N0720.N1413.d004116 g := by
  ext n
  simp only [_root_.GD.N0232.N0720.N1413.d004117, map_add, iteratedDeriv_add (hf n) (hg n), mul_add]

theorem d004120 {f g : ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffAt ℝ n f 0)
    (hg : ∀ n : ℕ, ContDiffAt ℝ n g 0) :
    _root_.GD.N0232.N0720.N1413.d004116 (f - g) = _root_.GD.N0232.N0720.N1413.d004116 f - _root_.GD.N0232.N0720.N1413.d004116 g := by
  ext n
  simp only [_root_.GD.N0232.N0720.N1413.d004117, map_sub, iteratedDeriv_sub (hf n) (hg n), mul_sub]



theorem d004121 {f g : ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffAt ℝ n f 0)
    (hg : ∀ n : ℕ, ContDiffAt ℝ n g 0) :
    _root_.GD.N0232.N0720.N1413.d004116 (f * g) = _root_.GD.N0232.N0720.N1413.d004116 f * _root_.GD.N0232.N0720.N1413.d004116 g := by
  ext n
  simp only [_root_.GD.N0232.N0720.N1413.d004117, iteratedDeriv_mul (hf n) (hg n),
    Finset.mul_sum, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Nat.cast_choose _ (by have := Finset.mem_range.mp hi; omega)]
  field_simp [Nat.factorial_ne_zero]

theorem d004122 {f : ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffAt ℝ n f 0) (k : ℕ) :
    _root_.GD.N0232.N0720.N1413.d004116 (f ^ k) = _root_.GD.N0232.N0720.N1413.d004116 f ^ k := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero]
      rw [show (1 : ℝ → ℝ) = (fun _ ↦ (1 : ℝ)) by ext; rfl]
      simpa using _root_.GD.N0232.N0720.N1413.d004118 1
  | succ k ih =>
      rw [pow_succ,
        _root_.GD.N0232.N0720.N1413.d004121 (f := f ^ k) (g := f) (fun n ↦ (hf n).pow k) hf,
        ih, pow_succ]

theorem d004123 (c : ℝ) (f : ℝ → ℝ) :
    _root_.GD.N0232.N0720.N1413.d004116 (fun t ↦ c * f t) = PowerSeries.C c * _root_.GD.N0232.N0720.N1413.d004116 f := by
  ext n
  simp only [_root_.GD.N0232.N0720.N1413.d004117, PowerSeries.coeff_C_mul,
    iteratedDeriv_const_mul_field]
  ring

theorem d004124 {f g : ℝ → ℝ}
    (h : f =ᶠ[𝓝 (0 : ℝ)] g) : _root_.GD.N0232.N0720.N1413.d004116 f = _root_.GD.N0232.N0720.N1413.d004116 g := by
  ext n
  rw [_root_.GD.N0232.N0720.N1413.d004117, _root_.GD.N0232.N0720.N1413.d004117, h.iteratedDeriv_eq n]



theorem d004125 (a b center q : ℝ) (j : ℕ)
    (mu : Measure (Icc a b)) [IsFiniteMeasure mu] :
    _root_.GD.N0232.N0720.N1413.d004116 (_root_.GD.N0232.N0720.N1413.d004111 a b center q j mu) =
      _root_.GD.N0232.N0720.N1415.d004075 q j (_root_.GD.N0232.N0720.N1415.d004091 a b center mu) := by
  ext n
  rw [_root_.GD.N0232.N0720.N1413.d004117, _root_.GD.N0232.N0720.N1413.d004114,
    _root_.GD.N0232.N0720.N1415.d004076]
  simp only [_root_.GD.N0232.N0720.N1415.d004071, _root_.GD.N0232.N0720.N1413.d004102, div_eq_mul_inv]
  ring


def d004126 (M B A0 A1 A2 A3 : ℝ → ℝ) : ℝ → ℝ :=
  M ^ 3 * A3 - (fun t ↦ 3 * (B * M ^ 2 * A2) t) +
    (fun t ↦ 3 * (B ^ 2 * M * A1) t) - B ^ 3 * A0

private theorem d004127 (M B A0 A1 A2 A3 : ℝ → ℝ)
    (hM : ∀ n : ℕ, ContDiffAt ℝ n M 0)
    (hB : ∀ n : ℕ, ContDiffAt ℝ n B 0)
    (hA0 : ∀ n : ℕ, ContDiffAt ℝ n A0 0)
    (hA1 : ∀ n : ℕ, ContDiffAt ℝ n A1 0)
    (hA2 : ∀ n : ℕ, ContDiffAt ℝ n A2 0)
    (hA3 : ∀ n : ℕ, ContDiffAt ℝ n A3 0) :
    _root_.GD.N0232.N0720.N1413.d004116 (_root_.GD.N0232.N0720.N1413.d004126 M B A0 A1 A2 A3) =
      _root_.GD.N0232.N0720.N1413.d004116 M ^ 3 * _root_.GD.N0232.N0720.N1413.d004116 A3 -
        PowerSeries.C 3 * (_root_.GD.N0232.N0720.N1413.d004116 B * _root_.GD.N0232.N0720.N1413.d004116 M ^ 2 * _root_.GD.N0232.N0720.N1413.d004116 A2) +
        PowerSeries.C 3 * (_root_.GD.N0232.N0720.N1413.d004116 B ^ 2 * _root_.GD.N0232.N0720.N1413.d004116 M * _root_.GD.N0232.N0720.N1413.d004116 A1) -
        _root_.GD.N0232.N0720.N1413.d004116 B ^ 3 * _root_.GD.N0232.N0720.N1413.d004116 A0 := by
  have hT1 : ∀ n : ℕ, ContDiffAt ℝ n (M ^ 3 * A3) 0 :=
    fun n ↦ ((hM n).pow 3).mul (hA3 n)
  have hT2 : ∀ n : ℕ, ContDiffAt ℝ n (B * M ^ 2 * A2) 0 :=
    fun n ↦ ((hB n).mul ((hM n).pow 2)).mul (hA2 n)
  have hT3 : ∀ n : ℕ, ContDiffAt ℝ n (B ^ 2 * M * A1) 0 :=
    fun n ↦ (((hB n).pow 2).mul (hM n)).mul (hA1 n)
  have hT4 : ∀ n : ℕ, ContDiffAt ℝ n (B ^ 3 * A0) 0 :=
    fun n ↦ ((hB n).pow 3).mul (hA0 n)
  have hCT2 : ∀ n : ℕ, ContDiffAt ℝ n (fun t ↦ 3 * (B * M ^ 2 * A2) t) 0 :=
    fun n ↦ contDiffAt_const.mul (hT2 n)
  have hCT3 : ∀ n : ℕ, ContDiffAt ℝ n (fun t ↦ 3 * (B ^ 2 * M * A1) t) 0 :=
    fun n ↦ contDiffAt_const.mul (hT3 n)
  unfold _root_.GD.N0232.N0720.N1413.d004126
  rw [_root_.GD.N0232.N0720.N1413.d004120
      (f := (M ^ 3 * A3 - (fun t ↦ 3 * (B * M ^ 2 * A2) t)) +
        (fun t ↦ 3 * (B ^ 2 * M * A1) t)) (g := B ^ 3 * A0)
      (fun n ↦ ((hT1 n).sub (hCT2 n)).add (hCT3 n)) hT4,
    _root_.GD.N0232.N0720.N1413.d004119
      (f := M ^ 3 * A3 - (fun t ↦ 3 * (B * M ^ 2 * A2) t))
      (g := fun t ↦ 3 * (B ^ 2 * M * A1) t)
      (fun n ↦ (hT1 n).sub (hCT2 n)) hCT3,
    _root_.GD.N0232.N0720.N1413.d004120 (f := M ^ 3 * A3)
      (g := fun t ↦ 3 * (B * M ^ 2 * A2) t) hT1 hCT2,
    _root_.GD.N0232.N0720.N1413.d004123, _root_.GD.N0232.N0720.N1413.d004123,
    _root_.GD.N0232.N0720.N1413.d004121 (f := M ^ 3) (g := A3) (fun n ↦ (hM n).pow 3) hA3,
    _root_.GD.N0232.N0720.N1413.d004121 (f := B ^ 3) (g := A0) (fun n ↦ (hB n).pow 3) hA0,
    _root_.GD.N0232.N0720.N1413.d004121 (f := B * M ^ 2) (g := A2)
      (fun n ↦ (hB n).mul ((hM n).pow 2)) hA2,
    _root_.GD.N0232.N0720.N1413.d004121 (f := B) (g := M ^ 2) hB (fun n ↦ (hM n).pow 2),
    _root_.GD.N0232.N0720.N1413.d004121 (f := B ^ 2 * M) (g := A1)
      (fun n ↦ ((hB n).pow 2).mul (hM n)) hA1,
    _root_.GD.N0232.N0720.N1413.d004121 (f := B ^ 2) (g := M) (fun n ↦ (hB n).pow 2) hM,
    _root_.GD.N0232.N0720.N1413.d004122 hM 3, _root_.GD.N0232.N0720.N1413.d004122 hM 2,
    _root_.GD.N0232.N0720.N1413.d004122 hB 3, _root_.GD.N0232.N0720.N1413.d004122 hB 2]


def d004128 (a b center q : ℝ) (mu : Measure (Icc a b)) : ℝ → ℝ :=
  _root_.GD.N0232.N0720.N1413.d004126
    (_root_.GD.N0232.N0720.N1413.d004111 a b center q 0 mu)
    (_root_.GD.N0232.N0720.N1413.d004111 a b center q 1 mu)
    (_root_.GD.N0232.N0720.N1413.d004111 a b center (q + 1) 0 mu)
    (_root_.GD.N0232.N0720.N1413.d004111 a b center (q + 1) 1 mu)
    (_root_.GD.N0232.N0720.N1413.d004111 a b center (q + 1) 2 mu)
    (_root_.GD.N0232.N0720.N1413.d004111 a b center (q + 1) 3 mu)


theorem d004129 (a b center q : ℝ)
    (mu : Measure (Icc a b)) [IsFiniteMeasure mu] :
    _root_.GD.N0232.N0720.N1413.d004116 (_root_.GD.N0232.N0720.N1413.d004128 a b center q mu) =
      _root_.GD.N0232.N0720.N1415.d004078 q (_root_.GD.N0232.N0720.N1415.d004091 a b center mu) := by
  have hzero : (0 : ℝ) ∈
      Ioo (-(_root_.GD.N0232.N0720.N1413.d004097 a b center / 2)) (_root_.GD.N0232.N0720.N1413.d004097 a b center / 2) := by
    have hrad := _root_.GD.N0232.N0720.N1413.d004098 a b center
    constructor <;> linarith
  have hs (p : ℝ) (j : ℕ) :
      ∀ n : ℕ, ContDiffAt ℝ n (_root_.GD.N0232.N0720.N1413.d004111 a b center p j mu) 0 :=
    _root_.GD.N0232.N0720.N1413.d004115 a b center p j mu hzero
  unfold _root_.GD.N0232.N0720.N1413.d004128
  rw [_root_.GD.N0232.N0720.N1413.d004127 _ _ _ _ _ _
    (hs q 0) (hs q 1) (hs (q + 1) 0) (hs (q + 1) 1)
    (hs (q + 1) 2) (hs (q + 1) 3)]
  simp only [_root_.GD.N0232.N0720.N1413.d004125, _root_.GD.N0232.N0720.N1415.d004078]



theorem d004130
    (a b center q : ℝ) (mu : Measure (Icc a b)) [IsFiniteMeasure mu]
    (hcubic : _root_.GD.N0232.N0720.N1413.d004128 a b center q mu =ᶠ[𝓝 (0 : ℝ)] (fun _ ↦ 0)) :
    _root_.GD.N0232.N0720.N1415.d004078 q (_root_.GD.N0232.N0720.N1415.d004091 a b center mu) = 0 := by
  have h := _root_.GD.N0232.N0720.N1413.d004124 hcubic
  rw [_root_.GD.N0232.N0720.N1413.d004129, _root_.GD.N0232.N0720.N1413.d004118, map_zero] at h
  exact h

end

end GD.N0232.N0720.N1413

#print axioms _root_.GD.N0232.N0720.N1413.d004110
#print axioms _root_.GD.N0232.N0720.N1413.d004114
#print axioms _root_.GD.N0232.N0720.N1413.d004129
#print axioms _root_.GD.N0232.N0720.N1413.d004130
