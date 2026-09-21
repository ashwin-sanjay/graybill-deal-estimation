import GD.Module1286














set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set
open scoped ENNReal NNReal

namespace GD.N0106.N0428.N0765.N1616
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1539 _root_.GD.N0106.N0428.N0765.N1521 _root_.GD.N0106.N0428.N0765.N1534

def d020929 (z : ℝ) : ℝ := z ^ 2 + (1 - z) ^ 2
def d020930 (z : ℝ) : ℝ := z ^ 2 / _root_.GD.N0106.N0428.N0765.N1616.d020929 z
def d020931 (z : ℝ) : ℝ := 2 * z * (1 - z) / _root_.GD.N0106.N0428.N0765.N1616.d020929 z ^ 2

theorem d020932 (z : ℝ) : 0 < _root_.GD.N0106.N0428.N0765.N1616.d020929 z := by
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020929
  nlinarith [sq_nonneg z, sq_nonneg (1 - z)]

@[fun_prop] theorem d020933 : Measurable _root_.GD.N0106.N0428.N0765.N1616.d020930 := by
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020930 _root_.GD.N0106.N0428.N0765.N1616.d020929
  fun_prop

theorem d020934 (z : ℝ) :
    1 - _root_.GD.N0106.N0428.N0765.N1616.d020930 z = (1 - z) ^ 2 / _root_.GD.N0106.N0428.N0765.N1616.d020929 z := by
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020930
  field_simp [(_root_.GD.N0106.N0428.N0765.N1616.d020932 z).ne']
  simp [_root_.GD.N0106.N0428.N0765.N1616.d020929]

theorem d020935 {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) : 0 < _root_.GD.N0106.N0428.N0765.N1616.d020931 z := by
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020931
  exact div_pos (mul_pos (mul_pos (by norm_num) hz.1) (sub_pos.mpr hz.2))
    (sq_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1616.d020932 z))

theorem d020936 (z : ℝ) : HasDerivAt _root_.GD.N0106.N0428.N0765.N1616.d020930 (_root_.GD.N0106.N0428.N0765.N1616.d020931 z) z := by
  have hd : HasDerivAt _root_.GD.N0106.N0428.N0765.N1616.d020929 (2 * z - 2 * (1 - z)) z := by
    apply ((hasDerivAt_pow 2 z).fun_add
      (((hasDerivAt_id z).const_sub 1).fun_pow 2)).congr_deriv
    dsimp only [id]
    ring
  apply ((hasDerivAt_pow 2 z).fun_div hd (_root_.GD.N0106.N0428.N0765.N1616.d020932 z).ne').congr_deriv
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020931 _root_.GD.N0106.N0428.N0765.N1616.d020929
  ring

theorem d020937 : InjOn _root_.GD.N0106.N0428.N0765.N1616.d020930 (Ioo 0 1) := by
  intro x hx y hy hxy
  have hx0 := (_root_.GD.N0106.N0428.N0765.N1616.d020932 x).ne'
  have hy0 := (_root_.GD.N0106.N0428.N0765.N1616.d020932 y).ne'
  have hcross : x ^ 2 * (1 - y) ^ 2 = y ^ 2 * (1 - x) ^ 2 := by
    have h := (div_eq_div_iff hx0 hy0).1 hxy
    unfold _root_.GD.N0106.N0428.N0765.N1616.d020929 at h
    nlinarith
  have hxprod : 0 < x * (1 - y) := mul_pos hx.1 (sub_pos.mpr hy.2)
  have hyprod : 0 < y * (1 - x) := mul_pos hy.1 (sub_pos.mpr hx.2)
  have heq : x * (1 - y) = y * (1 - x) := by
    apply (sq_eq_sq₀ hxprod.le hyprod.le).1
    simpa only [mul_pow] using hcross
  nlinarith

theorem d020938 : _root_.GD.N0106.N0428.N0765.N1616.d020930 '' Ioo 0 1 = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨div_pos (sq_pos_of_pos hz.1) (_root_.GD.N0106.N0428.N0765.N1616.d020932 z), ?_⟩
    have h : 0 < 1 - _root_.GD.N0106.N0428.N0765.N1616.d020930 z := by
      rw [_root_.GD.N0106.N0428.N0765.N1616.d020934]
      exact div_pos (sq_pos_of_pos (sub_pos.mpr hz.2)) (_root_.GD.N0106.N0428.N0765.N1616.d020932 z)
    linarith
  · intro ht
    let r := Real.sqrt t
    let s := Real.sqrt (1 - t)
    have hr : 0 < r := Real.sqrt_pos.2 ht.1
    have hs : 0 < s := Real.sqrt_pos.2 (sub_pos.mpr ht.2)
    have hr2 : r ^ 2 = t := Real.sq_sqrt ht.1.le
    have hs2 : s ^ 2 = 1 - t := Real.sq_sqrt (sub_pos.mpr ht.2).le
    have hrs : 0 < r + s := add_pos hr hs
    refine ⟨r / (r + s), ⟨div_pos hr hrs, (div_lt_one hrs).2 (by linarith)⟩, ?_⟩
    have hsub : 1 - r / (r + s) = s / (r + s) := by field_simp; ring
    have hchart : _root_.GD.N0106.N0428.N0765.N1616.d020930 (r / (r + s)) = r ^ 2 / (r ^ 2 + s ^ 2) := by
      unfold _root_.GD.N0106.N0428.N0765.N1616.d020930 _root_.GD.N0106.N0428.N0765.N1616.d020929
      rw [hsub]
      simp only [div_pow]
      rw [← add_div, div_div_div_cancel_right₀ (pow_ne_zero 2 hrs.ne')]
    rw [hchart, hr2, hs2]
    ring

theorem d020939 (g : ℝ → ℝ) :
    (∫ l in Ioo (0 : ℝ) 1, g l) =
      ∫ z in Ioo (0 : ℝ) 1, _root_.GD.N0106.N0428.N0765.N1616.d020931 z * g (_root_.GD.N0106.N0428.N0765.N1616.d020930 z) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun z (_ : z ∈ Ioo (0 : ℝ) 1) => (_root_.GD.N0106.N0428.N0765.N1616.d020936 z).hasDerivWithinAt)
    _root_.GD.N0106.N0428.N0765.N1616.d020937 g
  rw [_root_.GD.N0106.N0428.N0765.N1616.d020938] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  simp only [abs_of_pos (_root_.GD.N0106.N0428.N0765.N1616.d020935 hz), smul_eq_mul]

theorem d020940 (g : ℝ → ℝ) :
    IntegrableOn g (Ioo (0 : ℝ) 1) ↔
      IntegrableOn (fun z => _root_.GD.N0106.N0428.N0765.N1616.d020931 z * g (_root_.GD.N0106.N0428.N0765.N1616.d020930 z)) (Ioo (0 : ℝ) 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun z (_ : z ∈ Ioo (0 : ℝ) 1) => (_root_.GD.N0106.N0428.N0765.N1616.d020936 z).hasDerivWithinAt)
    _root_.GD.N0106.N0428.N0765.N1616.d020937 g
  rw [_root_.GD.N0106.N0428.N0765.N1616.d020938] at h
  rw [h]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  simp only [abs_of_pos (_root_.GD.N0106.N0428.N0765.N1616.d020935 hz), smul_eq_mul]

theorem d020941 (g : ℝ → ℝ) :
    (∫ l in Ioo (0 : ℝ) 1, g l) =
      ∫ c, (Real.sigmoid c * (1 - Real.sigmoid c)) * g (Real.sigmoid c) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun c (_ : c ∈ (univ : Set ℝ)) => (Real.hasDerivAt_sigmoid c).hasDerivWithinAt)
    Real.sigmoid_injective.injOn g
  have hsign : ∀ c, |Real.sigmoid c * (1 - Real.sigmoid c)| =
      Real.sigmoid c * (1 - Real.sigmoid c) := fun c =>
    abs_of_pos (mul_pos (Real.sigmoid_pos c) (sub_pos.mpr (Real.sigmoid_lt_one c)))
  simpa only [Set.image_univ, Real.range_sigmoid, Measure.restrict_univ, smul_eq_mul,
    hsign] using h

theorem d020942 (g : ℝ → ℝ) :
    IntegrableOn g (Ioo (0 : ℝ) 1) ↔
      Integrable (fun c => (Real.sigmoid c * (1 - Real.sigmoid c)) * g (Real.sigmoid c)) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun c (_ : c ∈ (univ : Set ℝ)) => (Real.hasDerivAt_sigmoid c).hasDerivWithinAt)
    Real.sigmoid_injective.injOn g
  have hsign : ∀ c, |Real.sigmoid c * (1 - Real.sigmoid c)| =
      Real.sigmoid c * (1 - Real.sigmoid c) := fun c =>
    abs_of_pos (mul_pos (Real.sigmoid_pos c) (sub_pos.mpr (Real.sigmoid_lt_one c)))
  simpa only [Set.image_univ, Real.range_sigmoid, IntegrableOn, Measure.restrict_univ,
    smul_eq_mul, hsign] using h

theorem d020943 {eta u v w : ℝ} (heta : 0 < eta) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 < w) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    0 < _root_.GD.N0106.N0428.N0765.N1534.d005328 eta u v w l := by
  have hl0 := hl.1
  have hl1 : 0 ≤ 1 - l := sub_nonneg.mpr hl.2
  have hthird : 0 ≤ (1 + eta) * u * l * (1 - l) := by positivity
  have hsecond : 0 ≤ eta * w * l := by positivity
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005328
  rcases lt_or_eq_of_le hl.2 with hlt | heq
  · have hfirst : 0 < v * (1 - l) := mul_pos hv (sub_pos.mpr hlt)
    linarith
  · subst l
    simpa using mul_pos heta hw

theorem d020944 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w) (Icc 0 1) := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005329
  apply ContinuousOn.mul
  · exact ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 9 / 2)).comp
      (by fun_prop : Continuous fun l : ℝ => l * (1 - l))).continuousOn
  · exact (by unfold _root_.GD.N0106.N0428.N0765.N1534.d005328; fun_prop : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1534.d005328 eta u v w) (Icc 0 1)).rpow_const
      (fun l hl => Or.inl (_root_.GD.N0106.N0428.N0765.N1616.d020943 heta hu hv hw hl).ne')

theorem d020945 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    IntegrableOn (_root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w) (Ioo (0 : ℝ) 1) ∧
      IntegrableOn (fun l => l * _root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w l) (Ioo (0 : ℝ) 1) := by
  have hc := _root_.GD.N0106.N0428.N0765.N1616.d020944 heta hu hv hw
  exact ⟨(hc.intervalIntegrable_of_Icc zero_le_one).1.mono Ioo_subset_Ioc_self le_rfl,
    ((continuousOn_id.mul hc).intervalIntegrable_of_Icc zero_le_one).1.mono
      Ioo_subset_Ioc_self le_rfl⟩

def d020946 (eta u v w z : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1616.d020929 z * (v * (1 - z) ^ 2 + eta * w * z ^ 2) +
    (1 + eta) * u * z ^ 2 * (1 - z) ^ 2

theorem d020947 (eta u v w z : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1534.d005328 eta u v w (_root_.GD.N0106.N0428.N0765.N1616.d020930 z) = _root_.GD.N0106.N0428.N0765.N1616.d020946 eta u v w z / _root_.GD.N0106.N0428.N0765.N1616.d020929 z ^ 2 := by
  simp only [_root_.GD.N0106.N0428.N0765.N1534.d005328, _root_.GD.N0106.N0428.N0765.N1616.d020934]
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020930 _root_.GD.N0106.N0428.N0765.N1616.d020946
  field_simp [(_root_.GD.N0106.N0428.N0765.N1616.d020932 z).ne']

theorem d020948 {r : ℝ} (hr : 0 ≤ r) :
    (r ^ 2) ^ ((9 : ℝ) / 2) = r ^ 9 := by
  rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr]
  norm_num [Real.rpow_natCast]

theorem d020949 {d : ℝ} (hd : 0 < d) :
    (d ^ 2) ^ (-((21 : ℝ) / 2)) = (d ^ 21)⁻¹ := by
  rw [← Real.rpow_natCast d 2, ← Real.rpow_mul hd.le]
  norm_num [Real.rpow_neg hd.le, Real.rpow_natCast]

def d020950 (eta u v w z : ℝ) : ℝ :=
  2 * z ^ 10 * (1 - z) ^ 10 * _root_.GD.N0106.N0428.N0765.N1616.d020929 z ^ 10 *
    _root_.GD.N0106.N0428.N0765.N1616.d020946 eta u v w z ^ (-((21 : ℝ) / 2))

def d020951 (eta u v w z : ℝ) : ℝ :=
  2 * z ^ 12 * (1 - z) ^ 10 * _root_.GD.N0106.N0428.N0765.N1616.d020929 z ^ 9 *
    _root_.GD.N0106.N0428.N0765.N1616.d020946 eta u v w z ^ (-((21 : ℝ) / 2))

theorem d020952 {eta u v w z : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1616.d020931 z * _root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w (_root_.GD.N0106.N0428.N0765.N1616.d020930 z) = _root_.GD.N0106.N0428.N0765.N1616.d020950 eta u v w z := by
  have hden := _root_.GD.N0106.N0428.N0765.N1616.d020932 z
  have hl : _root_.GD.N0106.N0428.N0765.N1616.d020930 z ∈ Ioo (0 : ℝ) 1 := _root_.GD.N0106.N0428.N0765.N1616.d020938 ▸ mem_image_of_mem _ hz
  have hP : 0 < _root_.GD.N0106.N0428.N0765.N1616.d020946 eta u v w z := by
    have hC := _root_.GD.N0106.N0428.N0765.N1616.d020943 heta hu hv hw (Ioo_subset_Icc_self hl)
    rw [_root_.GD.N0106.N0428.N0765.N1616.d020947] at hC
    exact (div_pos_iff_of_pos_right (sq_pos_of_pos hden)).1 hC
  have hprod : _root_.GD.N0106.N0428.N0765.N1616.d020930 z * (1 - _root_.GD.N0106.N0428.N0765.N1616.d020930 z) =
      (z * (1 - z) / _root_.GD.N0106.N0428.N0765.N1616.d020929 z) ^ 2 := by
    rw [_root_.GD.N0106.N0428.N0765.N1616.d020934, _root_.GD.N0106.N0428.N0765.N1616.d020930]
    ring
  have hr : 0 ≤ z * (1 - z) / _root_.GD.N0106.N0428.N0765.N1616.d020929 z :=
    (div_pos (mul_pos hz.1 (sub_pos.mpr hz.2)) hden).le
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005329, hprod, _root_.GD.N0106.N0428.N0765.N1616.d020948 hr, _root_.GD.N0106.N0428.N0765.N1616.d020947,
    Real.div_rpow hP.le (sq_nonneg _), _root_.GD.N0106.N0428.N0765.N1616.d020949 hden]
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020931 _root_.GD.N0106.N0428.N0765.N1616.d020950
  field_simp [hden.ne']

theorem d020953 {eta u v w z : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1616.d020931 z * (_root_.GD.N0106.N0428.N0765.N1616.d020930 z * _root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w (_root_.GD.N0106.N0428.N0765.N1616.d020930 z)) =
      _root_.GD.N0106.N0428.N0765.N1616.d020951 eta u v w z := by
  rw [mul_left_comm, _root_.GD.N0106.N0428.N0765.N1616.d020952 heta hu hv hw hz]
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020930 _root_.GD.N0106.N0428.N0765.N1616.d020950 _root_.GD.N0106.N0428.N0765.N1616.d020951
  field_simp [(_root_.GD.N0106.N0428.N0765.N1616.d020932 z).ne']

theorem d020954 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w =
      (∫ z in Ioo (0 : ℝ) 1, _root_.GD.N0106.N0428.N0765.N1616.d020951 eta u v w z) /
        ∫ z in Ioo (0 : ℝ) 1, _root_.GD.N0106.N0428.N0765.N1616.d020950 eta u v w z := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005330
  simp only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [_root_.GD.N0106.N0428.N0765.N1616.d020939 (fun l => l * _root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w l),
    _root_.GD.N0106.N0428.N0765.N1616.d020939 (_root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w)]
  congr 1 <;> apply integral_congr_ae <;>
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  · exact _root_.GD.N0106.N0428.N0765.N1616.d020953 heta hu hv hw hz
  · exact _root_.GD.N0106.N0428.N0765.N1616.d020952 heta hu hv hw hz

theorem d020955 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    IntegrableOn (_root_.GD.N0106.N0428.N0765.N1616.d020950 eta u v w) (Ioo (0 : ℝ) 1) ∧
      IntegrableOn (_root_.GD.N0106.N0428.N0765.N1616.d020951 eta u v w) (Ioo (0 : ℝ) 1) := by
  have hk := _root_.GD.N0106.N0428.N0765.N1616.d020945 heta hu hv hw
  constructor
  · apply ((_root_.GD.N0106.N0428.N0765.N1616.d020940 _).1 hk.1).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact _root_.GD.N0106.N0428.N0765.N1616.d020952 heta hu hv hw hz
  · apply ((_root_.GD.N0106.N0428.N0765.N1616.d020940 _).1 hk.2).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact _root_.GD.N0106.N0428.N0765.N1616.d020953 heta hu hv hw hz

def d020956 (eta u v w c : ℝ) : ℝ :=
  v + (v + eta * w + (1 + eta) * u) * Real.exp c + eta * w * (Real.exp c) ^ 2

def d020957 (eta u v w c : ℝ) : ℝ :=
  Real.exp (11 * c / 2) * (1 + Real.exp c) ^ 10 *
    _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-((21 : ℝ) / 2))

def d020958 (eta u v w c : ℝ) : ℝ :=
  Real.exp (13 * c / 2) * (1 + Real.exp c) ^ 9 *
    _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-((21 : ℝ) / 2))

theorem d020959 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (c : ℝ) :
    0 < _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c := by
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020956
  positivity

theorem d020960 (eta u v w c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1534.d005328 eta u v w (Real.sigmoid c) =
      _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c / (1 + Real.exp c) ^ 2 := by
  simp only [_root_.GD.N0106.N0428.N0765.N1534.d005328, _root_.GD.N0106.N0428.N0765.N1539.d005370, _root_.GD.N0106.N0428.N0765.N1539.d005369]
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020956
  field_simp [show 1 + Real.exp c ≠ 0 by positivity]
  ring

theorem d020961 {r d q : ℝ} (hr : 0 < r) (hd : 0 < d) (hq : 0 < q) :
    (r / d ^ 2) * ((r / d ^ 2) ^ ((9 : ℝ) / 2) *
      (q / d ^ 2) ^ (-((21 : ℝ) / 2))) =
      r ^ ((11 : ℝ) / 2) * d ^ 10 * q ^ (-((21 : ℝ) / 2)) := by
  have h11 : r ^ ((11 : ℝ) / 2) = r ^ ((9 : ℝ) / 2) * r := by
    rw [show (11 : ℝ) / 2 = 9 / 2 + 1 by norm_num, Real.rpow_add_one hr.ne']
  rw [Real.div_rpow hr.le (sq_nonneg _), Real.div_rpow hq.le (sq_nonneg _),
    _root_.GD.N0106.N0428.N0765.N1616.d020948 hd.le, _root_.GD.N0106.N0428.N0765.N1616.d020949 hd, h11]
  field_simp [hd.ne']

theorem d020962 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (c : ℝ) :
    (Real.sigmoid c * (1 - Real.sigmoid c)) *
      _root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w (Real.sigmoid c) = _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
  have hprod : Real.sigmoid c * (1 - Real.sigmoid c) =
      Real.exp c / (1 + Real.exp c) ^ 2 := by
    rw [_root_.GD.N0106.N0428.N0765.N1539.d005370, _root_.GD.N0106.N0428.N0765.N1539.d005369, ← one_div (1 + Real.exp c),
      div_mul_div_comm, mul_one, pow_two]
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005329, hprod, _root_.GD.N0106.N0428.N0765.N1616.d020960,
    _root_.GD.N0106.N0428.N0765.N1616.d020961 (Real.exp_pos c) (by positivity) (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c)]
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020957
  rw [show 11 * c / 2 = c * ((11 : ℝ) / 2) by ring, Real.exp_mul]

theorem d020963 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (c : ℝ) :
    (Real.sigmoid c * (1 - Real.sigmoid c)) *
      (Real.sigmoid c * _root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w (Real.sigmoid c)) =
      _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c := by
  rw [mul_left_comm, _root_.GD.N0106.N0428.N0765.N1616.d020962 heta hu hv hw c]
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020957 _root_.GD.N0106.N0428.N0765.N1616.d020958
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005369, show 13 * c / 2 = c + 11 * c / 2 by ring, Real.exp_add]
  field_simp [show 1 + Real.exp c ≠ 0 by positivity]

theorem d020964 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w = (∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c) / ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005330
  simp only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [_root_.GD.N0106.N0428.N0765.N1616.d020941 (fun l => l * _root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w l),
    _root_.GD.N0106.N0428.N0765.N1616.d020941 (_root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w)]
  congr 1 <;> apply integral_congr_ae <;> apply Filter.Eventually.of_forall
  · exact fun c => _root_.GD.N0106.N0428.N0765.N1616.d020963 heta hu hv hw c
  · exact fun c => _root_.GD.N0106.N0428.N0765.N1616.d020962 heta hu hv hw c

theorem d020965 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w) ∧ Integrable (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w) := by
  have hk := _root_.GD.N0106.N0428.N0765.N1616.d020945 heta hu hv hw
  exact ⟨((_root_.GD.N0106.N0428.N0765.N1616.d020942 _).1 hk.1).congr
      (Filter.Eventually.of_forall fun c => _root_.GD.N0106.N0428.N0765.N1616.d020962 heta hu hv hw c),
    ((_root_.GD.N0106.N0428.N0765.N1616.d020942 _).1 hk.2).congr
      (Filter.Eventually.of_forall fun c => _root_.GD.N0106.N0428.N0765.N1616.d020963 heta hu hv hw c)⟩

theorem d020966 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    0 < ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
  have hnum : (∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w l) =
      ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      _root_.GD.N0106.N0428.N0765.N1616.d020941]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun c => _root_.GD.N0106.N0428.N0765.N1616.d020962 heta hu hv hw c
  rw [← hnum]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((_root_.GD.N0106.N0428.N0765.N1616.d020944 heta hu hv hw).intervalIntegrable_of_Icc zero_le_one)
    _ zero_lt_one
  intro l hl
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005329
  exact mul_pos (Real.rpow_pos_of_pos (mul_pos hl.1 (sub_pos.mpr hl.2)) _)
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1616.d020943 heta hu hv hw (Ioo_subset_Icc_self hl)) _)

theorem d020967 {eta u v w k : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (hk : 0 < k) :
    _root_.GD.N0106.N0428.N0765.N1534.d005330 eta (k * u) (k * v) (k * w) = _root_.GD.N0106.N0428.N0765.N1534.d005330 eta u v w := by
  have hker : ∀ l ∈ Icc (0 : ℝ) 1,
      _root_.GD.N0106.N0428.N0765.N1534.d005329 eta (k * u) (k * v) (k * w) l =
        k ^ (-((21 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w l := by
    intro l hl
    have hC : _root_.GD.N0106.N0428.N0765.N1534.d005328 eta (k * u) (k * v) (k * w) l = k * _root_.GD.N0106.N0428.N0765.N1534.d005328 eta u v w l := by
      unfold _root_.GD.N0106.N0428.N0765.N1534.d005328
      ring
    rw [_root_.GD.N0106.N0428.N0765.N1534.d005329, hC, Real.mul_rpow hk.le (_root_.GD.N0106.N0428.N0765.N1616.d020943 heta hu hv hw hl).le]
    unfold _root_.GD.N0106.N0428.N0765.N1534.d005329
    ring
  have hden : (∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1534.d005329 eta (k * u) (k * v) (k * w) l) =
      k ^ (-((21 : ℝ) / 2)) * ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w l := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro l hl
    rw [Set.uIcc_of_le zero_le_one] at hl
    exact hker l hl
  have hnum : (∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1534.d005329 eta (k * u) (k * v) (k * w) l) =
      k ^ (-((21 : ℝ) / 2)) * ∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w l := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro l hl
    rw [Set.uIcc_of_le zero_le_one] at hl
    change l * _root_.GD.N0106.N0428.N0765.N1534.d005329 eta (k * u) (k * v) (k * w) l =
      k ^ (-((21 : ℝ) / 2)) * (l * _root_.GD.N0106.N0428.N0765.N1534.d005329 eta u v w l)
    rw [hker l hl]
    ring
  rw [_root_.GD.N0106.N0428.N0765.N1534.d005330, _root_.GD.N0106.N0428.N0765.N1534.d005330, hnum, hden,
    mul_div_mul_left _ _ (Real.rpow_pos_of_pos hk _).ne']


theorem d020968 (x a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1529.d020799 (Real.exp x) (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) =
      _root_.GD.N0106.N0428.N0765.N1534.d005330 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1 := by
  let k : ℝ := (1 + Real.exp a) * (1 + Real.exp b)
  have hk : 0 < k := by unfold k; positivity
  have hu : 0 ≤ _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0 := by
    change 0 ≤ Real.sigmoid a
    exact (Real.sigmoid_pos a).le
  have hv : 0 < _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 := by
    change 0 < (1 - Real.sigmoid a) * Real.sigmoid b
    exact mul_pos (sub_pos.mpr (Real.sigmoid_lt_one a)) (Real.sigmoid_pos b)
  have hw : 0 < _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2 := by
    change 0 < (1 - Real.sigmoid a) * (1 - Real.sigmoid b)
    exact mul_pos (sub_pos.mpr (Real.sigmoid_lt_one a))
      (sub_pos.mpr (Real.sigmoid_lt_one b))
  have h0 : k * _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 0 = Real.exp a * (1 + Real.exp b) := by
    change k * Real.sigmoid a = _
    rw [_root_.GD.N0106.N0428.N0765.N1539.d005369]
    unfold k
    field_simp [show 1 + Real.exp a ≠ 0 by positivity] <;> ring
  have h1 : k * _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 1 = Real.exp b := by
    change k * ((1 - Real.sigmoid a) * Real.sigmoid b) = _
    rw [_root_.GD.N0106.N0428.N0765.N1539.d005370, _root_.GD.N0106.N0428.N0765.N1539.d005369]
    unfold k
    field_simp [show 1 + Real.exp a ≠ 0 by positivity,
      show 1 + Real.exp b ≠ 0 by positivity] <;> ring
  have h2 : k * _root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b) 2 = 1 := by
    change k * ((1 - Real.sigmoid a) * (1 - Real.sigmoid b)) = _
    rw [_root_.GD.N0106.N0428.N0765.N1539.d005370, _root_.GD.N0106.N0428.N0765.N1539.d005370]
    unfold k
    field_simp [show 1 + Real.exp a ≠ 0 by positivity,
      show 1 + Real.exp b ≠ 0 by positivity] <;> ring
  have h := _root_.GD.N0106.N0428.N0765.N1616.d020967 (Real.exp_pos x) hu hv hw hk
  rw [h0, h1, h2] at h
  exact h.symm


theorem d020969 (x a b c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1616.d020956 (Real.exp x) (Real.exp a * (1 + Real.exp b)) (Real.exp b) 1 c =
      Real.exp b + (Real.exp b + Real.exp x + Real.exp a * (1 + Real.exp b) *
        (1 + Real.exp x)) * Real.exp c + Real.exp x * Real.exp (2 * c) := by
  rw [show 2 * c = c + c by ring, Real.exp_add]
  unfold _root_.GD.N0106.N0428.N0765.N1616.d020956
  ring


theorem d020970 (x a b : ℝ) :
    let eta := Real.exp x
    let u := Real.exp a * (1 + Real.exp b)
    let v := Real.exp b
    Integrable (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v 1) ∧ Integrable (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v 1) ∧
      0 < (∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v 1 c) ∧
      _root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) =
        (∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v 1 c) / ∫ c, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v 1 c := by
  dsimp
  have hi := _root_.GD.N0106.N0428.N0765.N1616.d020965 (Real.exp_pos x)
    (by positivity : 0 ≤ Real.exp a * (1 + Real.exp b)) (Real.exp_pos b) zero_lt_one
  refine ⟨hi.1, hi.2, _root_.GD.N0106.N0428.N0765.N1616.d020966 (Real.exp_pos x) (by positivity)
    (Real.exp_pos b) zero_lt_one, ?_⟩
  rw [_root_.GD.N0106.N0428.N0765.N1616.d020968, _root_.GD.N0106.N0428.N0765.N1616.d020964 (Real.exp_pos x) (by positivity)
    (Real.exp_pos b) zero_lt_one]

end
end GD.N0106.N0428.N0765.N1616

#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020936
#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020938
#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020940
#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020942
#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020947
#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020954
#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020955
#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020960
#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020964
#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020965
#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020966
#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020968
#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020969
#print axioms _root_.GD.N0106.N0428.N0765.N1616.d020970
