import GD.Module0260
import GD.Module0261
import GD.Module0257





























namespace GD.N0232.N0719.N0889

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open _root_.GD.N0232.N0719.N1016
open _root_.GD.N0232.N0719.N0886
open _root_.GD.N0232.N0719.N0879
open _root_.GD.N0232.N0719.N0887
open _root_.GD.N0232.N0719.N0894
open _root_.GD.N0232.N0719.N0881
open _root_.GD.N0232.N0719.N0888
open _root_.GD.N0232.N0719.N0892
open _root_.GD.N0232.N0719.N0891
open _root_.GD.N0232.N0719.N0895


def d003757
    (p₁ p₂ p₃ : ℝ) (z : ℝ × (ℝ × ℝ)) : ℝ :=
  _root_.GD.N0232.N0719.N0886.d003653 p₁ p₂ p₃ z * _root_.GD.N0232.N0719.N0886.d003654 p₁ p₂ p₃ z


def d003758
    (p₁ p₂ p₃ t : ℝ) (z : ℝ × (ℝ × ℝ)) : ℝ :=
  _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
    Real.exp
      (-t * _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
        z.1 z.2.1 z.2.2)


def d003759
    (p₁ p₂ p₃ t : ℝ)
    (zu : (ℝ × (ℝ × ℝ)) × ℝ) : ℝ :=
  let z := zu.1
  let u := zu.2
  _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
    (Real.exp
        (-t * p₁ * z.1 ^ 2 +
          Real.sqrt (2 * t) * u * p₁ * z.1) *
      Real.exp
        (-t * p₂ * z.2.1 ^ 2 +
          Real.sqrt (2 * t) * u * p₂ * z.2.1) *
      Real.exp
        (-t * p₃ * z.2.2 ^ 2 +
          Real.sqrt (2 * t) * u * p₃ * z.2.2))

@[fun_prop]
theorem d003760 (p₁ p₂ p₃ : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃) := by
  unfold _root_.GD.N0232.N0719.N0889.d003757 _root_.GD.N0232.N0719.N0886.d003653 _root_.GD.N0232.N0719.N0886.d003654 _root_.GD.N0232.N0719.N1016.d003609 _root_.GD.N0232.N0719.N0886.d003650 _root_.GD.N0232.N0719.N0886.d003651 _root_.GD.N0232.N0719.N0886.d003652
  fun_prop

@[fun_prop]
theorem d003761
    (p₁ p₂ p₃ t : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0889.d003759 p₁ p₂ p₃ t) := by
  unfold _root_.GD.N0232.N0719.N0889.d003759 _root_.GD.N0232.N0719.N0889.d003757
    _root_.GD.N0232.N0719.N0886.d003653 _root_.GD.N0232.N0719.N0886.d003654 _root_.GD.N0232.N0719.N1016.d003609 _root_.GD.N0232.N0719.N0886.d003650 _root_.GD.N0232.N0719.N0886.d003651 _root_.GD.N0232.N0719.N0886.d003652
  fun_prop

theorem d003762
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) :
    0 ≤ _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z₁ z₂ z₃ := by
  unfold _root_.GD.N0232.N0719.N0881.d003572
  positivity



theorem d003763
    {p₁ p₂ p₃ : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    Integrable (_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃)
      (_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) := by
  rw [show _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ =
      _root_.GD.N0232.N0719.N0886.d003659 (_root_.GD.N0232.N0719.N0886.d003662 p₁ p₂ p₃) by
        change
          (fun z ↦
            _root_.GD.N0232.N0719.N0886.d003653 p₁ p₂ p₃ z * _root_.GD.N0232.N0719.N0886.d003654 p₁ p₂ p₃ z) =
            _root_.GD.N0232.N0719.N0886.d003659 (_root_.GD.N0232.N0719.N0886.d003662 p₁ p₂ p₃)
        exact
          _root_.GD.N0232.N0719.N0886.d003663
            h₁₂ h₁₃ h₂₃]
  exact _root_.GD.N0232.N0719.N0886.d003660 _ _ _
    (_root_.GD.N0232.N0719.N0886.d003662 p₁ p₂ p₃)


theorem d003764
    {p₁ p₂ p₃ t : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (ht : 0 ≤ t)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    Integrable (_root_.GD.N0232.N0719.N0889.d003758 p₁ p₂ p₃ t)
      (_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) := by
  have hquartic :=
    _root_.GD.N0232.N0719.N0889.d003763
      (v₁ := v₁) (v₂ := v₂) (v₃ := v₃)
      h₁₂ h₁₃ h₂₃
  apply hquartic.norm.mono'
  · exact
      (_root_.GD.N0232.N0719.N0889.d003760 p₁ p₂ p₃).mul
        (by
          apply Measurable.exp
          unfold _root_.GD.N0232.N0719.N0881.d003572 _root_.GD.N0232.N0719.N0881.d003570
          fun_prop : Measurable fun z : ℝ × (ℝ × ℝ) ↦
            Real.exp
              (-t * _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                z.1 z.2.1 z.2.2)) |>.aestronglyMeasurable
  · filter_upwards [] with z
    have hQ :
        0 ≤ _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
          z.1 z.2.1 z.2.2 :=
      _root_.GD.N0232.N0719.N0889.d003762 hp₁ hp₂ hp₃
    have hexp :
        Real.exp
          (-t * _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
            z.1 z.2.1 z.2.2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hQ
    simp only [_root_.GD.N0232.N0719.N0889.d003758, norm_mul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (abs_nonneg _) hexp





theorem d003765
    {p₁ p₂ p₃ t : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1) (ht : 0 ≤ t)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    Integrable (_root_.GD.N0232.N0719.N0889.d003759 p₁ p₂ p₃ t)
      ((_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃).prod (gaussianReal 0 1)) := by
  let μz := _root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃
  let μu := gaussianReal 0 (1 : ℝ≥0)
  have hmeas :
      AEStronglyMeasurable
        (_root_.GD.N0232.N0719.N0889.d003759 p₁ p₂ p₃ t)
        (μz.prod μu) :=
    (_root_.GD.N0232.N0719.N0889.d003761 p₁ p₂ p₃ t).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [] with z
    let A :=
      _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
        Real.exp
          (-t * _root_.GD.N0232.N0719.N0881.d003571 p₁ p₂ p₃ z.1 z.2.1 z.2.2)
    let s :=
      Real.sqrt (2 * t) *
        _root_.GD.N0232.N0719.N0881.d003570 p₁ p₂ p₃ z.1 z.2.1 z.2.2
    have hexp :
        Integrable (fun u : ℝ ↦ Real.exp (s * u)) μu := by
      dsimp [μu]
      exact integrable_exp_mul_gaussianReal s
    convert hexp.const_mul A using 1
    funext u
    dsimp [A, s, μu]
    unfold _root_.GD.N0232.N0719.N0889.d003759
    dsimp
    calc
      _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
            (Real.exp
                (-t * p₁ * z.1 ^ 2 +
                  Real.sqrt (2 * t) * u * p₁ * z.1) *
              Real.exp
                (-t * p₂ * z.2.1 ^ 2 +
                  Real.sqrt (2 * t) * u * p₂ * z.2.1) *
              Real.exp
                (-t * p₃ * z.2.2 ^ 2 +
                  Real.sqrt (2 * t) * u * p₃ * z.2.2)) =
          _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
            Real.exp
              ((-t * p₁ * z.1 ^ 2 +
                  Real.sqrt (2 * t) * u * p₁ * z.1) +
                (-t * p₂ * z.2.1 ^ 2 +
                  Real.sqrt (2 * t) * u * p₂ * z.2.1) +
                (-t * p₃ * z.2.2 ^ 2 +
                  Real.sqrt (2 * t) * u * p₃ * z.2.2)) := by
            rw [← Real.exp_add, ← Real.exp_add]
      _ =
          _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
            Real.exp
              (-t * _root_.GD.N0232.N0719.N0881.d003571 p₁ p₂ p₃ z.1 z.2.1 z.2.2 +
                Real.sqrt (2 * t) *
                  _root_.GD.N0232.N0719.N0881.d003570 p₁ p₂ p₃ z.1 z.2.1 z.2.2 * u) := by
            congr 2
            unfold _root_.GD.N0232.N0719.N0881.d003571 _root_.GD.N0232.N0719.N0881.d003570
            ring
      _ =
          _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
              Real.exp
                (-t * _root_.GD.N0232.N0719.N0881.d003571 p₁ p₂ p₃ z.1 z.2.1 z.2.2) *
            Real.exp
              (Real.sqrt (2 * t) *
                _root_.GD.N0232.N0719.N0881.d003570 p₁ p₂ p₃ z.1 z.2.1 z.2.2 * u) := by
            rw [Real.exp_add]
            ring
  · have hquartic :=
      _root_.GD.N0232.N0719.N0889.d003763
        (v₁ := v₁) (v₂ := v₂) (v₃ := v₃)
        h₁₂ h₁₃ h₂₃
    have hbound :
        Integrable
          (fun z : ℝ × (ℝ × ℝ) ↦
            ‖_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z‖ *
              Real.exp
                (-t * _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                  z.1 z.2.1 z.2.2)) μz := by
      apply hquartic.norm.mono'
      · exact
          ((_root_.GD.N0232.N0719.N0889.d003760 p₁ p₂ p₃).norm.mul
            (by
              apply Measurable.exp
              unfold _root_.GD.N0232.N0719.N0881.d003572 _root_.GD.N0232.N0719.N0881.d003570
              fun_prop : Measurable fun z : ℝ × (ℝ × ℝ) ↦
                Real.exp
                  (-t * _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                    z.1 z.2.1 z.2.2))).aestronglyMeasurable
      · filter_upwards [] with z
        have hQ :
            0 ≤ _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
              z.1 z.2.1 z.2.2 :=
          _root_.GD.N0232.N0719.N0889.d003762 hp₁ hp₂ hp₃
        have hexp :
            Real.exp
              (-t * _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                z.1 z.2.1 z.2.2) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hQ
        simp only [norm_mul, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _),
          abs_of_nonneg (abs_nonneg _)]
        exact mul_le_of_le_one_right (abs_nonneg _) hexp
    convert hbound using 1
    funext z
    have haux :=
      _root_.GD.N0232.N0719.N0881.d003577
        (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
        (z₁ := z.1) (z₂ := z.2.1) (z₃ := z.2.2)
        (t := t) (c := ‖_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z‖)
        hsum ht
    rw [haux]
    apply integral_congr_ae
    filter_upwards [] with u
    unfold _root_.GD.N0232.N0719.N0889.d003759
    dsimp
    rw [abs_mul, abs_mul, abs_mul]
    simp only [abs_of_pos (Real.exp_pos _)]


theorem d003766
    {p t : ℝ} {v : ℝ≥0}
    (hp : 0 < p) (ht : 0 ≤ t) (hv : v ≠ 0) :
    p * (_root_.GD.N0232.N0719.N0887.d003556 v (t * p) : ℝ) =
      _root_.GD.N0232.N0719.N0888.d003689 (_root_.GD.N0232.N0719.N0895.d003746 p v) t := by
  have hh :
      0 < _root_.GD.N0232.N0719.N0887.d003554 v (t * p) := by
    rw [_root_.GD.N0232.N0719.N0895.d003749]
    exact _root_.GD.N0232.N0719.N0895.d003752 hp.le ht
  rw [_root_.GD.N0232.N0719.N0887.d003561 hv hh]
  unfold _root_.GD.N0232.N0719.N0887.d003555 _root_.GD.N0232.N0719.N0887.d003554
    _root_.GD.N0232.N0719.N0888.d003689 _root_.GD.N0232.N0719.N0895.d003746
  field_simp



theorem d003767
    {p t u : ℝ} {v : ℝ≥0} :
    _root_.GD.N0232.N0719.N0887.d003557 v (t * p) (Real.sqrt (2 * t) * u * p) =
      Real.sqrt (2 * t) *
        _root_.GD.N0232.N0719.N0888.d003689 (_root_.GD.N0232.N0719.N0895.d003746 p v) t * u := by
  unfold _root_.GD.N0232.N0719.N0887.d003557 _root_.GD.N0232.N0719.N0888.d003689
    _root_.GD.N0232.N0719.N0887.d003554 _root_.GD.N0232.N0719.N0895.d003746
  ring


def d003768
    (p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ) : ℝ :=
  -_root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t /
    (_root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t ^ 2 *
      Real.sqrt
        (_root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t))





theorem d003769
    {p₁ p₂ p₃ t : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (ht : 0 ≤ t) :
    ∫ z,
        _root_.GD.N0232.N0719.N0889.d003758 p₁ p₂ p₃ t z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃ =
      _root_.GD.N0232.N0719.N0889.d003768 p₁ p₂ p₃
        (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
        (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
        (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t := by
  let d₁ := _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁
  let d₂ := _root_.GD.N0232.N0719.N0895.d003746 p₂ v₂
  let d₃ := _root_.GD.N0232.N0719.N0895.d003746 p₃ v₃
  let β₁ := _root_.GD.N0232.N0719.N0888.d003689 d₁ t
  let β₂ := _root_.GD.N0232.N0719.N0888.d003689 d₂ t
  let β₃ := _root_.GD.N0232.N0719.N0888.d003689 d₃ t
  let m := _root_.GD.N0232.N0719.N0888.d003690 p₁ p₂ p₃ d₁ d₂ d₃ t
  let d := _root_.GD.N0232.N0719.N0888.d003691 p₁ p₂ p₃ d₁ d₂ d₃ t
  let c := Real.sqrt (2 * t)
  let s₁ := _root_.GD.N0232.N0719.N0887.d003556 v₁ (t * p₁)
  let s₂ := _root_.GD.N0232.N0719.N0887.d003556 v₂ (t * p₂)
  let s₃ := _root_.GD.N0232.N0719.N0887.d003556 v₃ (t * p₃)
  have h₁₂ : p₁ + p₂ ≠ 0 := ne_of_gt (add_pos hp₁ hp₂)
  have h₁₃ : p₁ + p₃ ≠ 0 := ne_of_gt (add_pos hp₁ hp₃)
  have h₂₃ : p₂ + p₃ ≠ 0 := ne_of_gt (add_pos hp₂ hp₃)
  have hh₁ : 0 < _root_.GD.N0232.N0719.N0887.d003554 v₁ (t * p₁) := by
    rw [_root_.GD.N0232.N0719.N0895.d003749]
    exact _root_.GD.N0232.N0719.N0895.d003752 hp₁.le ht
  have hh₂ : 0 < _root_.GD.N0232.N0719.N0887.d003554 v₂ (t * p₂) := by
    rw [_root_.GD.N0232.N0719.N0895.d003749]
    exact _root_.GD.N0232.N0719.N0895.d003752 hp₂.le ht
  have hh₃ : 0 < _root_.GD.N0232.N0719.N0887.d003554 v₃ (t * p₃) := by
    rw [_root_.GD.N0232.N0719.N0895.d003749]
    exact _root_.GD.N0232.N0719.N0895.d003752 hp₃.le ht
  have hsβ₁ : p₁ * (s₁ : ℝ) = β₁ := by
    dsimp [s₁, β₁, d₁]
    exact _root_.GD.N0232.N0719.N0889.d003766 hp₁ ht hv₁
  have hsβ₂ : p₂ * (s₂ : ℝ) = β₂ := by
    dsimp [s₂, β₂, d₂]
    exact _root_.GD.N0232.N0719.N0889.d003766 hp₂ ht hv₂
  have hsβ₃ : p₃ * (s₃ : ℝ) = β₃ := by
    dsimp [s₃, β₃, d₃]
    exact _root_.GD.N0232.N0719.N0889.d003766 hp₃ ht hv₃
  have hrank : 0 < d := by
    dsimp [d, d₁, d₂, d₃]
    exact _root_.GD.N0232.N0719.N0895.d003753 hp₁.le hp₂.le hp₃.le hsum ht
  have hc_sq : c ^ 2 = 2 * t := by
    dsimp [c]
    rw [Real.sq_sqrt]
    positivity
  have hauxInt :=
    _root_.GD.N0232.N0719.N0889.d003765
      (v₁ := v₁) (v₂ := v₂) (v₃ := v₃)
      hp₁.le hp₂.le hp₃.le hsum ht h₁₂ h₁₃ h₂₃
  letI : SFinite (_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) := by
    unfold _root_.GD.N0232.N0719.N0886.d003649
    infer_instance
  calc
    (∫ z,
        _root_.GD.N0232.N0719.N0889.d003758 p₁ p₂ p₃ t z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) =
        ∫ z, ∫ u,
          _root_.GD.N0232.N0719.N0889.d003759 p₁ p₂ p₃ t (z, u)
            ∂gaussianReal 0 1
          ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃ := by
      apply integral_congr_ae
      filter_upwards [] with z
      unfold _root_.GD.N0232.N0719.N0889.d003758 _root_.GD.N0232.N0719.N0889.d003759
      dsimp
      exact
        _root_.GD.N0232.N0719.N0881.d003577
          (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
          (z₁ := z.1) (z₂ := z.2.1) (z₃ := z.2.2)
          (t := t) (c := _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z)
          hsum ht
    _ = ∫ u, ∫ z,
          _root_.GD.N0232.N0719.N0889.d003759 p₁ p₂ p₃ t (z, u)
            ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃
          ∂gaussianReal 0 1 := by
      exact integral_integral_swap hauxInt
    _ = ∫ u,
          (_root_.GD.N0232.N0719.N0895.d003747 p₁ v₁ t u *
            _root_.GD.N0232.N0719.N0895.d003747 p₂ v₂ t u *
            _root_.GD.N0232.N0719.N0895.d003747 p₃ v₃ t u) *
          (∫ z,
            _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z
            ∂_root_.GD.N0232.N0719.N0879.d003730
              (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
              s₁ s₂ s₃)
          ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      filter_upwards [] with u
      have htilt :=
        _root_.GD.N0232.N0719.N0894.d003745
          (v₁ := v₁) (v₂ := v₂) (v₃ := v₃)
          (a₁ := t * p₁)
          (b₁ := Real.sqrt (2 * t) * u * p₁)
          (a₂ := t * p₂)
          (b₂ := Real.sqrt (2 * t) * u * p₂)
          (a₃ := t * p₃)
          (b₃ := Real.sqrt (2 * t) * u * p₃)
          (fun z ↦ _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z)
          hv₁ hv₂ hv₃ hh₁ hh₂ hh₃
      rw [_root_.GD.N0232.N0719.N0889.d003767,
        _root_.GD.N0232.N0719.N0889.d003767,
        _root_.GD.N0232.N0719.N0889.d003767] at htilt
      dsimp [_root_.GD.N0232.N0719.N0895.d003747, c, β₁, β₂, β₃,
        d₁, d₂, d₃, s₁, s₂, s₃] at htilt ⊢
      convert htilt using 1
      · apply integral_congr_ae
        filter_upwards [] with z
        unfold _root_.GD.N0232.N0719.N0889.d003759 _root_.GD.N0232.N0719.N0889.d003757
        dsimp
        ring
    _ = _root_.GD.N0232.N0719.N0895.d003748 p₁ p₂ p₃ v₁ v₂ v₃ t *
          ∫ u,
            Real.exp (t * u ^ 2 * m) *
              (∫ z,
                _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z
                ∂_root_.GD.N0232.N0719.N0879.d003730
                  (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
                  s₁ s₂ s₃)
            ∂gaussianReal 0 1 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [_root_.GD.N0232.N0719.N0895.d003751 ht]
      dsimp [m, d₁, d₂, d₃]
      ring
    _ = _root_.GD.N0232.N0719.N0895.d003748 p₁ p₂ p₃ v₁ v₂ v₃ t *
          (Real.sqrt d)⁻¹ *
          ∫ u,
            (∫ z,
              _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z
              ∂_root_.GD.N0232.N0719.N0879.d003730
                (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
                s₁ s₂ s₃)
            ∂gaussianReal 0 (_root_.GD.N0232.N0719.N0887.d003556 (1 : ℝ≥0) (-t * m)) := by
      have hprecisionU :
          _root_.GD.N0232.N0719.N0887.d003554 (1 : ℝ≥0) (-t * m) = d := by
        unfold _root_.GD.N0232.N0719.N0887.d003554 d _root_.GD.N0232.N0719.N0888.d003691
        simp
        ring
      have htiltU :=
        _root_.GD.N0232.N0719.N0887.d003567
          (v := (1 : ℝ≥0)) (a := -t * m) (b := 0)
          (fun u ↦
            ∫ z,
              _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z
              ∂_root_.GD.N0232.N0719.N0879.d003730
                (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
                s₁ s₂ s₃)
          one_ne_zero
          (by
            rw [hprecisionU]
            exact hrank)
      rw [show _root_.GD.N0232.N0719.N0887.d003557 (1 : ℝ≥0) (-t * m) 0 = 0 by
          simp [_root_.GD.N0232.N0719.N0887.d003557]] at htiltU
      have hnorm :
          _root_.GD.N0232.N0719.N0887.d003558 (1 : ℝ≥0) (-t * m) 0 =
            (Real.sqrt d)⁻¹ := by
        unfold _root_.GD.N0232.N0719.N0887.d003558
        rw [hprecisionU]
        simp
      have hinner :
          (∫ u,
              Real.exp (t * u ^ 2 * m) *
                (∫ z,
                  _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z
                  ∂_root_.GD.N0232.N0719.N0879.d003730
                    (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
                    s₁ s₂ s₃)
              ∂gaussianReal 0 1) =
            (Real.sqrt d)⁻¹ *
              ∫ u,
                (∫ z,
                  _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z
                  ∂_root_.GD.N0232.N0719.N0879.d003730
                    (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
                    s₁ s₂ s₃)
                ∂gaussianReal 0
                  (_root_.GD.N0232.N0719.N0887.d003556 (1 : ℝ≥0) (-t * m)) := by
        calc
          (∫ u,
              Real.exp (t * u ^ 2 * m) *
                (∫ z,
                  _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z
                  ∂_root_.GD.N0232.N0719.N0879.d003730
                    (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
                    s₁ s₂ s₃)
              ∂gaussianReal 0 1) =
              ∫ u,
                Real.exp (-(-t * m) * u ^ 2 + 0 * u) *
                  (∫ z,
                    _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z
                    ∂_root_.GD.N0232.N0719.N0879.d003730
                      (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
                      s₁ s₂ s₃)
                ∂gaussianReal 0 1 := by
            apply integral_congr_ae
            filter_upwards [] with u
            congr 1
            ring
          _ =
              _root_.GD.N0232.N0719.N0887.d003558 (1 : ℝ≥0) (-t * m) 0 *
                ∫ u,
                  (∫ z,
                    _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z
                    ∂_root_.GD.N0232.N0719.N0879.d003730
                      (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
                      s₁ s₂ s₃)
                  ∂gaussianReal 0
                    (_root_.GD.N0232.N0719.N0887.d003556 (1 : ℝ≥0) (-t * m)) := htiltU
          _ = _ := by rw [hnorm]
      rw [hinner]
      ring
    _ = _root_.GD.N0232.N0719.N0895.d003748 p₁ p₂ p₃ v₁ v₂ v₃ t *
          (Real.sqrt d)⁻¹ *
          (-_root_.GD.N0232.N0719.N0888.d003692 p₁ p₂ p₃ d₁ d₂ d₃ t) := by
      let ρ := _root_.GD.N0232.N0719.N0887.d003556 (1 : ℝ≥0) (-t * m)
      have hprecision :
          _root_.GD.N0232.N0719.N0887.d003554 (1 : ℝ≥0) (-t * m) = d := by
        unfold _root_.GD.N0232.N0719.N0887.d003554 d _root_.GD.N0232.N0719.N0888.d003691
        simp
        ring
      have hρ : (ρ : ℝ) = 1 / d := by
        dsimp [ρ]
        rw [_root_.GD.N0232.N0719.N0887.d003561 one_ne_zero (by
          rw [hprecision]
          exact hrank)]
        unfold _root_.GD.N0232.N0719.N0887.d003555
        rw [hprecision]
        simp
      have haffine :=
        _root_.GD.N0232.N0719.N0879.d003736
          (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
          (c := c) (s₁ := s₁) (s₂ := s₂) (s₃ := s₃)
          (ρ := ρ) hsum h₁₂ h₁₃ h₂₃
      rw [hsβ₁, hsβ₂, hsβ₃] at haffine
      dsimp [m, _root_.GD.N0232.N0719.N0888.d003690] at haffine
      have haffine' :
          (∫ u,
              (∫ z,
                _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z
                ∂_root_.GD.N0232.N0719.N0879.d003730
                  (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
                  s₁ s₂ s₃)
              ∂gaussianReal 0 ρ) =
            (1 + (ρ : ℝ) * c ^ 2 *
                (p₁ * β₁ + p₂ * β₂ + p₃ * β₃)) *
              (-_root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ β₁ β₂ β₃ +
                3 * (ρ : ℝ) * c ^ 2 *
                  _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ β₁ β₂ β₃) := by
        simpa only [_root_.GD.N0232.N0719.N0889.d003757] using haffine
      have hinner :
          (∫ u,
              (∫ z,
                _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z
                ∂_root_.GD.N0232.N0719.N0879.d003730
                  (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
                  s₁ s₂ s₃)
              ∂gaussianReal 0
                (_root_.GD.N0232.N0719.N0887.d003556 (1 : ℝ≥0) (-t * m))) =
            -_root_.GD.N0232.N0719.N0888.d003692 p₁ p₂ p₃ d₁ d₂ d₃ t := by
        change
          (∫ u,
              (∫ z,
                _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z
                ∂_root_.GD.N0232.N0719.N0879.d003730
                  (c * β₁ * u) (c * β₂ * u) (c * β₃ * u)
                  s₁ s₂ s₃)
              ∂gaussianReal 0 ρ) =
            -_root_.GD.N0232.N0719.N0888.d003692 p₁ p₂ p₃ d₁ d₂ d₃ t
        rw [haffine', hρ, hc_sq]
        let E := _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ β₁ β₂ β₃
        let C := _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ β₁ β₂ β₃
        change
          (1 + (1 / d) * (2 * t) * m) *
              (-E + 3 * (1 / d) * (2 * t) * C) =
            -((E * (1 - 2 * t * m) - 6 * t * C) / d ^ 2)
        have hdrel : d = 1 - 2 * t * m := by
          rfl
        have hden0 : 1 - 2 * t * m ≠ 0 := by
          rw [← hdrel]
          exact hrank.ne'
        rw [hdrel]
        field_simp [hden0]
        ring
      rw [hinner]
    _ = (Real.sqrt
          (_root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t))⁻¹ *
          (-_root_.GD.N0232.N0719.N0888.d003692 p₁ p₂ p₃ d₁ d₂ d₃ t) := by
      rw [_root_.GD.N0232.N0719.N0895.d003755
        hp₁.le hp₂.le hp₃.le hsum ht]
    _ = _root_.GD.N0232.N0719.N0889.d003768 p₁ p₂ p₃ d₁ d₂ d₃ t := by
      have hD :
          0 <
            _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t := by
        dsimp [d₁, d₂, d₃, _root_.GD.N0232.N0719.N0895.d003746]
        exact _root_.GD.N0232.N0719.N0892.d003681
          hp₁.le hp₂.le hp₃.le hsum
          (by positivity) (by positivity) (by positivity) ht
      have hcore :=
        have hd₁prec : 1 + 2 * t * d₁ ≠ 0 := by
          rw [← _root_.GD.N0232.N0719.N0895.d003749]
          exact hh₁.ne'
        have hd₂prec : 1 + 2 * t * d₂ ≠ 0 := by
          rw [← _root_.GD.N0232.N0719.N0895.d003749]
          exact hh₂.ne'
        have hd₃prec : 1 + 2 * t * d₃ ≠ 0 := by
          rw [← _root_.GD.N0232.N0719.N0895.d003749]
          exact hh₃.ne'
        _root_.GD.N0232.N0719.N0888.d003694
          (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
          (d₁ := d₁) (d₂ := d₂) (d₃ := d₃) (t := t)
          hsum h₁₂ h₁₃ h₂₃
          hd₁prec hd₂prec hd₃prec
          hrank.ne' hD.ne'
      rw [hcore]
      unfold _root_.GD.N0232.N0719.N0889.d003768
      field_simp [hD.ne', Real.sqrt_ne_zero'.mpr hD]


theorem d003770
    {p₁ p₂ p₃ t : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (ht : 0 ≤ t) :
    (∫ z,
        _root_.GD.N0232.N0719.N0889.d003758 p₁ p₂ p₃ t z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) ≤ 0 := by
  rw [_root_.GD.N0232.N0719.N0889.d003769
    hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ ht]
  unfold _root_.GD.N0232.N0719.N0889.d003768
  have hd₁ :
      0 ≤ _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁ := by
    unfold _root_.GD.N0232.N0719.N0895.d003746
    positivity
  have hd₂ :
      0 ≤ _root_.GD.N0232.N0719.N0895.d003746 p₂ v₂ := by
    unfold _root_.GD.N0232.N0719.N0895.d003746
    positivity
  have hd₃ :
      0 ≤ _root_.GD.N0232.N0719.N0895.d003746 p₃ v₃ := by
    unfold _root_.GD.N0232.N0719.N0895.d003746
    positivity
  have hD :=
    _root_.GD.N0232.N0719.N0892.d003681
      hp₁.le hp₂.le hp₃.le hsum
      hd₁ hd₂ hd₃ ht
  have hN :=
    _root_.GD.N0232.N0719.N0892.d003682
      hd₁ hd₂ hd₃
      (add_pos hp₁ hp₂) (add_pos hp₁ hp₃) (add_pos hp₂ hp₃) ht
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hN)
    (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))



theorem d003771
    {p₁ p₂ p₃ t : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (ht : 0 ≤ t) :
    (∫ z,
        _root_.GD.N0232.N0719.N0889.d003758 p₁ p₂ p₃ t z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) < 0 ↔
      ¬(_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁ = _root_.GD.N0232.N0719.N0895.d003746 p₂ v₂ ∧
        _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁ = _root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) := by
  rw [_root_.GD.N0232.N0719.N0889.d003769
    hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ ht]
  unfold _root_.GD.N0232.N0719.N0889.d003768
  let d₁ := _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁
  let d₂ := _root_.GD.N0232.N0719.N0895.d003746 p₂ v₂
  let d₃ := _root_.GD.N0232.N0719.N0895.d003746 p₃ v₃
  let D := _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t
  have hd₁ : 0 ≤ d₁ := by dsimp [d₁, _root_.GD.N0232.N0719.N0895.d003746]; positivity
  have hd₂ : 0 ≤ d₂ := by dsimp [d₂, _root_.GD.N0232.N0719.N0895.d003746]; positivity
  have hd₃ : 0 ≤ d₃ := by dsimp [d₃, _root_.GD.N0232.N0719.N0895.d003746]; positivity
  have hD : 0 < D :=
    _root_.GD.N0232.N0719.N0892.d003681 hp₁.le hp₂.le hp₃.le hsum
      hd₁ hd₂ hd₃ ht
  have hden :
      0 < D ^ 2 * Real.sqrt D :=
    mul_pos (sq_pos_of_pos hD) (Real.sqrt_pos.2 hD)
  change
    (-_root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t /
        (D ^ 2 * Real.sqrt D) < 0) ↔
      ¬(d₁ = d₂ ∧ d₁ = d₃)
  rw [div_neg_iff]
  simp only [hden, (not_lt_of_ge hden.le),
    and_false, false_or, and_true, neg_lt_zero]
  constructor
  · intro hnum hbalanced
    have hzero :
        _root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t = 0 :=
      (_root_.GD.N0232.N0719.N0892.d003683
        hd₁ hd₂ hd₃
        (add_pos hp₁ hp₂) (add_pos hp₁ hp₃) (add_pos hp₂ hp₃) ht).2
        hbalanced
    linarith
  · intro hmismatch
    exact
      _root_.GD.N0232.N0719.N0892.d003684
        hd₁ hd₂ hd₃
        (add_pos hp₁ hp₂) (add_pos hp₁ hp₃) (add_pos hp₂ hp₃) ht
        hmismatch

end

end GD.N0232.N0719.N0889
