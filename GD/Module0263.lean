import GD.Module0262
















namespace GD.N0232.N0719.N0890

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open _root_.GD.N0232.N0719.N1016
open _root_.GD.N0232.N0719.N0886
open _root_.GD.N0232.N0719.N0881
open _root_.GD.N0232.N0719.N0889
open _root_.GD.N0232.N0719.N0892
open _root_.GD.N0232.N0719.N0891
open _root_.GD.N0232.N0719.N0895


def d003772
    (p₁ p₂ p₃ τ : ℝ) (z : ℝ × (ℝ × ℝ)) : ℝ :=
  _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z /
    (τ + _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z.1 z.2.1 z.2.2)


def d003773
    (p₁ p₂ p₃ τ : ℝ)
    (zt : (ℝ × (ℝ × ℝ)) × ℝ) : ℝ :=
  Real.exp (-τ * zt.2) *
    _root_.GD.N0232.N0719.N0889.d003758 p₁ p₂ p₃ zt.2 zt.1

@[fun_prop]
theorem d003774
    {p₁ p₂ p₃ τ : ℝ}
    (hden :
      ∀ z : ℝ × (ℝ × ℝ),
        τ + _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z.1 z.2.1 z.2.2 ≠ 0) :
    Measurable (_root_.GD.N0232.N0719.N0890.d003772 p₁ p₂ p₃ τ) := by
  unfold _root_.GD.N0232.N0719.N0890.d003772
  apply Measurable.div
  · exact _root_.GD.N0232.N0719.N0889.d003760 _ _ _
  · unfold _root_.GD.N0232.N0719.N0881.d003572 _root_.GD.N0232.N0719.N0881.d003570
    fun_prop

@[fun_prop]
theorem d003775
    (p₁ p₂ p₃ τ : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0890.d003773 p₁ p₂ p₃ τ) := by
  unfold _root_.GD.N0232.N0719.N0890.d003773 _root_.GD.N0232.N0719.N0889.d003758
    _root_.GD.N0232.N0719.N0881.d003572 _root_.GD.N0232.N0719.N0881.d003570
  fun_prop

theorem d003776
    {p₁ p₂ p₃ τ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hτ : 0 < τ) (z : ℝ × (ℝ × ℝ)) :
    0 <
      τ + _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z.1 z.2.1 z.2.2 :=
  add_pos_of_pos_of_nonneg hτ
    (_root_.GD.N0232.N0719.N0889.d003762 hp₁ hp₂ hp₃)


theorem d003777
    {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, Real.exp (-t * a)) = a⁻¹ := by
  have h :=
    integral_exp_mul_Ioi (a := -a) (by linarith) 0
  simpa [mul_comm, one_div] using h

theorem d003778
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t * a)) (Ioi 0) := by
  simpa [mul_comm] using
    (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0)


theorem d003779
    {p₁ p₂ p₃ τ : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hτ : 0 < τ)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    Integrable (_root_.GD.N0232.N0719.N0890.d003772 p₁ p₂ p₃ τ)
      (_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) := by
  have hquartic :=
    _root_.GD.N0232.N0719.N0889.d003763
      (v₁ := v₁) (v₂ := v₂) (v₃ := v₃)
      h₁₂ h₁₃ h₂₃
  have hbound :
      Integrable
        (fun z : ℝ × (ℝ × ℝ) ↦
          τ⁻¹ * ‖_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z‖)
        (_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) :=
    hquartic.norm.const_mul τ⁻¹
  apply hbound.mono'
  · exact
      (_root_.GD.N0232.N0719.N0890.d003774
        (fun z ↦
          (_root_.GD.N0232.N0719.N0890.d003776 hp₁ hp₂ hp₃ hτ z).ne')).aestronglyMeasurable
  · filter_upwards [] with z
    have hQ :
        0 ≤ _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z.1 z.2.1 z.2.2 :=
      _root_.GD.N0232.N0719.N0889.d003762 hp₁ hp₂ hp₃
    have hden :
        0 <
          τ + _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z.1 z.2.1 z.2.2 :=
      add_pos_of_pos_of_nonneg hτ hQ
    rw [show
      ‖_root_.GD.N0232.N0719.N0890.d003772 p₁ p₂ p₃ τ z‖ =
        ‖_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z‖ /
          (τ + _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z.1 z.2.1 z.2.2) by
        simp [_root_.GD.N0232.N0719.N0890.d003772, abs_of_pos hden]]
    have hquot :
        ‖_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z‖ /
            (τ + _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
              z.1 z.2.1 z.2.2) ≤
          ‖_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z‖ / τ :=
      div_le_div_of_nonneg_left
        (norm_nonneg _) hτ (le_add_of_nonneg_right hQ)
    simpa [div_eq_inv_mul, mul_comm] using hquot




theorem d003780
    {p₁ p₂ p₃ τ : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hτ : 0 < τ)
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0) :
    Integrable (_root_.GD.N0232.N0719.N0890.d003773 p₁ p₂ p₃ τ)
      ((_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃).prod
        (volume.restrict (Ioi 0))) := by
  let μz := _root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃
  let μt : Measure ℝ := volume.restrict (Ioi 0)
  have hmeas :
      AEStronglyMeasurable
        (_root_.GD.N0232.N0719.N0890.d003773 p₁ p₂ p₃ τ)
        (μz.prod μt) :=
    (_root_.GD.N0232.N0719.N0890.d003775 p₁ p₂ p₃ τ).aestronglyMeasurable
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [] with z
    have hQ :
        0 ≤ _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z.1 z.2.1 z.2.2 :=
      _root_.GD.N0232.N0719.N0889.d003762 hp₁ hp₂ hp₃
    have hexp :=
      _root_.GD.N0232.N0719.N0890.d003778
        (add_pos_of_pos_of_nonneg hτ hQ)
    have hscaled :=
      hexp.const_mul (_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z)
    refine hscaled.congr ?_
    filter_upwards [] with t
    unfold _root_.GD.N0232.N0719.N0890.d003773 _root_.GD.N0232.N0719.N0889.d003758
    dsimp
    symm
    calc
      Real.exp (-τ * t) *
          (_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
            Real.exp
              (-t *
                _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                  z.1 z.2.1 z.2.2)) =
          _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
            (Real.exp (-τ * t) *
              Real.exp
                (-t *
                  _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                    z.1 z.2.1 z.2.2)) := by ring
      _ =
          _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
            Real.exp
              (-t *
                (τ +
                  _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                    z.1 z.2.1 z.2.2)) := by
            rw [← Real.exp_add]
            congr 2
            ring
  · have hres :=
      _root_.GD.N0232.N0719.N0890.d003779
        (v₁ := v₁) (v₂ := v₂) (v₃ := v₃)
        hp₁ hp₂ hp₃ hτ h₁₂ h₁₃ h₂₃
    have hresnorm := hres.norm
    convert hresnorm using 1
    funext z
    have hQ :
        0 ≤ _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z.1 z.2.1 z.2.2 :=
      _root_.GD.N0232.N0719.N0889.d003762 hp₁ hp₂ hp₃
    have hden :
        0 <
          τ + _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃ z.1 z.2.1 z.2.2 :=
      add_pos_of_pos_of_nonneg hτ hQ
    have hexp :=
      _root_.GD.N0232.N0719.N0890.d003777 hden
    rw [show
      (∫ t, ‖_root_.GD.N0232.N0719.N0890.d003773 p₁ p₂ p₃ τ (z, t)‖ ∂μt) =
        ‖_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z‖ *
          (∫ t : ℝ in Ioi 0,
            Real.exp
              (-t *
                (τ +
                  _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                    z.1 z.2.1 z.2.2))) by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        unfold _root_.GD.N0232.N0719.N0890.d003773 _root_.GD.N0232.N0719.N0889.d003758
        simp only [norm_mul, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        calc
          Real.exp (-τ * t) *
              (|_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z| *
                Real.exp
                  (-t *
                    _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                      z.1 z.2.1 z.2.2)) =
              |_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z| *
                (Real.exp (-τ * t) *
                  Real.exp
                    (-t *
                      _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                        z.1 z.2.1 z.2.2)) := by ring
          _ =
              |_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z| *
                Real.exp
                  (-t *
                    (τ +
                      _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                        z.1 z.2.1 z.2.2)) := by
                rw [← Real.exp_add]
                congr 2
                ring]
    rw [hexp]
    simp [_root_.GD.N0232.N0719.N0890.d003772, abs_of_pos hden,
      div_eq_mul_inv]




theorem d003781
    {p₁ p₂ p₃ τ : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (hτ : 0 < τ) :
    (∫ z,
        _root_.GD.N0232.N0719.N0890.d003772 p₁ p₂ p₃ τ z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) =
      ∫ t : ℝ in Ioi 0,
        Real.exp (-τ * t) *
          _root_.GD.N0232.N0719.N0889.d003768 p₁ p₂ p₃
            (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
            (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
            (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t := by
  have h₁₂ : p₁ + p₂ ≠ 0 := ne_of_gt (add_pos hp₁ hp₂)
  have h₁₃ : p₁ + p₃ ≠ 0 := ne_of_gt (add_pos hp₁ hp₃)
  have h₂₃ : p₂ + p₃ ≠ 0 := ne_of_gt (add_pos hp₂ hp₃)
  have hjoint :=
    _root_.GD.N0232.N0719.N0890.d003780
      (v₁ := v₁) (v₂ := v₂) (v₃ := v₃)
      hp₁.le hp₂.le hp₃.le hτ h₁₂ h₁₃ h₂₃
  letI : SFinite (_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) := by
    unfold _root_.GD.N0232.N0719.N0886.d003649
    infer_instance
  calc
    (∫ z,
        _root_.GD.N0232.N0719.N0890.d003772 p₁ p₂ p₃ τ z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) =
        ∫ z,
          (∫ t : ℝ in Ioi 0,
            _root_.GD.N0232.N0719.N0890.d003773 p₁ p₂ p₃ τ (z, t))
          ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃ := by
      apply integral_congr_ae
      filter_upwards [] with z
      have hQ :
          0 ≤ _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
            z.1 z.2.1 z.2.2 :=
        _root_.GD.N0232.N0719.N0889.d003762 hp₁.le hp₂.le hp₃.le
      have hden :
          0 <
            τ + _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
              z.1 z.2.1 z.2.2 :=
        add_pos_of_pos_of_nonneg hτ hQ
      rw [show
        (∫ t : ℝ in Ioi 0,
          _root_.GD.N0232.N0719.N0890.d003773 p₁ p₂ p₃ τ (z, t)) =
            _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
              (∫ t : ℝ in Ioi 0,
                Real.exp
                  (-t *
                    (τ +
                      _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                        z.1 z.2.1 z.2.2))) by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with t
          unfold _root_.GD.N0232.N0719.N0890.d003773 _root_.GD.N0232.N0719.N0889.d003758
          dsimp
          calc
            Real.exp (-τ * t) *
                (_root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
                  Real.exp
                    (-t *
                      _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                        z.1 z.2.1 z.2.2)) =
                _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
                  (Real.exp (-τ * t) *
                    Real.exp
                      (-t *
                        _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                          z.1 z.2.1 z.2.2)) := by ring
            _ =
                _root_.GD.N0232.N0719.N0889.d003757 p₁ p₂ p₃ z *
                  Real.exp
                    (-t *
                      (τ +
                        _root_.GD.N0232.N0719.N0881.d003572 p₁ p₂ p₃
                          z.1 z.2.1 z.2.2)) := by
                  rw [← Real.exp_add]
                  congr 2
                  ring]
      rw [_root_.GD.N0232.N0719.N0890.d003777 hden]
      unfold _root_.GD.N0232.N0719.N0890.d003772
      ring
    _ = ∫ t : ℝ in Ioi 0, ∫ z,
          _root_.GD.N0232.N0719.N0890.d003773 p₁ p₂ p₃ τ (z, t)
            ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃ := by
      exact integral_integral_swap hjoint
    _ = ∫ t : ℝ in Ioi 0,
        Real.exp (-τ * t) *
          _root_.GD.N0232.N0719.N0889.d003768 p₁ p₂ p₃
            (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
            (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
            (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t := by
      apply integral_congr_ae
      apply (ae_restrict_iff' measurableSet_Ioi).2
      filter_upwards [] with t ht
      have ht0 : 0 ≤ t := le_of_lt ht
      unfold _root_.GD.N0232.N0719.N0890.d003773
      change
        (∫ z,
          Real.exp (-τ * t) *
            _root_.GD.N0232.N0719.N0889.d003758 p₁ p₂ p₃ t z
          ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) =
          Real.exp (-τ * t) *
            _root_.GD.N0232.N0719.N0889.d003768 p₁ p₂ p₃
              (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
              (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
              (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t
      rw [integral_const_mul,
        _root_.GD.N0232.N0719.N0889.d003769
          hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ ht0]


theorem d003782
    {p₁ p₂ p₃ τ : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (hτ : 0 < τ) :
    Integrable
      (fun t : ℝ ↦
        Real.exp (-τ * t) *
          _root_.GD.N0232.N0719.N0891.d003705 p₁ p₂ p₃
            (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
            (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
            (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t)
      (volume.restrict (Ioi 0)) := by
  have h₁₂ : p₁ + p₂ ≠ 0 := ne_of_gt (add_pos hp₁ hp₂)
  have h₁₃ : p₁ + p₃ ≠ 0 := ne_of_gt (add_pos hp₁ hp₃)
  have h₂₃ : p₂ + p₃ ≠ 0 := ne_of_gt (add_pos hp₂ hp₃)
  have hjoint :=
    _root_.GD.N0232.N0719.N0890.d003780
      (v₁ := v₁) (v₂ := v₂) (v₃ := v₃)
      hp₁.le hp₂.le hp₃.le hτ h₁₂ h₁₃ h₂₃
  letI : SFinite (_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) := by
    unfold _root_.GD.N0232.N0719.N0886.d003649
    infer_instance
  have houter := hjoint.integral_prod_right
  have hsigned :
      Integrable
        (fun t : ℝ ↦
          Real.exp (-τ * t) *
            _root_.GD.N0232.N0719.N0889.d003768 p₁ p₂ p₃
              (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
              (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
              (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t)
        (volume.restrict (Ioi 0)) := by
    apply houter.congr
    apply (ae_restrict_iff' measurableSet_Ioi).2
    filter_upwards [] with t ht
    unfold _root_.GD.N0232.N0719.N0890.d003773
    change
      (∫ z,
        Real.exp (-τ * t) *
          _root_.GD.N0232.N0719.N0889.d003758 p₁ p₂ p₃ t z
        ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) =
        Real.exp (-τ * t) *
          _root_.GD.N0232.N0719.N0889.d003768 p₁ p₂ p₃
            (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
            (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
            (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t
    rw [integral_const_mul,
      _root_.GD.N0232.N0719.N0889.d003769
        hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ (le_of_lt ht)]
  have hneg := hsigned.neg
  refine hneg.congr ?_
  filter_upwards [] with t
  change
    -(Real.exp (-τ * t) *
      _root_.GD.N0232.N0719.N0889.d003768 p₁ p₂ p₃
        (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
        (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
        (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t) =
      Real.exp (-τ * t) *
        _root_.GD.N0232.N0719.N0891.d003705 p₁ p₂ p₃
          (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
          (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
          (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) t
  unfold _root_.GD.N0232.N0719.N0889.d003768 _root_.GD.N0232.N0719.N0891.d003705
  ring


theorem d003783
    {p₁ p₂ p₃ t τ d₁ d₂ d₃ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃)
    (ht : 0 ≤ t) :
    0 ≤
      Real.exp (-τ * t) *
        _root_.GD.N0232.N0719.N0891.d003705 p₁ p₂ p₃ d₁ d₂ d₃ t := by
  have hD :
      0 <
        _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t :=
    _root_.GD.N0232.N0719.N0892.d003681 hp₁ hp₂ hp₃ hsum
      hd₁ hd₂ hd₃ ht
  have hN :
      0 ≤ _root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t :=
    _root_.GD.N0232.N0719.N0892.d003682
      hd₁ hd₂ hd₃ h₁₂ h₁₃ h₂₃ ht
  apply mul_nonneg (Real.exp_pos _).le
  unfold _root_.GD.N0232.N0719.N0891.d003705
  exact div_nonneg hN
    (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))






theorem d003784
    {p₁ p₂ p₃ τ V : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (hτ : 0 < τ) (hV : 0 < V)
    (hv₁V : (v₁ : ℝ) ≤ V)
    (hv₂V : (v₂ : ℝ) ≤ V)
    (hv₃V : (v₃ : ℝ) ≤ V) :
    (∫ z,
        _root_.GD.N0232.N0719.N0890.d003772 p₁ p₂ p₃ τ z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) ≤
      -(3 / 128 : ℝ) *
        _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃
          (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
          (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
          (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) / (τ + V) := by
  let d₁ := _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁
  let d₂ := _root_.GD.N0232.N0719.N0895.d003746 p₂ v₂
  let d₃ := _root_.GD.N0232.N0719.N0895.d003746 p₃ v₃
  let T := 1 / (4 * (τ + V))
  let C := (3 / 32 : ℝ) * _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃
  let f : ℝ → ℝ := fun t ↦
    Real.exp (-τ * t) *
      _root_.GD.N0232.N0719.N0891.d003705 p₁ p₂ p₃ d₁ d₂ d₃ t
  have hτV : 0 < τ + V := add_pos hτ hV
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hd₁ : 0 ≤ d₁ := by
    dsimp [d₁, _root_.GD.N0232.N0719.N0895.d003746]
    positivity
  have hd₂ : 0 ≤ d₂ := by
    dsimp [d₂, _root_.GD.N0232.N0719.N0895.d003746]
    positivity
  have hd₃ : 0 ≤ d₃ := by
    dsimp [d₃, _root_.GD.N0232.N0719.N0895.d003746]
    positivity
  have hfInt :
      Integrable f (volume.restrict (Ioi 0)) := by
    dsimp [f, d₁, d₂, d₃]
    exact
      _root_.GD.N0232.N0719.N0890.d003782
        hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ hτ
  have hfNonneg :
      0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    apply (ae_restrict_iff' measurableSet_Ioi).2
    filter_upwards [] with t ht
    exact
      _root_.GD.N0232.N0719.N0890.d003783
        hp₁.le hp₂.le hp₃.le hsum
        hd₁ hd₂ hd₃
        (add_pos hp₁ hp₂) (add_pos hp₁ hp₃) (add_pos hp₂ hp₃)
        (le_of_lt ht)
  have hsubset : Ioc (0 : ℝ) T ⊆ Ioi 0 := by
    intro t ht
    exact ht.1
  have hfLocal :
      IntegrableOn f (Ioc (0 : ℝ) T) :=
    hfInt.mono_measure
      (Measure.restrict_mono hsubset le_rfl)
  have hpoint :
      ∀ t ∈ Ioc (0 : ℝ) T, C ≤ f t := by
    intro t ht
    have hkernel :=
      _root_.GD.N0232.N0719.N0891.d003708
        hp₁.le hp₂.le hp₃.le hsum
        (show 0 ≤ (v₁ : ℝ) by positivity)
        (show 0 ≤ (v₂ : ℝ) by positivity)
        (show 0 ≤ (v₃ : ℝ) by positivity)
        hv₁V hv₂V hv₃V hV hτ.le
        (le_of_lt ht.1) ht.2
        (add_pos hp₁ hp₂) (add_pos hp₁ hp₃) (add_pos hp₂ hp₃)
    simpa [C, f, d₁, d₂, d₃, _root_.GD.N0232.N0719.N0895.d003746, _root_.GD.N0232.N0719.N0891.d003696,
      mul_comm] using
      hkernel
  have hlocal :
      C * T ≤ ∫ t in Ioc (0 : ℝ) T, f t := by
    have hraw :=
      setIntegral_ge_of_const_le
        (μ := volume) (f := f) (c := C)
        measurableSet_Ioc
        (by simp [Real.volume_Ioc])
        hpoint hfLocal
    simpa [Real.volume_Ioc, hT.le, smul_eq_mul, mul_comm] using hraw
  have hglobal :
      (∫ t in Ioc (0 : ℝ) T, f t) ≤
        ∫ t in Ioi 0, f t := by
    exact
      setIntegral_mono_set hfInt hfNonneg
        (Filter.Eventually.of_forall fun t ht ↦ hsubset ht)
  have hpositive :
      C * T ≤ ∫ t in Ioi 0, f t :=
    hlocal.trans hglobal
  have hcross :
      (∫ z,
          _root_.GD.N0232.N0719.N0890.d003772 p₁ p₂ p₃ τ z
        ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) =
        -(∫ t in Ioi 0, f t) := by
    rw [_root_.GD.N0232.N0719.N0890.d003781
      hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ hτ]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [f, d₁, d₂, d₃]
    unfold _root_.GD.N0232.N0719.N0889.d003768 _root_.GD.N0232.N0719.N0891.d003705
    ring
  have hCT :
      C * T =
        (3 / 128 : ℝ) *
          _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ / (τ + V) := by
    dsimp [C, T]
    field_simp [hτV.ne']
    ring
  rw [hcross]
  rw [hCT] at hpositive
  dsimp [d₁, d₂, d₃] at hpositive
  calc
    -(∫ t in Ioi 0, f t) ≤
        -((3 / 128 : ℝ) *
          _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃
            (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
            (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
            (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) / (τ + V)) :=
      neg_le_neg hpositive
    _ =
        -(3 / 128 : ℝ) *
          _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃
            (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
            (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
            (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) / (τ + V) := by
      ring



theorem d003785
    {p₁ p₂ p₃ τ V : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (hτ : 0 < τ) (hV : 0 < V)
    (hv₁V : (v₁ : ℝ) ≤ V)
    (hv₂V : (v₂ : ℝ) ≤ V)
    (hv₃V : (v₃ : ℝ) ≤ V)
    (hA0 :
      0 <
        _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃
          (_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁)
          (_root_.GD.N0232.N0719.N0895.d003746 p₂ v₂)
          (_root_.GD.N0232.N0719.N0895.d003746 p₃ v₃)) :
    (∫ z,
        _root_.GD.N0232.N0719.N0890.d003772 p₁ p₂ p₃ τ z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) < 0 := by
  have hbound :=
    _root_.GD.N0232.N0719.N0890.d003784
      hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ hτ hV
      hv₁V hv₂V hv₃V
  have hτV : 0 < τ + V := add_pos hτ hV
  exact hbound.trans_lt (by
    apply div_neg_of_neg_of_pos
    · exact mul_neg_of_neg_of_pos (by norm_num) hA0
    · exact hτV)



theorem d003786
    {p₁ p₂ p₃ τ : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (hτ : 0 < τ)
    (hbalanced :
      _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁ = _root_.GD.N0232.N0719.N0895.d003746 p₂ v₂ ∧
        _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁ = _root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) :
    (∫ z,
        _root_.GD.N0232.N0719.N0890.d003772 p₁ p₂ p₃ τ z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) = 0 := by
  rw [_root_.GD.N0232.N0719.N0890.d003781
    hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ hτ]
  apply integral_eq_zero_of_ae
  apply (ae_restrict_iff' measurableSet_Ioi).2
  filter_upwards [] with t ht
  let d₁ := _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁
  let d₂ := _root_.GD.N0232.N0719.N0895.d003746 p₂ v₂
  let d₃ := _root_.GD.N0232.N0719.N0895.d003746 p₃ v₃
  have hd₁ : 0 ≤ d₁ := by
    dsimp [d₁, _root_.GD.N0232.N0719.N0895.d003746]
    positivity
  have hd₂ : 0 ≤ d₂ := by
    dsimp [d₂, _root_.GD.N0232.N0719.N0895.d003746]
    positivity
  have hd₃ : 0 ≤ d₃ := by
    dsimp [d₃, _root_.GD.N0232.N0719.N0895.d003746]
    positivity
  have hnum :
      _root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t = 0 :=
    (_root_.GD.N0232.N0719.N0892.d003683
      hd₁ hd₂ hd₃
      (add_pos hp₁ hp₂) (add_pos hp₁ hp₃)
      (add_pos hp₂ hp₃) (le_of_lt ht)).2 hbalanced
  change
    Real.exp (-τ * t) *
      _root_.GD.N0232.N0719.N0889.d003768 p₁ p₂ p₃ d₁ d₂ d₃ t = 0
  unfold _root_.GD.N0232.N0719.N0889.d003768
  rw [hnum]
  simp









theorem d003787
    {p₁ p₂ p₃ τ : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (hτ : 0 < τ) :
    (∫ z,
        _root_.GD.N0232.N0719.N0890.d003772 p₁ p₂ p₃ τ z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) < 0 ↔
      ¬(_root_.GD.N0232.N0719.N0895.d003746 p₁ v₁ = _root_.GD.N0232.N0719.N0895.d003746 p₂ v₂ ∧
        _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁ = _root_.GD.N0232.N0719.N0895.d003746 p₃ v₃) := by
  let d₁ := _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁
  let d₂ := _root_.GD.N0232.N0719.N0895.d003746 p₂ v₂
  let d₃ := _root_.GD.N0232.N0719.N0895.d003746 p₃ v₃
  let V : ℝ := (v₁ : ℝ) + (v₂ : ℝ) + (v₃ : ℝ)
  have hv₁pos : 0 < (v₁ : ℝ) := by
    exact_mod_cast (pos_of_ne_zero hv₁)
  have hv₂nonneg : 0 ≤ (v₂ : ℝ) := by positivity
  have hv₃nonneg : 0 ≤ (v₃ : ℝ) := by positivity
  have hV : 0 < V := by
    dsimp [V]
    linarith
  have hv₁V : (v₁ : ℝ) ≤ V := by
    dsimp [V]
    linarith
  have hv₂V : (v₂ : ℝ) ≤ V := by
    have hv₁nonneg : 0 ≤ (v₁ : ℝ) := by positivity
    dsimp [V]
    linarith
  have hv₃V : (v₃ : ℝ) ≤ V := by
    have hv₁nonneg : 0 ≤ (v₁ : ℝ) := by positivity
    dsimp [V]
    linarith
  constructor
  · intro hneg hbalanced
    have hzero := _root_.GD.N0232.N0719.N0890.d003786
      hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ hτ hbalanced
    linarith
  · intro hmismatch
    have hd₁ : 0 ≤ d₁ := by
      dsimp [d₁, _root_.GD.N0232.N0719.N0895.d003746]
      positivity
    have hd₂ : 0 ≤ d₂ := by
      dsimp [d₂, _root_.GD.N0232.N0719.N0895.d003746]
      positivity
    have hd₃ : 0 ≤ d₃ := by
      dsimp [d₃, _root_.GD.N0232.N0719.N0895.d003746]
      positivity
    have hA0nonneg : 0 ≤ _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ :=
      _root_.GD.N0232.N0719.N0892.d003674
        (add_pos hp₁ hp₂) (add_pos hp₁ hp₃) (add_pos hp₂ hp₃)
    have hA0ne : _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ ≠ 0 := by
      intro hzero
      exact hmismatch
        ((_root_.GD.N0232.N0719.N0892.d003675
          (add_pos hp₁ hp₂) (add_pos hp₁ hp₃)
          (add_pos hp₂ hp₃)).1 hzero)
    have hA0 : 0 < _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ :=
      lt_of_le_of_ne hA0nonneg (Ne.symm hA0ne)
    exact _root_.GD.N0232.N0719.N0890.d003785
      hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ hτ hV
      hv₁V hv₂V hv₃V hA0





theorem d003788
    {p₁ p₂ p₃ τ : ℝ} {v₁ v₂ v₃ : ℝ≥0}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hp₃ : 0 < p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (hτ : 0 < τ) :
    (∫ z,
        _root_.GD.N0232.N0719.N0890.d003772 p₁ p₂ p₃ τ z
      ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃) = 0 ↔
      _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁ = _root_.GD.N0232.N0719.N0895.d003746 p₂ v₂ ∧
        _root_.GD.N0232.N0719.N0895.d003746 p₁ v₁ = _root_.GD.N0232.N0719.N0895.d003746 p₃ v₃ := by
  let I :=
    ∫ z,
      _root_.GD.N0232.N0719.N0890.d003772 p₁ p₂ p₃ τ z
    ∂_root_.GD.N0232.N0719.N0886.d003649 v₁ v₂ v₃
  have hstrict :=
    _root_.GD.N0232.N0719.N0890.d003787
      hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ hτ
  constructor
  · intro hzero
    by_contra hnot
    have hneg : I < 0 := hstrict.2 hnot
    dsimp [I] at hneg
    linarith
  · intro hbalanced
    exact _root_.GD.N0232.N0719.N0890.d003786
      hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ hτ hbalanced

end

end GD.N0232.N0719.N0890
