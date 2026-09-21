import Mathlib















open MeasureTheory Filter
open scoped ENNReal Topology

namespace GD.N0232.N0720.N1242

noncomputable section

def d002130 (t u : ℝ) : ℝ := t * (1-u) + (1-t) * u

def d002131 (t h u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((h-t)^2 / _root_.GD.N0232.N0720.N1242.d002130 t u)

theorem d002132 {t u : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1)
    (hu : u ∈ Set.Ioo (0:ℝ) 1) : 0 < _root_.GD.N0232.N0720.N1242.d002130 t u := by
  exact add_pos (mul_pos ht.1 (sub_pos.mpr hu.2))
    (mul_pos (sub_pos.mpr ht.2) hu.1)

theorem d002133 {t u : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1)
    (hu : u ∈ Set.Ioo (0:ℝ) 1) : _root_.GD.N0232.N0720.N1242.d002131 t u u ≤ 1 := by
  have hd := _root_.GD.N0232.N0720.N1242.d002132 ht hu
  apply ENNReal.ofReal_le_one.mpr
  apply (div_le_one hd).mpr
  dsimp [_root_.GD.N0232.N0720.N1242.d002130] at *
  nlinarith [mul_nonneg hu.1.le (sub_pos.mpr hu.2).le,
    mul_nonneg ht.1.le (sub_pos.mpr ht.2).le]

theorem d002134 (t h u : ℝ) :
    _root_.GD.N0232.N0720.N1242.d002131 t (1-h) (1-u) = _root_.GD.N0232.N0720.N1242.d002131 (1-t) h u := by
  unfold _root_.GD.N0232.N0720.N1242.d002131 _root_.GD.N0232.N0720.N1242.d002130
  congr 1
  congr 1 <;> ring

private theorem d002135 {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (h u : ℝ) (hu : 0 < u) :
    Tendsto (fun n => _root_.GD.N0232.N0720.N1242.d002131 (t n) h u) atTop
      (𝓝 (ENNReal.ofReal (h^2/u))) := by
  have hd : Tendsto (fun n => _root_.GD.N0232.N0720.N1242.d002130 (t n) u) atTop (𝓝 u) := by
    simpa [_root_.GD.N0232.N0720.N1242.d002130] using
      (ht.mul_const (1-u)).add (((tendsto_const_nhds (x := (1:ℝ))).sub ht).mul_const u)
  have hn : Tendsto (fun n => (h-t n)^2) atTop (𝓝 (h^2)) := by
    simpa using (tendsto_const_nhds.sub ht).pow 2
  exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (hn.div hd hu.ne')

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ] {u H : Ω → ℝ}


theorem d002136 (hu : Measurable u) (hH : Measurable H)
    (hunit : ∀ᵐ x ∂μ, u x ∈ Set.Ioo (0:ℝ) 1)
    (hdom : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      (∫⁻ x, _root_.GD.N0232.N0720.N1242.d002131 t (H x) (u x) ∂μ) ≤ ∫⁻ x, _root_.GD.N0232.N0720.N1242.d002131 t (u x) (u x) ∂μ) :
    (∫⁻ x, ENNReal.ofReal ((H x)^2 / u x) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (u x) ∂μ := by
  let t : ℕ → ℝ := fun n => 1 / ((n:ℝ)+2)
  have htunit (n : ℕ) : t n ∈ Set.Ioo (0:ℝ) 1 := by
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    dsimp [t]
    constructor
    · positivity
    · exact (div_lt_one (by positivity)).mpr (by linarith)
  have ht : Tendsto t atTop (𝓝 0) := by
    simpa [t, Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_add_atTop_iff_nat 2).mpr
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmeas (n : ℕ) : Measurable (fun x => _root_.GD.N0232.N0720.N1242.d002131 (t n) (H x) (u x)) := by
    unfold _root_.GD.N0232.N0720.N1242.d002131 _root_.GD.N0232.N0720.N1242.d002130
    fun_prop
  have hbase (n : ℕ) : Measurable (fun x => _root_.GD.N0232.N0720.N1242.d002131 (t n) (u x) (u x)) := by
    unfold _root_.GD.N0232.N0720.N1242.d002131 _root_.GD.N0232.N0720.N1242.d002130
    fun_prop
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => _root_.GD.N0232.N0720.N1242.d002131 (t n) (H x) (u x)) atTop
      (𝓝 (ENNReal.ofReal ((H x)^2/u x))) := by
    filter_upwards [hunit] with x hx
    exact _root_.GD.N0232.N0720.N1242.d002135 ht (H x) (u x) hx.1
  have hbaselim : Tendsto (fun n => ∫⁻ x, _root_.GD.N0232.N0720.N1242.d002131 (t n) (u x) (u x) ∂μ)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (u x) ∂μ)) := by
    apply tendsto_lintegral_of_dominated_convergence (fun _ => 1) hbase
    · intro n
      filter_upwards [hunit] with x hx
      exact _root_.GD.N0232.N0720.N1242.d002133 (htunit n) hx
    · simp
    · filter_upwards [hunit] with x hx
      simpa [pow_two, mul_div_cancel_right₀ _ hx.1.ne'] using
        _root_.GD.N0232.N0720.N1242.d002135 ht (u x) (u x) hx.1
  calc
    _ = ∫⁻ x, liminf (fun n => _root_.GD.N0232.N0720.N1242.d002131 (t n) (H x) (u x)) atTop ∂μ :=
      lintegral_congr_ae (hlim.mono fun _ hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ x, _root_.GD.N0232.N0720.N1242.d002131 (t n) (H x) (u x) ∂μ) atTop :=
      lintegral_liminf_le hmeas
    _ ≤ liminf (fun n => ∫⁻ x, _root_.GD.N0232.N0720.N1242.d002131 (t n) (u x) (u x) ∂μ) atTop :=
      liminf_le_liminf (Eventually.of_forall fun n => hdom (t n) (htunit n))
    _ = _ := hbaselim.liminf_eq

theorem d002137 (h u : ℝ) (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    h^2/u + (1-h)^2/(1-u) = 1 + (h-u)^2/(u*(1-u)) := by
  field_simp [hu.1.ne', (sub_pos.mpr hu.2).ne']
  ring




theorem d002138 (hu : Measurable u) (hH : Measurable H)
    (hunit : ∀ᵐ x ∂μ, u x ∈ Set.Ioo (0:ℝ) 1)
    (hdom : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      (∫⁻ x, _root_.GD.N0232.N0720.N1242.d002131 t (H x) (u x) ∂μ) ≤ ∫⁻ x, _root_.GD.N0232.N0720.N1242.d002131 t (u x) (u x) ∂μ) :
    H =ᵐ[μ] u := by
  have h0 := _root_.GD.N0232.N0720.N1242.d002136 hu hH hunit hdom
  have h1 := _root_.GD.N0232.N0720.N1242.d002136 (measurable_const.sub hu) (measurable_const.sub hH)
    (show ∀ᵐ x ∂μ, 1-u x ∈ Set.Ioo (0:ℝ) 1 from
      hunit.mono fun _ hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    (show ∀ t ∈ Set.Ioo (0:ℝ) 1,
        (∫⁻ x, _root_.GD.N0232.N0720.N1242.d002131 t (1-H x) (1-u x) ∂μ) ≤
          ∫⁻ x, _root_.GD.N0232.N0720.N1242.d002131 t (1-u x) (1-u x) ∂μ from by
      intro t ht
      simp_rw [_root_.GD.N0232.N0720.N1242.d002134]
      exact hdom (1-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  let penalty : Ω → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((H x-u x)^2/(u x*(1-u x)))
  have hpmeas : Measurable penalty := by
    dsimp [penalty]
    fun_prop
  have hsum : (∫⁻ x, ENNReal.ofReal ((H x)^2/u x) ∂μ) +
        (∫⁻ x, ENNReal.ofReal ((1-H x)^2/(1-u x)) ∂μ) =
      μ Set.univ + ∫⁻ x, penalty x ∂μ := by
    rw [← lintegral_add_left (by fun_prop)]
    calc
      _ = ∫⁻ x, 1 + penalty x ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hunit] with x hx
        rw [← ENNReal.ofReal_add (div_nonneg (sq_nonneg _) hx.1.le)
          (div_nonneg (sq_nonneg _) (sub_pos.mpr hx.2).le),
          _root_.GD.N0232.N0720.N1242.d002137 (H x) (u x) hx]
        rw [ENNReal.ofReal_add (by norm_num)
          (div_nonneg (sq_nonneg _) (mul_pos hx.1 (sub_pos.mpr hx.2)).le)]
        simp [penalty]
      _ = _ := by rw [lintegral_add_left measurable_const]; simp
  have hrhs : (∫⁻ x, ENNReal.ofReal (u x) ∂μ) +
      (∫⁻ x, ENNReal.ofReal (1-u x) ∂μ) = μ Set.univ := by
    rw [← lintegral_add_left (by fun_prop)]
    calc
      _ = ∫⁻ _ : Ω, (1:ℝ≥0∞) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hunit] with x hx
        rw [← ENNReal.ofReal_add hx.1.le (sub_pos.mpr hx.2).le]
        simp
      _ = _ := by simp
  have hpzero : ∫⁻ x, penalty x ∂μ = 0 := by
    apply le_antisymm _ bot_le
    apply ENNReal.le_of_add_le_add_left (measure_ne_top μ Set.univ)
    simpa only [bot_eq_zero, add_zero, hsum, hrhs] using add_le_add h0 h1
  have hpae : penalty =ᵐ[μ] 0 := (lintegral_eq_zero_iff hpmeas).mp hpzero
  filter_upwards [hunit, hpae] with x hx hpx
  have hd : 0 < u x*(1-u x) := mul_pos hx.1 (sub_pos.mpr hx.2)
  have hz : (H x-u x)^2/(u x*(1-u x)) ≤ 0 := by
    exact ENNReal.ofReal_eq_zero.mp hpx
  have : (H x-u x)^2 ≤ 0 := by simpa using (div_le_iff₀ hd).mp hz
  nlinarith [sq_nonneg (H x-u x)]


def d002139 : Measure ℝ := ProbabilityTheory.betaMeasure (1/2) (1/2)

theorem d002140 : IsProbabilityMeasure _root_.GD.N0232.N0720.N1242.d002139 :=
  ProbabilityTheory.isProbabilityMeasureBeta (by norm_num) (by norm_num)

theorem d002141 : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1242.d002139, x ∈ Set.Ioo (0:ℝ) 1 := by
  unfold _root_.GD.N0232.N0720.N1242.d002139 ProbabilityTheory.betaMeasure
  apply (ae_withDensity_iff
    ((ProbabilityTheory.measurable_betaPDFReal (1/2) (1/2)).ennreal_ofReal)).mpr
  filter_upwards [] with x hx
  by_contra hn
  apply hx
  have hn' : ¬ (0 < x ∧ x < 1) := hn
  simp only [ProbabilityTheory.betaPDFReal, if_neg hn', ENNReal.ofReal_zero]

theorem d002142 {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    ProbabilityTheory.betaPDFReal (1/2) (1/2) x =
      1 / (Real.pi * Real.sqrt (x*(1-x))) := by
  have hb : ProbabilityTheory.beta (1/2) (1/2) = Real.pi := by
    norm_num [ProbabilityTheory.beta, Real.Gamma_one_half_eq,
      Real.mul_self_sqrt Real.pi_pos.le]
  rw [ProbabilityTheory.betaPDFReal, if_pos (show 0 < x ∧ x < 1 from hx), hb]
  norm_num only
  rw [Real.rpow_neg hx.1.le, Real.rpow_neg (sub_pos.mpr hx.2).le,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul hx.1.le]
  ring


def d002143 (t : ℝ) : Measure ℝ :=
  _root_.GD.N0232.N0720.N1242.d002139.withDensity (fun x =>
    ENNReal.ofReal (Real.sqrt (t*(1-t)) / _root_.GD.N0232.N0720.N1242.d002130 t x))

def d002144 (t : ℝ) (H : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((H x-t)^2) ∂_root_.GD.N0232.N0720.N1242.d002143 t

theorem d002145 (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1)
    (H : ℝ → ℝ) (hH : Measurable H) :
    _root_.GD.N0232.N0720.N1242.d002144 t H = ENNReal.ofReal (Real.sqrt (t*(1-t))) *
      ∫⁻ x, _root_.GD.N0232.N0720.N1242.d002131 t (H x) x ∂_root_.GD.N0232.N0720.N1242.d002139 := by
  unfold _root_.GD.N0232.N0720.N1242.d002144 _root_.GD.N0232.N0720.N1242.d002143
  rw [lintegral_withDensity_eq_lintegral_mul _ (by unfold _root_.GD.N0232.N0720.N1242.d002130; fun_prop)
    (by fun_prop), ← lintegral_const_mul _ (by unfold _root_.GD.N0232.N0720.N1242.d002131 _root_.GD.N0232.N0720.N1242.d002130; fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1242.d002141] with x hx
  change ENNReal.ofReal (Real.sqrt (t*(1-t)) / _root_.GD.N0232.N0720.N1242.d002130 t x) *
      ENNReal.ofReal ((H x-t)^2) =
    ENNReal.ofReal (Real.sqrt (t*(1-t))) *
      ENNReal.ofReal ((H x-t)^2 / _root_.GD.N0232.N0720.N1242.d002130 t x)
  rw [← ENNReal.ofReal_mul (div_nonneg (Real.sqrt_nonneg _)
      (_root_.GD.N0232.N0720.N1242.d002132 ht hx).le),
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  congr 1
  ring




theorem d002146 (H : ℝ → ℝ) (hH : Measurable H)
    (hdom : ∀ t ∈ Set.Ioo (0:ℝ) 1, _root_.GD.N0232.N0720.N1242.d002144 t H ≤ _root_.GD.N0232.N0720.N1242.d002144 t id) :
    H =ᵐ[_root_.GD.N0232.N0720.N1242.d002139] id := by
  letI := _root_.GD.N0232.N0720.N1242.d002140
  apply _root_.GD.N0232.N0720.N1242.d002138 measurable_id hH _root_.GD.N0232.N0720.N1242.d002141
  intro t ht
  have h := hdom t ht
  rw [_root_.GD.N0232.N0720.N1242.d002145 t ht H hH, _root_.GD.N0232.N0720.N1242.d002145 t ht id measurable_id] at h
  have hc : ENNReal.ofReal (Real.sqrt (t*(1-t))) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr
      (Real.sqrt_pos.mpr (mul_pos ht.1 (sub_pos.mpr ht.2))))
  exact (ENNReal.mul_le_mul_iff_right hc ENNReal.ofReal_ne_top).mp h

end
end GD.N0232.N0720.N1242

#print axioms _root_.GD.N0232.N0720.N1242.d002136
#print axioms _root_.GD.N0232.N0720.N1242.d002138
#print axioms _root_.GD.N0232.N0720.N1242.d002146
