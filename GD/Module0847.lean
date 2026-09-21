import GD.Module0845

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0228.N0547.N0787

noncomputable section

open _root_.GD.N0228.N0547.N0782
  _root_.GD.N0228.N0547.N0778
  _root_.GD.N0228.N0547.N0790




def d012926 (z : ℝ × ℝ) : ℝ :=
  z.1 * Real.sqrt z.2

@[fun_prop]
theorem d012927 :
    Measurable _root_.GD.N0228.N0547.N0787.d012926 := by
  unfold _root_.GD.N0228.N0547.N0787.d012926
  fun_prop


def d012928 (xi : ℝ)
    (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  Real.sqrt xi * _root_.GD.N0228.N0547.N0787.d012926 z.1 +
    Real.sqrt (1 - xi) * _root_.GD.N0228.N0547.N0787.d012926 z.2

@[fun_prop]
theorem d012929 :
    Measurable (fun z : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) ↦
      _root_.GD.N0228.N0547.N0787.d012928 z.1 z.2) := by
  unfold _root_.GD.N0228.N0547.N0787.d012928 _root_.GD.N0228.N0547.N0787.d012926
  fun_prop


def d012930 (p : ℝ) :
    Set ((ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ))) :=
  {z | Real.sqrt z.1.1 ≤ _root_.GD.N0228.N0547.N0782.d003367 p *
    |_root_.GD.N0228.N0547.N0787.d012928 z.1.2 z.2|}

theorem d012931 (p : ℝ) :
    MeasurableSet (_root_.GD.N0228.N0547.N0787.d012930 p) := by
  unfold _root_.GD.N0228.N0547.N0787.d012930
  have hright : Measurable
      (fun z : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × ℝ)) ↦
        _root_.GD.N0228.N0547.N0782.d003367 p *
          |_root_.GD.N0228.N0547.N0787.d012928 z.1.2 z.2|) := by
    unfold _root_.GD.N0228.N0547.N0787.d012928 _root_.GD.N0228.N0547.N0787.d012926
    fun_prop
  exact measurableSet_le (measurable_fst.fst.sqrt) hright


def d012932 (r s : ℕ) (p : ℝ)
    (tx : ℝ × ℝ) : ℝ≥0∞ :=
  _root_.GD.N0228.N0547.N0790.d012893 r s
    (Prod.mk tx ⁻¹' _root_.GD.N0228.N0547.N0787.d012930 p)

theorem d012933
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s) (p : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0787.d012932 r s p) := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012887 r) :=
    _root_.GD.N0228.N0547.N0790.d012888 hrpos
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012887 s) :=
    _root_.GD.N0228.N0547.N0790.d012888 hspos
  unfold _root_.GD.N0228.N0547.N0787.d012932 _root_.GD.N0228.N0547.N0790.d012893
  exact measurable_measure_prodMk_left
    (_root_.GD.N0228.N0547.N0787.d012931 p)

theorem d012934
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s) (p : ℝ)
    (tx : ℝ × ℝ) :
    _root_.GD.N0228.N0547.N0787.d012932 r s p tx ≤ 1 := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0790.d012893 r s) :=
    _root_.GD.N0228.N0547.N0790.d012907 hrpos hspos
  calc
    _root_.GD.N0228.N0547.N0787.d012932 r s p tx ≤
        _root_.GD.N0228.N0547.N0790.d012893 r s Set.univ :=
      measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ


def d012935 (r s : ℕ) (p : ℝ)
    (tx : ℝ × ℝ) : ℝ :=
  (_root_.GD.N0228.N0547.N0787.d012932 r s p tx).toReal

theorem d012936
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s) (p : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0787.d012935 r s p) :=
  (_root_.GD.N0228.N0547.N0787.d012933 hrpos hspos p).ennreal_toReal

theorem d012937
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s) (p : ℝ)
    (tx : ℝ × ℝ) :
    _root_.GD.N0228.N0547.N0787.d012935 r s p tx ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · rw [_root_.GD.N0228.N0547.N0787.d012935, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      (_root_.GD.N0228.N0547.N0787.d012934 hrpos hspos p tx)


def d012938 (rho : ℝ) (base : ℝ × (ℝ × ℝ)) : ℝ :=
  rho * base.2.1 + (1 - rho) * base.2.2


def d012939 (rho : ℝ) (base : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (base.1 ^ 2 / _root_.GD.N0228.N0547.N0787.d012938 rho base,
    rho * base.2.1 / _root_.GD.N0228.N0547.N0787.d012938 rho base)

@[fun_prop]
theorem d012940 (rho : ℝ) : Measurable (_root_.GD.N0228.N0547.N0787.d012939 rho) := by
  unfold _root_.GD.N0228.N0547.N0787.d012939 _root_.GD.N0228.N0547.N0787.d012938
  fun_prop



def d012941 (r s : ℕ) (rho : ℝ) : Measure (ℝ × ℝ) :=
  (_root_.GD.N0228.N0547.N0790.d012894 r s).map (_root_.GD.N0228.N0547.N0787.d012939 rho)

private theorem d012942
    {rho q₁ q₂ : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    0 < rho * q₁ + (1 - rho) * q₂ := by
  positivity

private theorem d012943
    {rho q₁ q₂ : ℝ}
    (hD : rho * q₁ + (1 - rho) * q₂ ≠ 0) :
    1 - rho * q₁ / (rho * q₁ + (1 - rho) * q₂) =
      (1 - rho) * q₂ / (rho * q₁ + (1 - rho) * q₂) := by
  field_simp
  ring

private theorem d012944
    {rho q₁ q₂ : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (z : (ℝ × ℝ) × (ℝ × ℝ)) :
    _root_.GD.N0228.N0547.N0787.d012928
        (rho * q₁ / (rho * q₁ + (1 - rho) * q₂)) z =
      (Real.sqrt rho *
          (z.1.1 * Real.sqrt (z.1.2 * q₁)) +
        Real.sqrt (1 - rho) *
          (z.2.1 * Real.sqrt (z.2.2 * q₂))) /
        Real.sqrt (rho * q₁ + (1 - rho) * q₂) := by
  have hDpos := _root_.GD.N0228.N0547.N0787.d012942 hrho0 hrho1 hq₁ hq₂
  have hD : rho * q₁ + (1 - rho) * q₂ ≠ 0 := ne_of_gt hDpos
  have hrho : 0 ≤ rho := hrho0.le
  have h1rho : 0 ≤ 1 - rho := (sub_pos.mpr hrho1).le
  have hq₁' : 0 ≤ q₁ := hq₁.le
  have hq₂' : 0 ≤ q₂ := hq₂.le
  rw [_root_.GD.N0228.N0547.N0787.d012928, _root_.GD.N0228.N0547.N0787.d012943 hD,
    Real.sqrt_div (mul_nonneg hrho hq₁'),
    Real.sqrt_div (mul_nonneg h1rho hq₂'),
    Real.sqrt_mul hrho q₁, Real.sqrt_mul h1rho q₂]
  have hsqrt₁ : Real.sqrt (z.1.2 * q₁) =
      Real.sqrt q₁ * Real.sqrt z.1.2 := by
    rw [mul_comm, Real.sqrt_mul hq₁']
  have hsqrt₂ : Real.sqrt (z.2.2 * q₂) =
      Real.sqrt q₂ * Real.sqrt z.2.2 := by
    rw [mul_comm, Real.sqrt_mul hq₂']
  rw [hsqrt₁, hsqrt₂]
  unfold _root_.GD.N0228.N0547.N0787.d012926
  field_simp [ne_of_gt (Real.sqrt_pos.2 hDpos)]



def d012945 (rho q₁ q₂ : ℝ)
    (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  Real.sqrt rho * (z.1.1 * Real.sqrt (z.1.2 * q₁)) +
    Real.sqrt (1 - rho) * (z.2.1 * Real.sqrt (z.2.2 * q₂))

private theorem d012946
    (rho p z₀ q₁ q₂ : ℝ) (z : (ℝ × ℝ) × (ℝ × ℝ)) :
    ((z₀, (q₁, q₂)), z) ∈ _root_.GD.N0228.N0547.N0790.d012904 rho p ↔
      |z₀| ≤ _root_.GD.N0228.N0547.N0782.d003367 p * |_root_.GD.N0228.N0547.N0787.d012945 rho q₁ q₂ z| := by
  rfl

private theorem d012947
    {rho q₁ q₂ : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (p z₀ : ℝ)
    (z : (ℝ × ℝ) × (ℝ × ℝ)) :
    ((_root_.GD.N0228.N0547.N0787.d012939 rho (z₀, (q₁, q₂))), z) ∈
        _root_.GD.N0228.N0547.N0787.d012930 p ↔
      |z₀| ≤ _root_.GD.N0228.N0547.N0782.d003367 p *
        |_root_.GD.N0228.N0547.N0787.d012945 rho q₁ q₂ z| := by
  have hDpos := _root_.GD.N0228.N0547.N0787.d012942 hrho0 hrho1 hq₁ hq₂
  have hsqrtDpos : 0 < Real.sqrt
      (rho * q₁ + (1 - rho) * q₂) := Real.sqrt_pos.2 hDpos
  have hleft : Real.sqrt
      (z₀ ^ 2 / (rho * q₁ + (1 - rho) * q₂)) =
      |z₀| / Real.sqrt (rho * q₁ + (1 - rho) * q₂) := by
    rw [Real.sqrt_div (sq_nonneg z₀), Real.sqrt_sq_eq_abs]
  have hright : _root_.GD.N0228.N0547.N0787.d012928
        (rho * q₁ / (rho * q₁ + (1 - rho) * q₂)) z =
      _root_.GD.N0228.N0547.N0787.d012945 rho q₁ q₂ z /
        Real.sqrt (rho * q₁ + (1 - rho) * q₂) := by
    simpa only [_root_.GD.N0228.N0547.N0787.d012945] using
      _root_.GD.N0228.N0547.N0787.d012944 hrho0 hrho1 hq₁ hq₂ z
  unfold _root_.GD.N0228.N0547.N0787.d012930 _root_.GD.N0228.N0547.N0787.d012939 _root_.GD.N0228.N0547.N0787.d012938
  change Real.sqrt
      (z₀ ^ 2 / (rho * q₁ + (1 - rho) * q₂)) ≤
        _root_.GD.N0228.N0547.N0782.d003367 p *
          |_root_.GD.N0228.N0547.N0787.d012928
            (rho * q₁ / (rho * q₁ + (1 - rho) * q₂)) z| ↔ _
  rw [hleft, hright, abs_div, abs_of_pos hsqrtDpos]
  rw [show _root_.GD.N0228.N0547.N0782.d003367 p *
      (|_root_.GD.N0228.N0547.N0787.d012945 rho q₁ q₂ z| /
        Real.sqrt (rho * q₁ + (1 - rho) * q₂)) =
      (_root_.GD.N0228.N0547.N0782.d003367 p * |_root_.GD.N0228.N0547.N0787.d012945 rho q₁ q₂ z|) /
        Real.sqrt (rho * q₁ + (1 - rho) * q₂) by ring]
  exact div_le_div_iff_of_pos_right hsqrtDpos



theorem d012948
    {r s : ℕ} {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (p z₀ q₁ q₂ : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    _root_.GD.N0228.N0547.N0787.d012932 r s p
        (_root_.GD.N0228.N0547.N0787.d012939 rho (z₀, (q₁, q₂))) =
      _root_.GD.N0228.N0547.N0790.d012906 r s rho p (z₀, (q₁, q₂)) := by
  unfold _root_.GD.N0228.N0547.N0787.d012932 _root_.GD.N0228.N0547.N0790.d012906
  congr 1
  ext z
  change
    ((_root_.GD.N0228.N0547.N0787.d012939 rho (z₀, (q₁, q₂))), z) ∈
        _root_.GD.N0228.N0547.N0787.d012930 p ↔
      ((z₀, (q₁, q₂)), z) ∈ _root_.GD.N0228.N0547.N0790.d012904 rho p
  rw [_root_.GD.N0228.N0547.N0787.d012947 hrho0 hrho1 hq₁ hq₂ p z₀ z,
    _root_.GD.N0228.N0547.N0787.d012946]

private theorem d012949
    {d : ℕ} (hd : 0 < d) : ∀ᵐ q ∂_root_.GD.N0228.N0547.N0778.d009365 d, 0 < q := by
  unfold _root_.GD.N0228.N0547.N0778.d009365
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  exact _root_.GD.N0232.N0720.N1091.d012773
    (by positivity) (by norm_num)

private theorem d012950
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s) :
    ∀ᵐ base ∂_root_.GD.N0228.N0547.N0790.d012894 r s, 0 < base.2.1 ∧ 0 < base.2.2 := by
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 r) :=
    _root_.GD.N0228.N0547.N0790.d012889 hrpos
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 s) :=
    _root_.GD.N0228.N0547.N0790.d012889 hspos
  have hinnerSet : MeasurableSet
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hinner : ∀ᵐ qs ∂(_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s),
      qs ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae hinnerSet).2
    filter_upwards [_root_.GD.N0228.N0547.N0787.d012949 hrpos] with q₁ hq₁
    filter_upwards [_root_.GD.N0228.N0547.N0787.d012949 hspos] with q₂ hq₂
    exact ⟨hq₁, hq₂⟩
  have houterSet : MeasurableSet
      ((Set.univ : Set ℝ) ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))) :=
    MeasurableSet.univ.prod hinnerSet
  unfold _root_.GD.N0228.N0547.N0790.d012894
  have hout : ∀ᵐ base ∂(gaussianReal 0 1).prod
      ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s)),
      base ∈ (Set.univ : Set ℝ) ×ˢ
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := by
    apply (Measure.ae_prod_iff_ae_ae houterSet).2
    filter_upwards with z₀
    filter_upwards [hinner] with qs hqs
    exact ⟨Set.mem_univ z₀, hqs⟩
  filter_upwards [hout] with base hbase
  exact ⟨hbase.2.1, hbase.2.2⟩




theorem d012951
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s)
    {rho p : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∫⁻ tx, _root_.GD.N0228.N0547.N0787.d012932 r s p tx
        ∂(_root_.GD.N0228.N0547.N0787.d012941 r s rho) = ENNReal.ofReal p := by
  calc
    ∫⁻ tx, _root_.GD.N0228.N0547.N0787.d012932 r s p tx
        ∂(_root_.GD.N0228.N0547.N0787.d012941 r s rho) =
        ∫⁻ base, _root_.GD.N0228.N0547.N0787.d012932 r s p
          (_root_.GD.N0228.N0547.N0787.d012939 rho base) ∂(_root_.GD.N0228.N0547.N0790.d012894 r s) := by
      unfold _root_.GD.N0228.N0547.N0787.d012941
      exact lintegral_map
        (_root_.GD.N0228.N0547.N0787.d012933 hrpos hspos p)
        (_root_.GD.N0228.N0547.N0787.d012940 rho)
    _ = ∫⁻ base, _root_.GD.N0228.N0547.N0790.d012906 r s rho p base
          ∂(_root_.GD.N0228.N0547.N0790.d012894 r s) := by
      apply lintegral_congr_ae
      filter_upwards [_root_.GD.N0228.N0547.N0787.d012950 hrpos hspos]
        with base hbase
      exact _root_.GD.N0228.N0547.N0787.d012948 hrho0 hrho1 p
        base.1 base.2.1 base.2.2 hbase.1 hbase.2
    _ = ENNReal.ofReal p :=
      _root_.GD.N0228.N0547.N0790.d012913 hrpos hspos
        hrho0.le hrho1.le hp0 hp1

theorem d012952
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s) (p : ℝ)
    (tx : ℝ × ℝ) :
    ENNReal.ofReal (_root_.GD.N0228.N0547.N0787.d012935 r s p tx) =
      _root_.GD.N0228.N0547.N0787.d012932 r s p tx := by
  rw [_root_.GD.N0228.N0547.N0787.d012935, ENNReal.ofReal_toReal]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    (_root_.GD.N0228.N0547.N0787.d012934 hrpos hspos p tx)


theorem d012953
    {r s : ℕ} (hrpos : 0 < r) (hspos : 0 < s)
    {rho p : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∫⁻ tx, ENNReal.ofReal
        (_root_.GD.N0228.N0547.N0787.d012935 r s p tx)
        ∂(_root_.GD.N0228.N0547.N0787.d012941 r s rho) = ENNReal.ofReal p := by
  simp_rw [_root_.GD.N0228.N0547.N0787.d012952 hrpos hspos p]
  exact _root_.GD.N0228.N0547.N0787.d012951
    hrpos hspos hrho0 hrho1 hp0 hp1

end

end GD.N0228.N0547.N0787

#print axioms _root_.GD.N0228.N0547.N0787.d012948
#print axioms _root_.GD.N0228.N0547.N0787.d012951
#print axioms _root_.GD.N0228.N0547.N0787.d012952
#print axioms _root_.GD.N0228.N0547.N0787.d012953
