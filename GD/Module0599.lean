import GD.Module0598

open MeasureTheory Set

namespace GD.N0147

noncomputable section

open _root_.GD.N0118





theorem d008617
    (c₁ c₂ w coeff upper : ℝ)
    (density : ℝ × ℝ → ℝ)
    (hw : 0 < w) (hUpper : 0 ≤ upper) (hcoeff : coeff ≠ 0)
    (hInt :
      Integrable
        (fun x ↦ density x * (coeff * _root_.GD.N0118.d008583 c₁ c₂ w x) ^ 2)
        (volume.prod volume))
    (hDensity :
      ∀ x, _root_.GD.N0118.d008583 c₁ c₂ w x ≠ 0 →
        0 ≤ density x ∧ density x < upper) :
    ∫ x, density x * (coeff * _root_.GD.N0118.d008583 c₁ c₂ w x) ^ 2
        ∂(volume.prod volume)
      < 4 / (9 * w ^ 2) * coeff ^ 2 * upper := by
  let t : ℝ × ℝ → ℝ := fun x ↦ _root_.GD.N0118.d008583 c₁ c₂ w x
  let f : ℝ × ℝ → ℝ :=
    fun x ↦ density x * (coeff * t x) ^ 2
  let g : ℝ × ℝ → ℝ :=
    fun x ↦ upper * (coeff * t x) ^ 2
  have hgInt : Integrable g (volume.prod volume) := by
    have ht := (_root_.GD.N0118.d008600 c₁ c₂ w).const_mul
      (upper * coeff ^ 2)
    convert ht using 1
    funext x
    dsimp [g, t]
    ring
  have hfInt : Integrable f (volume.prod volume) := by
    simpa [f, t] using hInt
  have hdiffInt : Integrable (fun x ↦ g x - f x) (volume.prod volume) :=
    hgInt.sub hfInt
  have hdiffNonneg : ∀ x, 0 ≤ g x - f x := by
    intro x
    by_cases hx : t x = 0
    · simp [f, g, hx]
    · have hle := (hDensity x (by simpa [t] using hx)).2.le
      dsimp [f, g]
      exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right hle (sq_nonneg _))
  have htInt : Integrable (fun x ↦ t x ^ 2) (volume.prod volume) := by
    simpa [t] using _root_.GD.N0118.d008600 c₁ c₂ w
  have htIntegralPos : 0 < ∫ x, t x ^ 2 ∂(volume.prod volume) := by
    rw [show (∫ x, t x ^ 2 ∂(volume.prod volume)) = 4 / (9 * w ^ 2) by
      simpa [t] using _root_.GD.N0118.d008602 c₁ c₂ w hw]
    positivity
  have htSupport :
      0 < (volume.prod volume) (Function.support (fun x ↦ t x ^ 2)) :=
    (integral_pos_iff_support_of_nonneg
      (fun x ↦ sq_nonneg (t x)) htInt).mp htIntegralPos
  have hsupportSub :
      Function.support (fun x ↦ t x ^ 2) ⊆
        Function.support (fun x ↦ g x - f x) := by
    intro x hx
    have htx : t x ≠ 0 := by
      simpa [Function.mem_support] using hx
    have hd := (hDensity x (by simpa [t] using htx)).2
    have hsquare : 0 < (coeff * t x) ^ 2 := sq_pos_of_ne_zero (mul_ne_zero hcoeff htx)
    have hpos : 0 < g x - f x := by
      dsimp [g, f]
      nlinarith [mul_pos (sub_pos.mpr hd) hsquare]
    exact hpos.ne'
  have hdiffSupport :
      0 < (volume.prod volume) (Function.support (fun x ↦ g x - f x)) :=
    htSupport.trans_le (measure_mono hsupportSub)
  have hdiffIntegralPos :
      0 < ∫ x, (g x - f x) ∂(volume.prod volume) :=
    (integral_pos_iff_support_of_nonneg hdiffNonneg hdiffInt).mpr hdiffSupport
  have hfg : (∫ x, f x ∂(volume.prod volume)) < ∫ x, g x ∂(volume.prod volume) := by
    rw [integral_sub hgInt hfInt] at hdiffIntegralPos
    linarith
  calc
    (∫ x, density x * (coeff * _root_.GD.N0118.d008583 c₁ c₂ w x) ^ 2
        ∂(volume.prod volume)) = ∫ x, f x ∂(volume.prod volume) := by rfl
    _ < ∫ x, g x ∂(volume.prod volume) := hfg
    _ = upper * coeff ^ 2 *
        (∫ x, _root_.GD.N0118.d008583 c₁ c₂ w x ^ 2 ∂(volume.prod volume)) := by
      rw [show g = fun x ↦ (upper * coeff ^ 2) * _root_.GD.N0118.d008583 c₁ c₂ w x ^ 2 by
        funext x
        dsimp [g, t]
        ring,
        integral_const_mul]
    _ = upper * coeff ^ 2 * (4 / (9 * w ^ 2)) := by
      rw [_root_.GD.N0118.d008602 c₁ c₂ w hw]
    _ = 4 / (9 * w ^ 2) * coeff ^ 2 * upper := by ring




theorem d008618
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (center₁ center₂ coeff upper : ι → ℝ)
    (w : ℝ) (density : ℝ × ℝ → ℝ)
    (hw : 0 < w) (hUpper : ∀ i ∈ s, 0 ≤ upper i)
    (hDisjoint :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x,
        (coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) *
          (coeff j * _root_.GD.N0118.d008583 (center₁ j) (center₂ j) w x) = 0)
    (hInt :
      ∀ i ∈ s,
        Integrable
          (fun x ↦ density x *
            (coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) ^ 2)
          (volume.prod volume))
    (hDensity :
      ∀ i ∈ s, ∀ x,
        _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x ≠ 0 →
          0 ≤ density x ∧ density x < upper i)
    (hnonzero : ∃ i ∈ s, coeff i ≠ 0) :
    ∫ x,
        density x *
          (∑ i ∈ s,
            coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) ^ 2
          ∂(volume.prod volume)
      < ∑ i ∈ s,
          4 / (9 * w ^ 2) * coeff i ^ 2 * upper i := by
  let f : ι → (ℝ × ℝ) → ℝ :=
    fun i x ↦ coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x
  have hSq :
      ∀ x, (∑ i ∈ s, f i x) ^ 2 = ∑ i ∈ s, (f i x) ^ 2 :=
    _root_.GD.N0147.d008609 s f hDisjoint
  have hRewrite :
      (fun x ↦ density x * (∑ i ∈ s, f i x) ^ 2) =
        fun x ↦ ∑ i ∈ s, density x * (f i x) ^ 2 := by
    funext x
    rw [hSq x, Finset.mul_sum]
  rw [show
      (fun x ↦ density x *
        (∑ i ∈ s,
          coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) ^ 2) =
        fun x ↦ density x * (∑ i ∈ s, f i x) ^ 2 by rfl,
    hRewrite,
    integral_finset_sum s hInt]
  apply Finset.sum_lt_sum
  · intro i hi
    exact _root_.GD.N0147.d008611
      (center₁ i) (center₂ i) w (coeff i) (upper i) density
      hw (hUpper i hi) (hInt i hi)
      (fun x hx ↦ ⟨(hDensity i hi x hx).1, (hDensity i hi x hx).2.le⟩)
  · obtain ⟨i, hi, hci⟩ := hnonzero
    exact ⟨i, hi,
      _root_.GD.N0147.d008617
        (center₁ i) (center₂ i) w (coeff i) (upper i) density
        hw (hUpper i hi) hci (hInt i hi) (hDensity i hi)⟩



theorem d008619
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (center₁ center₂ coeff : ι → ℝ)
    (w : ℝ) (density₁ density₂ : ℝ × ℝ → ℝ)
    (hDisjoint :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x,
        (coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) *
          (coeff j * _root_.GD.N0118.d008583 (center₁ j) (center₂ j) w x) = 0)
    (hInt₁ :
      ∀ i ∈ s,
        Integrable
          (fun x ↦ density₁ x *
            (coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) ^ 2)
          (volume.prod volume))
    (hInt₂ :
      ∀ i ∈ s,
        Integrable
          (fun x ↦ density₂ x *
            (coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) ^ 2)
          (volume.prod volume))
    (hDensity :
      ∀ i ∈ s, ∀ x,
        _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x ≠ 0 →
          density₁ x ≤ density₂ x) :
    ∫ x,
        density₁ x *
          (∑ i ∈ s,
            coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) ^ 2
          ∂(volume.prod volume)
      ≤
    ∫ x,
        density₂ x *
          (∑ i ∈ s,
            coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) ^ 2
          ∂(volume.prod volume) := by
  let f : ι → (ℝ × ℝ) → ℝ :=
    fun i x ↦ coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x
  have hSq :
      ∀ x, (∑ i ∈ s, f i x) ^ 2 = ∑ i ∈ s, (f i x) ^ 2 :=
    _root_.GD.N0147.d008609 s f hDisjoint
  have hRewrite (density : ℝ × ℝ → ℝ) :
      (fun x ↦ density x * (∑ i ∈ s, f i x) ^ 2) =
        fun x ↦ ∑ i ∈ s, density x * (f i x) ^ 2 := by
    funext x
    rw [hSq x, Finset.mul_sum]
  rw [show
      (fun x ↦ density₁ x *
        (∑ i ∈ s,
          coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) ^ 2) =
        fun x ↦ density₁ x * (∑ i ∈ s, f i x) ^ 2 by rfl,
    show
      (fun x ↦ density₂ x *
        (∑ i ∈ s,
          coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) ^ 2) =
        fun x ↦ density₂ x * (∑ i ∈ s, f i x) ^ 2 by rfl,
    hRewrite density₁, hRewrite density₂,
    integral_finset_sum s hInt₁, integral_finset_sum s hInt₂]
  apply Finset.sum_le_sum
  intro i hi
  apply integral_mono (hInt₁ i hi) (hInt₂ i hi)
  intro x
  by_cases hx : _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x = 0
  · simp [hx, f]
  · exact mul_le_mul_of_nonneg_right (hDensity i hi x hx) (sq_nonneg _)

end

end GD.N0147
