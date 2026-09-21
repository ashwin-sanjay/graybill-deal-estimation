import Mathlib
import GD.Module0597


















open MeasureTheory Set

namespace GD.N0147

noncomputable section

open _root_.GD.N0118

variable {X ι : Type*} [MeasurableSpace X] [DecidableEq ι]



theorem d008603
    {μ : Measure X} {θ h : X → ℝ} {E : ℝ}
    (hθInt : Integrable θ μ)
    (hθhInt : Integrable (fun x => θ x * h x) μ)
    (hθNonneg : ∀ᵐ x ∂μ, 0 ≤ θ x)
    (hMass : ∫ x, θ x ∂μ = 1)
    (hE : 0 ≤ E)
    (hBound : ∀ᵐ x ∂μ, θ x ≠ 0 → |h x| ≤ E) :
    |∫ x, θ x * h x ∂μ| ≤ E := by
  have hMajorInt : Integrable (fun x => θ x * E) μ :=
    hθInt.mul_const E
  have hPoint :
      ∀ᵐ x ∂μ, |θ x * h x| ≤ θ x * E := by
    filter_upwards [hθNonneg, hBound] with x hθx hx
    by_cases hz : θ x = 0
    · simp [hz]
    · rw [abs_mul, abs_of_nonneg hθx]
      exact mul_le_mul_of_nonneg_left (hx hz) hθx
  calc
    |∫ x, θ x * h x ∂μ|
        ≤ ∫ x, |θ x * h x| ∂μ :=
          abs_integral_le_integral_abs
    _ ≤ ∫ x, θ x * E ∂μ :=
      integral_mono_ae hθhInt.norm hMajorInt hPoint
    _ = (∫ x, θ x ∂μ) * E := by rw [integral_mul_const]
    _ = E := by rw [hMass, one_mul]

lemma d008604 (c w x : ℝ) :
    0 ≤ _root_.GD.N0118.d008582 c w x := by
  by_cases hL : x ∈ Ioc (c - w) c
  · have hR : x ∉ Ioc c (c + w) := by
      intro hx
      linarith [hL.2, hx.1]
    have hnum : 0 ≤ x - (c - w) := sub_nonneg.mpr (le_of_lt hL.1)
    simp [_root_.GD.N0118.d008582, hL, hR, _root_.GD.N0118.d008580, div_nonneg hnum (sq_nonneg w)]
  · by_cases hR : x ∈ Ioc c (c + w)
    · have hnum : 0 ≤ (c + w) - x := sub_nonneg.mpr hR.2
      simp [_root_.GD.N0118.d008582, hL, hR, _root_.GD.N0118.d008581, div_nonneg hnum (sq_nonneg w)]
    · simp [_root_.GD.N0118.d008582, hL, hR]

lemma d008605 (c₁ c₂ w : ℝ) (p : ℝ × ℝ) :
    0 ≤ _root_.GD.N0118.d008583 c₁ c₂ w p :=
  mul_nonneg (_root_.GD.N0147.d008604 c₁ w p.1)
    (_root_.GD.N0147.d008604 c₂ w p.2)



theorem d008606
    (c₁ c₂ w B : ℝ) (g : ℝ × ℝ → ℝ)
    (hw : 0 < w) (hB : 0 ≤ B)
    (hInt :
      Integrable
        (fun p =>
          _root_.GD.N0118.d008583 c₁ c₂ w p * (g p - g (c₁, c₂)))
        (volume.prod volume))
    (hLip :
      ∀ p, _root_.GD.N0118.d008583 c₁ c₂ w p ≠ 0 →
        |g p - g (c₁, c₂)| ≤ B * w) :
    |∫ p,
        _root_.GD.N0118.d008583 c₁ c₂ w p * (g p - g (c₁, c₂))
          ∂(volume.prod volume)| ≤ B * w := by
  apply _root_.GD.N0147.d008603
    (_root_.GD.N0118.d008591 c₁ c₂ w) hInt
  · exact Filter.Eventually.of_forall (_root_.GD.N0147.d008605 c₁ c₂ w)
  · exact _root_.GD.N0118.d008601 c₁ c₂ w hw
  · exact mul_nonneg hB (le_of_lt hw)
  · exact Filter.Eventually.of_forall hLip




theorem d008607
    (c₁ c₂ w p κ B₀ : ℝ)
    (rho g : ℝ × ℝ → ℝ)
    (hw : 0 < w) (hκ : 0 ≤ κ) (hB₀ : 0 ≤ B₀)
    (hInt :
      Integrable
        (fun x =>
          _root_.GD.N0118.d008583 c₁ c₂ w x * ((p * rho x - 1) * g x))
        (volume.prod volume))
    (hRel :
      ∀ x, _root_.GD.N0118.d008583 c₁ c₂ w x ≠ 0 →
        |p * rho x - 1| ≤ κ)
    (hCarrier :
      ∀ x, _root_.GD.N0118.d008583 c₁ c₂ w x ≠ 0 →
        |g x| ≤ B₀) :
    |∫ x,
        _root_.GD.N0118.d008583 c₁ c₂ w x * ((p * rho x - 1) * g x)
          ∂(volume.prod volume)| ≤ κ * B₀ := by
  apply _root_.GD.N0147.d008603
    (_root_.GD.N0118.d008591 c₁ c₂ w) hInt
  · exact Filter.Eventually.of_forall (_root_.GD.N0147.d008605 c₁ c₂ w)
  · exact _root_.GD.N0118.d008601 c₁ c₂ w hw
  · exact mul_nonneg hκ hB₀
  · filter_upwards [] with x
    intro hx
    rw [abs_mul]
    exact mul_le_mul (hRel x hx) (hCarrier x hx)
      (abs_nonneg _) hκ


theorem d008608
    (s : Finset ι) (weight error bound : ι → ℝ)
    (hBound : ∀ i ∈ s, |error i| ≤ bound i) :
    |∑ i ∈ s, weight i * error i|
      ≤ ∑ i ∈ s, |weight i| * bound i := by
  calc
    |∑ i ∈ s, weight i * error i|
        ≤ ∑ i ∈ s, |weight i * error i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, |weight i| * bound i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hBound i hi) (abs_nonneg _)



theorem d008609
    (s : Finset ι) (f : ι → X → ℝ)
    (hDisjoint :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        ∀ x, f i x * f j x = 0) :
    ∀ x, (∑ i ∈ s, f i x) ^ 2 = ∑ i ∈ s, (f i x) ^ 2 := by
  intro x
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hCross : f a x * (∑ i ∈ s, f i x) = 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro i hi
        exact hDisjoint a (Finset.mem_insert_self a s) i
          (Finset.mem_insert_of_mem hi) (Ne.symm (by
            intro hai
            apply ha
            simpa [hai] using hi)) x
      have hIH :
          (∑ i ∈ s, f i x) ^ 2 = ∑ i ∈ s, (f i x) ^ 2 := by
        apply ih
        intro i hi j hj hij
        exact hDisjoint i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij
      simp only [Finset.sum_insert ha]
      calc
        (f a x + ∑ i ∈ s, f i x) ^ 2
            = f a x ^ 2 + (∑ i ∈ s, f i x) ^ 2 := by
              nlinarith
        _ = f a x ^ 2 + ∑ i ∈ s, (f i x) ^ 2 := by rw [hIH]


theorem d008610
    {μ : Measure X} (s : Finset ι) (f : ι → X → ℝ)
    (hDisjoint :
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        ∀ x, f i x * f j x = 0)
    (hInt : ∀ i ∈ s, Integrable (fun x => (f i x) ^ 2) μ) :
    ∫ x, (∑ i ∈ s, f i x) ^ 2 ∂μ
      = ∑ i ∈ s, ∫ x, (f i x) ^ 2 ∂μ := by
  rw [integral_congr_ae
    (Filter.Eventually.of_forall
      (_root_.GD.N0147.d008609 s f hDisjoint))]
  exact integral_finset_sum s hInt



theorem d008611
    (c₁ c₂ w coeff upper : ℝ)
    (density : ℝ × ℝ → ℝ)
    (hw : 0 < w) (hUpper : 0 ≤ upper)
    (hInt :
      Integrable
        (fun x =>
          density x * (coeff * _root_.GD.N0118.d008583 c₁ c₂ w x) ^ 2)
        (volume.prod volume))
    (hDensity :
      ∀ x, _root_.GD.N0118.d008583 c₁ c₂ w x ≠ 0 →
        0 ≤ density x ∧ density x ≤ upper) :
    ∫ x, density x * (coeff * _root_.GD.N0118.d008583 c₁ c₂ w x) ^ 2
        ∂(volume.prod volume)
      ≤ 4 / (9 * w ^ 2) * coeff ^ 2 * upper := by
  have hMajorInt :
      Integrable
        (fun x => upper * (coeff * _root_.GD.N0118.d008583 c₁ c₂ w x) ^ 2)
        (volume.prod volume) := by
    have ht := (_root_.GD.N0118.d008600 c₁ c₂ w).const_mul
      (upper * coeff ^ 2)
    convert ht using 1
    funext x
    ring
  have hPoint :
      ∀ x,
        density x * (coeff * _root_.GD.N0118.d008583 c₁ c₂ w x) ^ 2
          ≤ upper * (coeff * _root_.GD.N0118.d008583 c₁ c₂ w x) ^ 2 := by
    intro x
    by_cases hz : _root_.GD.N0118.d008583 c₁ c₂ w x = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_right (hDensity x hz).2 (sq_nonneg _)
  calc
    ∫ x, density x * (coeff * _root_.GD.N0118.d008583 c₁ c₂ w x) ^ 2
          ∂(volume.prod volume)
        ≤ ∫ x, upper * (coeff * _root_.GD.N0118.d008583 c₁ c₂ w x) ^ 2
          ∂(volume.prod volume) :=
      integral_mono hInt hMajorInt hPoint
    _ = upper * coeff ^ 2 *
        (∫ x, _root_.GD.N0118.d008583 c₁ c₂ w x ^ 2 ∂(volume.prod volume)) := by
      rw [show
          (fun x => upper * (coeff * _root_.GD.N0118.d008583 c₁ c₂ w x) ^ 2) =
            fun x => (upper * coeff ^ 2) * _root_.GD.N0118.d008583 c₁ c₂ w x ^ 2 by
          funext x
          ring,
        integral_const_mul]
    _ = upper * coeff ^ 2 * (4 / (9 * w ^ 2)) := by
      rw [_root_.GD.N0118.d008602 c₁ c₂ w hw]
    _ = 4 / (9 * w ^ 2) * coeff ^ 2 * upper := by ring



theorem d008612
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
          (fun x =>
            density x *
              (coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) ^ 2)
          (volume.prod volume))
    (hDensity :
      ∀ i ∈ s, ∀ x,
        _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x ≠ 0 →
          0 ≤ density x ∧ density x ≤ upper i) :
    ∫ x,
        density x *
          (∑ i ∈ s,
            coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) ^ 2
          ∂(volume.prod volume)
      ≤ ∑ i ∈ s,
          4 / (9 * w ^ 2) * coeff i ^ 2 * upper i := by
  let f : ι → (ℝ × ℝ) → ℝ :=
    fun i x => coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x
  have hSq :
      ∀ x, (∑ i ∈ s, f i x) ^ 2 = ∑ i ∈ s, (f i x) ^ 2 :=
    _root_.GD.N0147.d008609 s f hDisjoint
  have hRewrite :
      (fun x => density x * (∑ i ∈ s, f i x) ^ 2) =
        fun x => ∑ i ∈ s, density x * (f i x) ^ 2 := by
    funext x
    rw [hSq x, Finset.mul_sum]
  rw [show
      (fun x =>
        density x *
          (∑ i ∈ s,
            coeff i * _root_.GD.N0118.d008583 (center₁ i) (center₂ i) w x) ^ 2) =
        fun x => density x * (∑ i ∈ s, f i x) ^ 2 by rfl,
    hRewrite,
    integral_finset_sum s hInt]
  apply Finset.sum_le_sum
  intro i hi
  exact _root_.GD.N0147.d008611
    (center₁ i) (center₂ i) w (coeff i) (upper i) density
    hw (hUpper i hi) (hInt i hi) (hDensity i hi)



theorem d008613
    (atomic smear densityError C : ℝ)
    (hC : 0 ≤ C)
    (hAtomic : atomic ≤ -(3 * C / 4))
    (hSmear : |smear| ≤ C / 16)
    (hDensity : |densityError| ≤ C / 16) :
    atomic + smear + densityError ≤ -(C / 2) := by
  have hs : smear ≤ C / 16 := le_trans (le_abs_self smear) hSmear
  have hd : densityError ≤ C / 16 :=
    le_trans (le_abs_self densityError) hDensity
  linarith



theorem d008614
    (trace energy δ M : ℝ)
    (hδ : 0 < δ) (hM : 0 < M)
    (hTrace : trace ≤ -δ)
    (hEnergy : energy ≤ M) :
    2 * (δ / M) * trace + (δ / M) ^ 2 * energy
      ≤ -(δ ^ 2 / M) := by
  have hε : 0 ≤ δ / M := le_of_lt (div_pos hδ hM)
  have hlin :
      2 * (δ / M) * trace ≤ 2 * (δ / M) * (-δ) :=
    mul_le_mul_of_nonneg_left hTrace (mul_nonneg (by norm_num) hε)
  have hquad :
      (δ / M) ^ 2 * energy ≤ (δ / M) ^ 2 * M :=
    mul_le_mul_of_nonneg_left hEnergy (sq_nonneg _)
  calc
    2 * (δ / M) * trace + (δ / M) ^ 2 * energy
        ≤ 2 * (δ / M) * (-δ) + (δ / M) ^ 2 * M :=
      add_le_add hlin hquad
    _ = -(δ ^ 2 / M) := by
      field_simp [ne_of_gt hM]
      ring

theorem d008615
    (trace energy δ M : ℝ)
    (hδ : 0 < δ) (hM : 0 < M)
    (hTrace : trace ≤ -δ)
    (hEnergy : energy ≤ M) :
    2 * (δ / M) * trace + (δ / M) ^ 2 * energy < 0 := by
  have hMargin := _root_.GD.N0147.d008614
    trace energy δ M hδ hM hTrace hEnergy
  have hNeg : -(δ ^ 2 / M) < 0 :=
    neg_lt_zero.mpr (div_pos (sq_pos_of_pos hδ) hM)
  exact lt_of_le_of_lt hMargin hNeg



theorem d008616
    (atomic smear densityError energy C M : ℝ)
    (hC : 0 < C) (hM : 0 < M)
    (hAtomic : atomic ≤ -(3 * C / 4))
    (hSmear : |smear| ≤ C / 16)
    (hDensity : |densityError| ≤ C / 16)
    (hEnergy : energy ≤ M) :
    let trace := atomic + smear + densityError
    let δ := C / 2
    2 * (δ / M) * trace + (δ / M) ^ 2 * energy
      ≤ -(δ ^ 2 / M) := by
  dsimp
  apply _root_.GD.N0147.d008614
  · linarith
  · exact hM
  · exact _root_.GD.N0147.d008613
      atomic smear densityError C (le_of_lt hC)
      hAtomic hSmear hDensity
  · exact hEnergy

end

end GD.N0147
