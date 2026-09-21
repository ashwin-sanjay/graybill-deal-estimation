import GD.Module1687

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace GD.N0213.N0494
noncomputable section
open _root_.GD.N0213.N0495 _root_.GD.N0213.N0523 _root_.GD.N0213.N0522
open _root_.GD.N0213.N0516 _root_.GD.N0213.N0521
open _root_.GD.N0230.N0665

variable {k : ℕ}

theorem d028485 (a : Fin k → ℝ) (ρ : ℝ) :
    ∀ᵐ t ∂_root_.GD.N0213.N0516.d028413 a ρ, ∀ i, 0 < t i := by
  rw [_root_.GD.N0213.N0516.d028413, ae_withDensity_iff (_root_.GD.N0213.N0516.d028404 a ρ)]
  filter_upwards with t ht
  by_contra h
  simp [_root_.GD.N0213.N0516.d028400, h] at ht

theorem d028486 (a : Fin k → ℝ) (ρ : ℝ)
    (F : (Fin k → ℝ) → (Fin k → ℝ) → ℝ≥0∞)
    (hF : Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => F z.1 z.2)) :
    Measurable (fun t => ∫⁻ β, F β t ∂_root_.GD.N0213.N0516.d028412 a ρ t) := by
  have heq (t : Fin k → ℝ) : (∫⁻ β, F β t ∂_root_.GD.N0213.N0516.d028412 a ρ t) =
      ∫⁻ β, _root_.GD.N0213.N0516.d028399 a ρ t β * F β t := by
    rw [_root_.GD.N0213.N0516.d028415, lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (_root_.GD.N0213.N0516.d028399 a ρ t) by fun_prop)
      (show Measurable (fun β => F β t) by fun_prop)]
    rfl
  simp_rw [heq]
  fun_prop

def d028487 (L : ℝ) (w : (Fin k → ℝ) → Fin k → ℝ)
    (β t : Fin k → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 * _root_.GD.N0213.N0521.d028475 β (w t))

def d028488 (L : ℝ) (s : Fin k → ℝ) (c : ℝ) (β t : Fin k → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (_root_.GD.N0213.N0495.d007175 L (∑ j, β j) ^ 2 * _root_.GD.N0213.N0521.d028481 s t c)

@[fun_prop] theorem d028489 : Measurable (_root_.GD.N0230.N0665.d000407 (I := Fin k)) := by
  unfold _root_.GD.N0230.N0665.d000407 _root_.GD.N0230.N0665.d000406
  fun_prop

@[fun_prop] theorem d028490 (s : Fin k → ℝ) (c : ℝ) :
    Measurable (fun t => _root_.GD.N0213.N0521.d028481 s t c) := by
  unfold _root_.GD.N0213.N0521.d028481
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  by_cases hij : i = j
  · simp only [if_pos hij]
    fun_prop
  · simp only [if_neg hij]
    fun_prop

@[fun_prop] theorem d028491 (L : ℝ)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => _root_.GD.N0213.N0494.d028487 L w z.1 z.2) := by
  unfold _root_.GD.N0213.N0494.d028487 _root_.GD.N0213.N0495.d007174 _root_.GD.N0213.N0521.d028475
  fun_prop

@[fun_prop] theorem d028492 (L : ℝ) (s : Fin k → ℝ) (c : ℝ) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => _root_.GD.N0213.N0494.d028488 L s c z.1 z.2) := by
  unfold _root_.GD.N0213.N0494.d028488 _root_.GD.N0213.N0495.d007175 _root_.GD.N0213.N0495.d007174
  fun_prop

theorem d028493 {k : ℕ} (a t : Fin (k + 1) → ℝ)
    {ρ L : ℝ} (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i)
    (hρ : ρ < 1) (hL : 0 < L) (w : Fin (k + 1) → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    (∫⁻ β, ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 * _root_.GD.N0213.N0521.d028475 β (_root_.GD.N0230.N0665.d000407 t))
      ∂_root_.GD.N0213.N0516.d028412 a ρ t) ≤
      (∫⁻ β, ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 * _root_.GD.N0213.N0521.d028475 β w) ∂_root_.GD.N0213.N0516.d028412 a ρ t) +
      (∫⁻ β, _root_.GD.N0213.N0494.d028488 L (fun i => a i * (1 - ρ)) (1 - ρ)⁻¹ β t ∂_root_.GD.N0213.N0516.d028412 a ρ t) := by
  let s : Fin (k + 1) → ℝ := fun i => a i * (1 - ρ)
  let c : ℝ := (1 - ρ)⁻¹
  have hs : ∀ i, 0 < s i := fun i => mul_pos (ha i) (sub_pos.mpr hρ)
  have hc : 0 < c := inv_pos.mpr (sub_pos.mpr hρ)
  have hr (i : Fin (k + 1)) : c * s i * t i = a i * t i := by
    dsimp [s, c]
    field_simp [(sub_pos.mpr hρ).ne']
  have h := _root_.GD.N0213.N0521.d028484 s t w hs ht hc hL hw0 hw1
  dsimp only at h
  simp_rw [hr] at h
  exact h

theorem d028494 {k : ℕ} (a : Fin (k + 1) → ℝ)
    {ρ L : ℝ} (ha : ∀ i, 0 < a i) (hρ : ρ < 1) (hL : 0 < L)
    (w : (Fin (k + 1) → ℝ) → Fin (k + 1) → ℝ) (hw : Measurable w)
    (hw0 : ∀ t i, 0 ≤ w t i) (hw1 : ∀ t, ∑ i, w t i = 1) :
    (∫⁻ β, ∫⁻ t, _root_.GD.N0213.N0494.d028487 L _root_.GD.N0230.N0665.d000407 β t
      ∂_root_.GD.N0213.N0516.d028411 a β ∂_root_.GD.N0213.N0522.d008020 (fun i => 1 - ρ * a i)) ≤
      (∫⁻ β, ∫⁻ t, _root_.GD.N0213.N0494.d028487 L w β t
        ∂_root_.GD.N0213.N0516.d028411 a β ∂_root_.GD.N0213.N0522.d008020 (fun i => 1 - ρ * a i)) +
      (∫⁻ β, ∫⁻ t, _root_.GD.N0213.N0494.d028488 L (fun i => a i * (1 - ρ)) (1 - ρ)⁻¹ β t
        ∂_root_.GD.N0213.N0516.d028411 a β ∂_root_.GD.N0213.N0522.d008020 (fun i => 1 - ρ * a i)) := by
  let s : Fin (k + 1) → ℝ := fun i => a i * (1 - ρ)
  let c : ℝ := (1 - ρ)⁻¹
  have hp := _root_.GD.N0213.N0494.d028491 L (_root_.GD.N0230.N0665.d000407 (I := Fin (k + 1))) _root_.GD.N0213.N0494.d028489
  have hwm := _root_.GD.N0213.N0494.d028491 L w hw
  have hE := _root_.GD.N0213.N0494.d028492 L s c
  rw [_root_.GD.N0213.N0516.d028416 a ρ ha hρ _ hp,
    _root_.GD.N0213.N0516.d028416 a ρ ha hρ _ hwm,
    _root_.GD.N0213.N0516.d028416 a ρ ha hρ _ hE]
  calc
    _ ≤ ∫⁻ t, (∫⁻ β, _root_.GD.N0213.N0494.d028487 L w β t ∂_root_.GD.N0213.N0516.d028412 a ρ t) +
        (∫⁻ β, _root_.GD.N0213.N0494.d028488 L s c β t ∂_root_.GD.N0213.N0516.d028412 a ρ t) ∂_root_.GD.N0213.N0516.d028413 a ρ := by
      apply lintegral_mono_ae
      filter_upwards [_root_.GD.N0213.N0494.d028485 a ρ] with t ht
      exact _root_.GD.N0213.N0494.d028493 a t ha ht hρ hL (w t) (hw0 t) (hw1 t)
    _ = _ := lintegral_add_left (_root_.GD.N0213.N0494.d028486 a ρ _ hwm) _

end
end GD.N0213.N0494

#print axioms _root_.GD.N0213.N0494.d028493
#print axioms _root_.GD.N0213.N0494.d028494
