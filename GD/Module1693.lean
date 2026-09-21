import GD.Module1329
import GD.Module0500
import GD.Module1668

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace GD.N0083
noncomputable section

open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0044 _root_.GD.N0043
open _root_.GD.N0072 _root_.GD.N0089

variable {k : ℕ}

def d028535 (i : Fin k) (t : ℝ) : Fin k → ℝ := Function.update (fun _ => 1) i t

def d028536 (shape v : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  _root_.GD.N0232.N0719.N0954.d009342 shape (fun i => shape i / v i)

def d028537 (shape v : Fin k → ℝ)
    (w : (Fin k → ℝ) → Fin k → ℝ) (i : Fin k) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (w x i ^ 2) ∂_root_.GD.N0083.d028536 shape v

def d028538 (shape v : Fin k → ℝ)
    (w : (Fin k → ℝ) → Fin k → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (_root_.GD.N0072.d007621 v (w x)) ∂_root_.GD.N0083.d028536 shape v

theorem d028539 (i : Fin k) {t : ℝ} (ht : 0 < t) :
    ∀ j, 0 < _root_.GD.N0083.d028535 i t j := by
  intro j
  by_cases hj : j = i
  · subst j; simpa [_root_.GD.N0083.d028535] using ht
  · simp [_root_.GD.N0083.d028535, Function.update_of_ne hj]

theorem d028540 (i : Fin k) : _root_.GD.N0083.d028535 i 1 = fun _ => 1 := by
  funext j
  simp [_root_.GD.N0083.d028535]

theorem d028541 (shape : Fin k → ℝ) :
    _root_.GD.N0083.d028536 shape (fun _ => 1) = _root_.GD.N0232.N0719.N0954.d009342 shape shape := by
  simp [_root_.GD.N0083.d028536]

theorem d028542 (shape : Fin k → ℝ) (i : Fin k) (t : ℝ) :
    _root_.GD.N0083.d028536 shape (_root_.GD.N0083.d028535 i t) =
      _root_.GD.N0232.N0719.N0954.d009342 shape (Function.update shape i (shape i / t)) := by
  unfold _root_.GD.N0083.d028536
  congr 1
  funext j
  by_cases hj : j = i
  · subst j; simp [_root_.GD.N0083.d028535]
  · simp [_root_.GD.N0083.d028535, Function.update_of_ne hj]

theorem d028543 {shape v : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i) (hv : ∀ i, 0 < v i) :
    IsProbabilityMeasure (_root_.GD.N0083.d028536 shape v) := by
  letI (i : Fin k) : IsProbabilityMeasure (gammaMeasure (shape i) (shape i / v i)) :=
    isProbabilityMeasure_gammaMeasure (hshape i) (div_pos (hshape i) (hv i))
  unfold _root_.GD.N0083.d028536 _root_.GD.N0232.N0719.N0954.d009342
  infer_instance



theorem d028544 {shape : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i) (i : Fin k) (hi : shape i < 1)
    (w : (Fin k → ℝ) → Fin k → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ M : ℝ, 1 ≤ M →
      ENNReal.ofReal M * _root_.GD.N0083.d028537 shape (_root_.GD.N0083.d028535 i M) w i ≤ ENNReal.ofReal C) :
    _root_.GD.N0083.d028537 shape (fun _ => 1) w i = 0 := by
  apply _root_.GD.N0043.d007627 hi hC
  intro M hM
  calc
    ENNReal.ofReal (M ^ (1 - shape i)) * _root_.GD.N0083.d028537 shape (fun _ => 1) w i ≤
        ENNReal.ofReal M * _root_.GD.N0083.d028537 shape (_root_.GD.N0083.d028535 i M) w i := by
      simpa only [_root_.GD.N0083.d028537, _root_.GD.N0083.d028541, _root_.GD.N0083.d028542] using
        _root_.GD.N0044.d021657 hshape hshape i hM
          (fun x => ENNReal.ofReal (w x i ^ 2))
    _ ≤ _ := hcap M hM



theorem d028545 {shape : Fin k → ℝ}
    (hshape : ∀ j, 0 < shape j) (i : Fin k)
    (w : (Fin k → ℝ) → Fin k → ℝ)
    (hzero : _root_.GD.N0083.d028537 shape (fun _ => 1) w i = 0)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    _root_.GD.N0083.d028537 shape (_root_.GD.N0083.d028535 i e) w i = 0 := by
  have hM : 1 ≤ e⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ he).2 (by simpa using he1)
  have hrate : ∀ j, 0 < Function.update shape i (shape i / e) j := by
    intro j
    by_cases hj : j = i
    · subst j; simpa using div_pos (hshape i) he
    · simpa only [Function.update_of_ne hj] using hshape j
  have hr : Function.update (Function.update shape i (shape i / e)) i
      ((Function.update shape i (shape i / e) i) / e⁻¹) = shape := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
      field_simp [he.ne']
    · simp [Function.update_of_ne hj]
  have hh := _root_.GD.N0044.d021656 hshape hrate i hM
    (fun x => ENNReal.ofReal (w x i ^ 2))
  rw [hr] at hh
  have hh' : ENNReal.ofReal ((e⁻¹) ^ (-shape i)) *
      _root_.GD.N0083.d028537 shape (_root_.GD.N0083.d028535 i e) w i ≤ _root_.GD.N0083.d028537 shape (fun _ => 1) w i := by
    simpa only [_root_.GD.N0083.d028537, _root_.GD.N0083.d028542, _root_.GD.N0083.d028541] using hh
  rw [hzero] at hh'
  have hz := mul_eq_zero.mp (le_antisymm hh' bot_le)
  exact hz.resolve_left (ne_of_gt (ENNReal.ofReal_pos.mpr
    (Real.rpow_pos_of_pos (inv_pos.mpr he) _)))

theorem d028546 {shape : Fin k → ℝ}
    (hshape : ∀ j, 0 < shape j) (i : Fin k)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hzero : _root_.GD.N0083.d028537 shape (fun _ => 1) w i = 0)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    ∀ᵐ x ∂_root_.GD.N0083.d028536 shape (_root_.GD.N0083.d028535 i e), w x i = 0 := by
  have hz := _root_.GD.N0083.d028545 hshape i w hzero he he1
  have hm : Measurable (fun x => ENNReal.ofReal (w x i ^ 2)) := by fun_prop
  have hh := (lintegral_eq_zero_iff hm).mp hz
  filter_upwards [hh] with x hx
  have hs : w x i ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
  nlinarith [sq_nonneg (w x i)]

end
end GD.N0083

#print axioms _root_.GD.N0083.d028544
#print axioms _root_.GD.N0083.d028545
#print axioms _root_.GD.N0083.d028546
