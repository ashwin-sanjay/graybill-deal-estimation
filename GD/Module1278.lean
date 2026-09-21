import GD.Module1022










set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0720.N1225

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1237 _root_.GD.N0232.N0720.N1224

def d020627 (q : ℝ) : Set _root_.GD.N0232.N0720.N1436.d013217 :=
  Icc (1 / 4 : ℝ) (3 / 4) ×ˢ Icc (q ^ 2) (2 * q ^ 2)

theorem d020628 (q : ℝ) (hq : 2 ≤ q) :
    1 / q ^ 2 ∈ Ioo (0 : ℝ) 1 := by
  have hq0 : 0 < q := by linarith
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  exact ⟨by positivity, (div_lt_one (sq_pos_of_pos hq0)).2 (by linarith)⟩

def d020629 (q : ℝ) (hq : 2 ≤ q) : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨1 / q ^ 2, _root_.GD.N0232.N0720.N1225.d020628 q hq⟩

def d020630 (q : ℝ) (hq : 2 ≤ q) : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨1 - 1 / q ^ 2, by
    have ht := _root_.GD.N0232.N0720.N1225.d020628 q hq
    constructor <;> linarith [ht.1, ht.2]⟩

theorem d020631 (q : ℝ) (hq : 2 ≤ q) :
    _root_.GD.N0232.N0720.N1225.d020627 q ⊆ _root_.GD.N0232.N0720.N1436.d013218 := by
  intro z hz
  have hq0 : 0 < q := by linarith
  exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
    lt_of_lt_of_le (sq_pos_of_pos hq0) hz.2.1⟩

theorem d020632 (q : ℝ) (hq : 2 ≤ q) :
    _root_.GD.N0232.N0720.N1436.d013288 (_root_.GD.N0232.N0720.N1225.d020627 q) = ENNReal.ofReal (q ^ 2 / 2) := by
  have hs : MeasurableSet (_root_.GD.N0232.N0720.N1225.d020627 q) := measurableSet_Icc.prod measurableSet_Icc
  rw [_root_.GD.N0232.N0720.N1436.d013288, Measure.restrict_apply hs,
    inter_eq_self_of_subset_left (_root_.GD.N0232.N0720.N1225.d020631 q hq)]
  rw [_root_.GD.N0232.N0720.N1225.d020627, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc]
  rw [show (3 / 4 : ℝ) - 1 / 4 = 1 / 2 by ring,
    show 2 * q ^ 2 - q ^ 2 = q ^ 2 by ring]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

private theorem d020633 (t : _root_.GD.N0232.N0720.N1441.d013676)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) :
    Integrable (fun z ↦ _root_.GD.N0232.N0720.N1237.d016241 t z * (g z - (t : ℝ)) ^ 2) _root_.GD.N0232.N0720.N1436.d013288 := by
  apply _root_.GD.N0232.N0720.N1237.d016244 t _ (by fun_prop) (B := 1)
  intro z
  rw [abs_of_nonneg (sq_nonneg _)]
  have h0 := (hb z).1
  have h1 := (hb z).2
  have ht0 := t.property.1
  have ht1 := t.property.2
  nlinarith [mul_nonneg
    (show 0 ≤ 1 - (g z - (t : ℝ)) by linarith)
    (show 0 ≤ 1 + (g z - (t : ℝ)) by linarith)]


theorem d020634
    (q : ℝ) (hq : 2 ≤ q)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) :
    1 / (16384 * q) ≤
      (∫ z, (g z - (_root_.GD.N0232.N0720.N1225.d020629 q hq : ℝ)) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 2 (_root_.GD.N0232.N0720.N1225.d020629 q hq)) +
      (∫ z, (g z - (_root_.GD.N0232.N0720.N1225.d020630 q hq : ℝ)) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 2 (_root_.GD.N0232.N0720.N1225.d020630 q hq)) := by
  let t := _root_.GD.N0232.N0720.N1225.d020629 q hq
  let s := _root_.GD.N0232.N0720.N1225.d020630 q hq
  let F := fun z ↦ _root_.GD.N0232.N0720.N1237.d016241 t z * (g z - (t : ℝ)) ^ 2 + _root_.GD.N0232.N0720.N1237.d016241 s z * (g z - (s : ℝ)) ^ 2
  have hi := (_root_.GD.N0232.N0720.N1225.d020633 t g hg hb).add (_root_.GD.N0232.N0720.N1225.d020633 s g hg hb)
  have hq0 : 0 < q := by linarith
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  have ht4 : 1 / q ^ 2 ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hq0)).2
    nlinarith
  have hpoint : ∀ z ∈ _root_.GD.N0232.N0720.N1225.d020627 q, 1 / (8192 * q ^ 3) ≤ F z := by
    intro z hz
    have ht := _root_.GD.N0232.N0720.N1224.d016251 q hq t (Or.inl rfl) z hz.1 hz.2
    have hs := _root_.GD.N0232.N0720.N1224.d016251 q hq s (Or.inr rfl) z hz.1 hz.2
    have hsq : (1 / 8 : ℝ) ≤ (g z - (t : ℝ)) ^ 2 + (g z - (s : ℝ)) ^ 2 := by
      change (1 / 8 : ℝ) ≤ (g z - 1 / q ^ 2) ^ 2 + (g z - (1 - 1 / q ^ 2)) ^ 2
      nlinarith [sq_nonneg (g z - 1 / 2), sq_nonneg (1 / q ^ 2 - 1 / 4)]
    have hmul := mul_le_mul_of_nonneg_left hsq
      (by positivity : 0 ≤ 1 / (1024 * q ^ 3))
    have hfirst := mul_le_mul_of_nonneg_right ht (sq_nonneg (g z - (t : ℝ)))
    have hsecond := mul_le_mul_of_nonneg_right hs (sq_nonneg (g z - (s : ℝ)))
    calc
      1 / (8192 * q ^ 3) = (1 / (1024 * q ^ 3)) * (1 / 8) := by ring
      _ ≤ _ := hmul
      _ ≤ F z := by dsimp only [F]; nlinarith
  have hnonneg : 0 ≤ᵐ[_root_.GD.N0232.N0720.N1436.d013288] F := by
    filter_upwards [_root_.GD.N0232.N0720.N1237.d016242 t, _root_.GD.N0232.N0720.N1237.d016242 s] with z ht hs
    exact add_nonneg (mul_nonneg ht.le (sq_nonneg _)) (mul_nonneg hs.le (sq_nonneg _))
  have hS : MeasurableSet (_root_.GD.N0232.N0720.N1225.d020627 q) := measurableSet_Icc.prod measurableSet_Icc
  have hfinite : _root_.GD.N0232.N0720.N1436.d013288 (_root_.GD.N0232.N0720.N1225.d020627 q) ≠ ⊤ := by
    rw [_root_.GD.N0232.N0720.N1225.d020632 q hq]
    exact ENNReal.ofReal_ne_top
  have hbound := setIntegral_mono_on
    (integrableOn_const hfinite : IntegrableOn (fun _ : _root_.GD.N0232.N0720.N1436.d013217 ↦ 1 / (8192 * q ^ 3))
      (_root_.GD.N0232.N0720.N1225.d020627 q) _root_.GD.N0232.N0720.N1436.d013288)
    hi.integrableOn hS hpoint
  have hconst : (∫ _ in _root_.GD.N0232.N0720.N1225.d020627 q, (1 / (8192 * q ^ 3) : ℝ)
      ∂_root_.GD.N0232.N0720.N1436.d013288) = 1 / (16384 * q) := by
    rw [integral_const]
    simp only [measureReal_def, Measure.restrict_apply_univ, _root_.GD.N0232.N0720.N1225.d020632 q hq,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ q ^ 2 / 2), smul_eq_mul]
    field_simp [hq0.ne']; ring
  rw [hconst] at hbound
  have htotal := hbound.trans (setIntegral_le_integral hi hnonneg)
  rw [_root_.GD.N0232.N0720.N1237.d016243, _root_.GD.N0232.N0720.N1237.d016243]
  have hsplit := integral_add (_root_.GD.N0232.N0720.N1225.d020633 t g hg hb)
    (_root_.GD.N0232.N0720.N1225.d020633 s g hg hb)
  change (∫ z, F z ∂_root_.GD.N0232.N0720.N1436.d013288) = _ at hsplit
  exact htotal.trans_eq hsplit


theorem d020635
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (C : ℝ) :
    ¬ (∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      (∫ z, (g z - (t : ℝ)) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 2 t) ≤ C * (t : ℝ) * (1 - (t : ℝ))) := by
  intro hcap
  let q := 32768 * (|C| + 1) + 2
  have hq : 2 ≤ q := by dsimp [q]; linarith [abs_nonneg C]
  have hq0 : 0 < q := by linarith
  have hqbig : 32768 * |C| < q := by dsimp [q]; linarith
  have hlower := _root_.GD.N0232.N0720.N1225.d020634 q hq g hg hb
  have ht := hcap (_root_.GD.N0232.N0720.N1225.d020629 q hq)
  have hs := hcap (_root_.GD.N0232.N0720.N1225.d020630 q hq)
  have ht0 : 0 < 1 / q ^ 2 := by positivity
  have ht1 : 1 / q ^ 2 < 1 := (_root_.GD.N0232.N0720.N1225.d020628 q hq).2
  have hCbound : C * (1 / q ^ 2) * (1 - 1 / q ^ 2) ≤ |C| / q ^ 2 := by
    calc
      _ ≤ |C| * (1 / q ^ 2) * (1 - 1 / q ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self C) ht0.le) (by linarith)
      _ ≤ |C| * (1 / q ^ 2) := mul_le_of_le_one_right (by positivity) (by linarith)
      _ = _ := by ring
  have hCbound' : C * (1 - 1 / q ^ 2) * (1 - (1 - 1 / q ^ 2)) ≤ |C| / q ^ 2 := by
    convert hCbound using 1; ring
  change _ ≤ C * (1 / q ^ 2) * (1 - 1 / q ^ 2) at ht
  change _ ≤ C * (1 - 1 / q ^ 2) * (1 - (1 - 1 / q ^ 2)) at hs
  have hineq : 1 / (16384 * q) ≤ 2 * |C| / q ^ 2 := by
    calc
      _ ≤ _ := hlower
      _ ≤ |C| / q ^ 2 + |C| / q ^ 2 := add_le_add (ht.trans hCbound) (hs.trans hCbound')
      _ = _ := by ring
  have hmul := (div_le_div_iff₀ (by positivity : 0 < 16384 * q)
    (sq_pos_of_pos hq0)).1 hineq
  nlinarith [mul_pos hq0 (sub_pos.mpr hqbig)]

end
end GD.N0232.N0720.N1225

#print axioms _root_.GD.N0232.N0720.N1225.d020634
#print axioms _root_.GD.N0232.N0720.N1225.d020635
