import GD.Module1678
import GD.Module0395

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0089
noncomputable section

variable {k : ℕ}

def d028378 (a : ℝ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ => gammaMeasure a 1
def d028379 (p : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  Measure.pi fun i => gammaMeasure 1 (p i)
def d028380 (a : ℝ) : Measure (Fin k → ℝ) :=
  Measure.pi fun _ => _root_.GD.N0089.d028372 a

def d028381 (a : ℝ) (p : Fin k → ℝ) : ℝ≥0∞ := ∏ i, gammaPDF a 1 (p i)
def d028382 (p x : Fin k → ℝ) : ℝ≥0∞ := ∏ i, gammaPDF 1 (p i) (x i)
def d028383 (a : ℝ) (x : Fin k → ℝ) : ℝ≥0∞ := ∏ i, _root_.GD.N0089.d028371 a (x i)
def d028384 (a : ℝ) (x p : Fin k → ℝ) : ℝ≥0∞ :=
  ∏ i, gammaPDF (a + 1) (1 + x i) (p i)

@[fun_prop] theorem d028385 (s : ℝ) :
    Measurable (fun z : ℝ × ℝ => gammaPDF s z.1 z.2) := by
  unfold gammaPDF gammaPDFReal
  apply Measurable.ennreal_ofReal
  apply Measurable.ite (measurableSet_le measurable_const measurable_snd) <;> fun_prop

@[fun_prop] theorem d028386 (a : ℝ) : Measurable (_root_.GD.N0089.d028381 (k := k) a) := by
  unfold _root_.GD.N0089.d028381 gammaPDF
  fun_prop
@[fun_prop] theorem d028387 :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => _root_.GD.N0089.d028382 z.1 z.2) := by
  unfold _root_.GD.N0089.d028382
  fun_prop
@[fun_prop] theorem d028388 (a : ℝ) : Measurable (_root_.GD.N0089.d028383 (k := k) a) := by
  unfold _root_.GD.N0089.d028383
  fun_prop
@[fun_prop] theorem d028389 (a : ℝ) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => _root_.GD.N0089.d028384 a z.1 z.2) := by
  unfold _root_.GD.N0089.d028384
  fun_prop

theorem d028390 (a : ℝ) : _root_.GD.N0089.d028378 (k := k) a =
    (volume : Measure (Fin k → ℝ)).withDensity (_root_.GD.N0089.d028381 a) := by
  unfold _root_.GD.N0089.d028378 _root_.GD.N0089.d028381 gammaMeasure
  letI : SigmaFinite (volume.withDensity (gammaPDF a 1)) := by
    unfold gammaPDF
    infer_instance
  simpa only [← volume_pi] using _root_.GD.N0089.d006088
    (fun _ : Fin k => (volume : Measure ℝ)) (fun _ => gammaPDF a 1)
    (fun _ => (measurable_gammaPDFReal a 1).ennreal_ofReal)

theorem d028391 (p : Fin k → ℝ) : _root_.GD.N0089.d028379 p =
    (volume : Measure (Fin k → ℝ)).withDensity (_root_.GD.N0089.d028382 p) := by
  unfold _root_.GD.N0089.d028379 _root_.GD.N0089.d028382 gammaMeasure
  letI (i : Fin k) : SigmaFinite (volume.withDensity (gammaPDF 1 (p i))) := by
    unfold gammaPDF
    infer_instance
  simpa only [← volume_pi] using _root_.GD.N0089.d006088
    (fun _ : Fin k => (volume : Measure ℝ)) (fun i => gammaPDF 1 (p i))
    (fun i => (measurable_gammaPDFReal 1 (p i)).ennreal_ofReal)

theorem d028392 (a : ℝ) : _root_.GD.N0089.d028380 (k := k) a =
    (volume : Measure (Fin k → ℝ)).withDensity (_root_.GD.N0089.d028383 a) := by
  unfold _root_.GD.N0089.d028380 _root_.GD.N0089.d028383 _root_.GD.N0089.d028372
  letI : SigmaFinite (volume.withDensity (_root_.GD.N0089.d028371 a)) := by
    unfold _root_.GD.N0089.d028371 paretoPDF
    infer_instance
  simpa only [← volume_pi] using _root_.GD.N0089.d006088
    (fun _ : Fin k => (volume : Measure ℝ)) (fun _ => _root_.GD.N0089.d028371 a)
    (fun _ => _root_.GD.N0089.d028373 a)

theorem d028393 (a : ℝ) (x : Fin k → ℝ) : _root_.GD.N0089.d028313 a x =
    (volume : Measure (Fin k → ℝ)).withDensity (_root_.GD.N0089.d028384 a x) := by
  unfold _root_.GD.N0089.d028313 _root_.GD.N0089.d028384 gammaMeasure
  letI (i : Fin k) : SigmaFinite (volume.withDensity (gammaPDF (a + 1) (1 + x i))) := by
    unfold gammaPDF
    infer_instance
  simpa only [← volume_pi] using _root_.GD.N0089.d006088
    (fun _ : Fin k => (volume : Measure ℝ)) (fun i => gammaPDF (a + 1) (1 + x i))
    (fun i => (measurable_gammaPDFReal (a + 1) (1 + x i)).ennreal_ofReal)

theorem d028394 (a : ℝ) (ha : 0 < a) (p x : Fin k → ℝ) :
    _root_.GD.N0089.d028381 a p * _root_.GD.N0089.d028382 p x = _root_.GD.N0089.d028383 a x * _root_.GD.N0089.d028384 a x p := by
  unfold _root_.GD.N0089.d028381 _root_.GD.N0089.d028382 _root_.GD.N0089.d028383 _root_.GD.N0089.d028384
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [add_comm (x i) 1] using _root_.GD.N0089.d028377 a (x i) (p i) ha




theorem d028395 (a : ℝ) (ha : 0 < a)
    (F : (Fin k → ℝ) → (Fin k → ℝ) → ℝ≥0∞)
    (hF : Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => F z.1 z.2)) :
    (∫⁻ p, ∫⁻ x, F p x ∂_root_.GD.N0089.d028379 p ∂_root_.GD.N0089.d028378 a) =
      ∫⁻ x, ∫⁻ p, F p x ∂_root_.GD.N0089.d028313 a x ∂_root_.GD.N0089.d028380 a := by
  have hleft : (∫⁻ p, ∫⁻ x, F p x ∂_root_.GD.N0089.d028379 p ∂_root_.GD.N0089.d028378 a) =
      ∫⁻ p, ∫⁻ x, _root_.GD.N0089.d028381 a p * _root_.GD.N0089.d028382 p x * F p x := by
    calc
      _ = ∫⁻ p, (∫⁻ x, _root_.GD.N0089.d028382 p x * F p x) ∂_root_.GD.N0089.d028378 a := by
        apply lintegral_congr
        intro p
        rw [_root_.GD.N0089.d028391, lintegral_withDensity_eq_lintegral_mul _
          (show Measurable (_root_.GD.N0089.d028382 p) by fun_prop)
          (show Measurable (fun x => F p x) by fun_prop)]
        rfl
      _ = _ := by
        rw [_root_.GD.N0089.d028390, lintegral_withDensity_eq_lintegral_mul _
          (_root_.GD.N0089.d028386 a)
          (show Measurable (fun p : Fin k → ℝ => ∫⁻ x, _root_.GD.N0089.d028382 p x * F p x) by fun_prop)]
        apply lintegral_congr
        intro p
        change _root_.GD.N0089.d028381 a p * (∫⁻ x, _root_.GD.N0089.d028382 p x * F p x) = _
        rw [← lintegral_const_mul'' _ (by fun_prop)]
        apply lintegral_congr
        intro x
        rw [mul_assoc]
  have hright : (∫⁻ x, ∫⁻ p, F p x ∂_root_.GD.N0089.d028313 a x ∂_root_.GD.N0089.d028380 a) =
      ∫⁻ x, ∫⁻ p, _root_.GD.N0089.d028383 a x * _root_.GD.N0089.d028384 a x p * F p x := by
    calc
      _ = ∫⁻ x, (∫⁻ p, _root_.GD.N0089.d028384 a x p * F p x) ∂_root_.GD.N0089.d028380 a := by
        apply lintegral_congr
        intro x
        rw [_root_.GD.N0089.d028393, lintegral_withDensity_eq_lintegral_mul _
          (show Measurable (_root_.GD.N0089.d028384 a x) by fun_prop)
          (show Measurable (fun p => F p x) by fun_prop)]
        rfl
      _ = _ := by
        rw [_root_.GD.N0089.d028392, lintegral_withDensity_eq_lintegral_mul _
          (_root_.GD.N0089.d028388 a)
          (show Measurable (fun x : Fin k → ℝ => ∫⁻ p, _root_.GD.N0089.d028384 a x p * F p x) by fun_prop)]
        apply lintegral_congr
        intro x
        change _root_.GD.N0089.d028383 a x * (∫⁻ p, _root_.GD.N0089.d028384 a x p * F p x) = _
        rw [← lintegral_const_mul'' _ (by fun_prop)]
        apply lintegral_congr
        intro p
        rw [mul_assoc]
  have hcore : Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) =>
      _root_.GD.N0089.d028381 a z.1 * _root_.GD.N0089.d028382 z.1 z.2 * F z.1 z.2) := by fun_prop
  rw [hleft, hright, lintegral_lintegral_swap hcore.aemeasurable]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro p
  rw [_root_.GD.N0089.d028394 a ha]

end
end GD.N0089

#print axioms _root_.GD.N0089.d028394
#print axioms _root_.GD.N0089.d028395
