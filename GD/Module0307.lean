import GD.Module0306
import GD.Module0206
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space
















open MeasureTheory Set
open scoped Topology

namespace GD.N0232.N0720.N1341

open _root_.GD.N0232.N0720.N1377
open _root_.GD.N0238.N0753

noncomputable section

abbrev d004414 (k : ℕ) := EuclideanSpace ℝ (Fin (k + 1))
abbrev d004415 (k : ℕ) := Metric.sphere (0 : _root_.GD.N0232.N0720.N1341.d004414 k) 1

def d004416 (k : ℕ) : Measure (_root_.GD.N0232.N0720.N1341.d004415 k) :=
  (volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)).toSphere

instance (k : ℕ) : IsFiniteMeasure (_root_.GD.N0232.N0720.N1341.d004416 k) := by
  unfold _root_.GD.N0232.N0720.N1341.d004416
  infer_instance

abbrev d004417 (k : ℕ) := Lp ℝ 2 (_root_.GD.N0232.N0720.N1341.d004416 k)

variable {k : ℕ}

def d004418 (h : _root_.GD.N0232.N0720.N1341.d004415 k → ℝ) : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ :=
  _root_.GD.N0238.N0753.d004402 (fun u : _root_.GD.N0238.N0753.d004398 (_root_.GD.N0232.N0720.N1341.d004414 k) ↦
    h ⟨u.1, mem_sphere_zero_iff_norm.mpr u.2⟩)

theorem d004419 (h : _root_.GD.N0232.N0720.N1341.d004415 k → ℝ) :
    _root_.GD.N0238.N0753.d004397 (_root_.GD.N0232.N0720.N1341.d004418 h) :=
  _root_.GD.N0238.N0753.d004403 _

theorem d004420 (h : _root_.GD.N0232.N0720.N1341.d004415 k → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 k) :
    _root_.GD.N0232.N0720.N1341.d004418 h u = h u := by
  have hu : ‖(u : _root_.GD.N0232.N0720.N1341.d004414 k)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  exact _root_.GD.N0238.N0753.d004404 _ ⟨u.1, hu⟩

theorem d004421 (h : _root_.GD.N0232.N0720.N1341.d004415 k → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 k)
    (r : Ioi (0 : ℝ)) :
    _root_.GD.N0232.N0720.N1341.d004418 h (r.1 • (u : _root_.GD.N0232.N0720.N1341.d004414 k)) = r.1 * h u := by
  rw [_root_.GD.N0232.N0720.N1341.d004419 h r.1 r.2, _root_.GD.N0232.N0720.N1341.d004420]
  rfl

theorem d004422 (f : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ) :
    (∫ x, f x) =
      ∫ p : _root_.GD.N0232.N0720.N1341.d004415 k × Ioi (0 : ℝ), f (p.2.1 • (p.1 : _root_.GD.N0232.N0720.N1341.d004414 k))
        ∂(_root_.GD.N0232.N0720.N1341.d004416 k).prod (Measure.volumeIoiPow k) := by
  calc
    (∫ x, f x) =
        ∫ x : ({0}ᶜ : Set (_root_.GD.N0232.N0720.N1341.d004414 k)), f x.1 ∂(volume.comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f,
        restrict_compl_singleton]
    _ = _ := by
      have h := (volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)).measurePreserving_homeomorphUnitSphereProd
        |>.integral_comp (Homeomorph.measurableEmbedding _)
          (fun p ↦ f ((homeomorphUnitSphereProd (_root_.GD.N0232.N0720.N1341.d004414 k)).symm p).1)
      simpa only [Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace_fin, Nat.add_sub_cancel, _root_.GD.N0232.N0720.N1341.d004416] using h

theorem d004423 (f : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ) :
    Integrable f ↔
      Integrable (fun p : _root_.GD.N0232.N0720.N1341.d004415 k × Ioi (0 : ℝ) ↦
        f (p.2.1 • (p.1 : _root_.GD.N0232.N0720.N1341.d004414 k)))
        ((_root_.GD.N0232.N0720.N1341.d004416 k).prod (Measure.volumeIoiPow k)) := by
  calc
    Integrable f ↔ IntegrableOn f ({0}ᶜ : Set (_root_.GD.N0232.N0720.N1341.d004414 k)) := by
      simp only [IntegrableOn, restrict_compl_singleton]
    _ ↔ Integrable (fun x : ({0}ᶜ : Set (_root_.GD.N0232.N0720.N1341.d004414 k)) ↦ f x.1)
        (volume.comap Subtype.val) := by
      simpa only [Function.comp_def] using!
        (integrableOn_iff_comap_subtypeVal (f := f) (μ := volume)
          (measurableSet_singleton (0 : _root_.GD.N0232.N0720.N1341.d004414 k)).compl)
    _ ↔ Integrable (fun p : _root_.GD.N0232.N0720.N1341.d004415 k × Ioi (0 : ℝ) ↦
        f (p.2.1 • (p.1 : _root_.GD.N0232.N0720.N1341.d004414 k)))
        ((_root_.GD.N0232.N0720.N1341.d004416 k).prod (Measure.volumeIoiPow k)) := by
      have h := (volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)).measurePreserving_homeomorphUnitSphereProd
        |>.integrable_comp_emb (Homeomorph.measurableEmbedding _)
          (g := fun p ↦ f ((homeomorphUnitSphereProd (_root_.GD.N0232.N0720.N1341.d004414 k)).symm p).1)
      simp only [Function.comp_def, homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace_fin, Nat.add_sub_cancel] at h
      have hcompose : (fun x : ({0}ᶜ : Set (_root_.GD.N0232.N0720.N1341.d004414 k)) ↦
          f (((homeomorphUnitSphereProd (_root_.GD.N0232.N0720.N1341.d004414 k)) x).2.1 •
            (((homeomorphUnitSphereProd (_root_.GD.N0232.N0720.N1341.d004414 k)) x).1 : _root_.GD.N0232.N0720.N1341.d004414 k))) =
          (fun x : ({0}ᶜ : Set (_root_.GD.N0232.N0720.N1341.d004414 k)) ↦ f x.1) := by
        funext x
        have heq := congrArg (fun y : ({0}ᶜ : Set (_root_.GD.N0232.N0720.N1341.d004414 k)) ↦ f y.1)
          ((homeomorphUnitSphereProd (_root_.GD.N0232.N0720.N1341.d004414 k)).symm_apply_apply x)
        simpa only [homeomorphUnitSphereProd_symm_apply_coe] using heq
      rw [hcompose] at h
      exact h

theorem d004424 (n : ℕ) (f : ℝ → ℝ) :
    (∫ r : Ioi (0 : ℝ), f r.1 ∂Measure.volumeIoiPow n) =
      ∫ r in Ioi (0 : ℝ), r ^ n * f r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi
      (fun r ↦ Real.toNNReal (r ^ n) • f r)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le n)]
    rfl
  · exact (measurable_subtype_coe.pow_const n).real_toNNReal

theorem d004425 (n : ℕ) (f : ℝ → ℝ) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ f r.1) (Measure.volumeIoiPow n) ↔
      IntegrableOn (fun r : ℝ ↦ r ^ n * f r) (Ioi 0) := by
  calc
    _ ↔ Integrable (fun r : Ioi (0 : ℝ) ↦
        (ENNReal.ofReal (r.1 ^ n)).toReal • f r.1)
        (volume.comap Subtype.val) := by
      exact integrable_withDensity_iff_integrable_smul'
        (by fun_prop) (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))
    _ ↔ Integrable (fun r : Ioi (0 : ℝ) ↦ r.1 ^ n * f r.1)
        (volume.comap Subtype.val) := by
      apply integrable_congr
      exact Filter.Eventually.of_forall (fun r ↦ by
        dsimp only
        rw [ENNReal.toReal_ofReal (pow_nonneg r.2.le n), smul_eq_mul])
    _ ↔ _ := by
      simpa only [Function.comp_def] using!
        (integrableOn_iff_comap_subtypeVal (f := fun r : ℝ ↦ r ^ n * f r)
          (μ := volume) measurableSet_Ioi).symm

def d004426 (x : _root_.GD.N0232.N0720.N1341.d004414 k) : ℝ := Real.exp (-‖x‖ ^ 2)
def d004427 (r : ℝ) : ℝ := r ^ 2 * Real.exp (-r ^ 2)
def d004428 (k : ℕ) : ℝ := _root_.GD.N0232.N0720.N1377.d002852 (k + 2) 2 0

theorem d004429 (k : ℕ) : 0 < _root_.GD.N0232.N0720.N1341.d004428 k :=
  _root_.GD.N0232.N0720.N1377.d002861 (k + 2) (by norm_num) 0

theorem d004430 (k : ℕ) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ _root_.GD.N0232.N0720.N1341.d004427 r.1)
      (Measure.volumeIoiPow k) := by
  rw [_root_.GD.N0232.N0720.N1341.d004425]
  have heq : (fun r : ℝ ↦ r ^ k * _root_.GD.N0232.N0720.N1341.d004427 r) =
      _root_.GD.N0232.N0720.N1377.d002851 (k + 2) 2 0 := by
    funext r
    have hexp : -(2 : ℝ) / 2 * r ^ 2 + 0 * r = -r ^ 2 := by ring
    simp only [_root_.GD.N0232.N0720.N1341.d004427, _root_.GD.N0232.N0720.N1377.d002851, hexp, pow_add]
    ring
  rw [heq]
  exact _root_.GD.N0232.N0720.N1377.d002860 (k + 2) (show (0 : ℝ) < 2 by norm_num) 0

theorem d004431 (k : ℕ) :
    (∫ r : Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1341.d004427 r.1 ∂Measure.volumeIoiPow k) =
      _root_.GD.N0232.N0720.N1341.d004428 k := by
  rw [_root_.GD.N0232.N0720.N1341.d004424]
  unfold _root_.GD.N0232.N0720.N1341.d004428 _root_.GD.N0232.N0720.N1377.d002852
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  have hexp : -(2 : ℝ) / 2 * r ^ 2 + 0 * r = -r ^ 2 := by ring
  simp only [_root_.GD.N0232.N0720.N1341.d004427, _root_.GD.N0232.N0720.N1377.d002851, hexp, pow_add]
  ring

theorem d004432 (d : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ)
    (hd : _root_.GD.N0238.N0753.d004397 d) (p : _root_.GD.N0232.N0720.N1341.d004415 k × Ioi (0 : ℝ)) :
    d (p.2.1 • (p.1 : _root_.GD.N0232.N0720.N1341.d004414 k)) ^ 2 *
        _root_.GD.N0232.N0720.N1341.d004426 (p.2.1 • (p.1 : _root_.GD.N0232.N0720.N1341.d004414 k)) =
      d p.1 ^ 2 * _root_.GD.N0232.N0720.N1341.d004427 p.2.1 := by
  have hu : ‖(p.1 : _root_.GD.N0232.N0720.N1341.d004414 k)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.2
  have hr : 0 < p.2.1 := p.2.2
  rw [hd p.2.1 p.2.2]
  simp only [_root_.GD.N0232.N0720.N1341.d004426, _root_.GD.N0232.N0720.N1341.d004427, smul_eq_mul, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, hu, mul_one]
  ring

theorem d004433 (d : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ)
    (hd : _root_.GD.N0238.N0753.d004397 d)
    (hangular : Integrable (fun u : _root_.GD.N0232.N0720.N1341.d004415 k ↦ d u ^ 2) (_root_.GD.N0232.N0720.N1341.d004416 k)) :
    Integrable (fun x ↦ d x ^ 2 * _root_.GD.N0232.N0720.N1341.d004426 x) := by
  rw [_root_.GD.N0232.N0720.N1341.d004423]
  have hp := hangular.mul_prod (_root_.GD.N0232.N0720.N1341.d004430 k)
  exact hp.congr (Filter.Eventually.of_forall (fun p ↦ (_root_.GD.N0232.N0720.N1341.d004432 d hd p).symm))

theorem d004434 (d : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ)
    (hd : _root_.GD.N0238.N0753.d004397 d) :
    (∫ x, d x ^ 2 * _root_.GD.N0232.N0720.N1341.d004426 x) =
      _root_.GD.N0232.N0720.N1341.d004428 k * ∫ u : _root_.GD.N0232.N0720.N1341.d004415 k, d u ^ 2 ∂_root_.GD.N0232.N0720.N1341.d004416 k := by
  rw [_root_.GD.N0232.N0720.N1341.d004422]
  simp_rw [_root_.GD.N0232.N0720.N1341.d004432 d hd]
  have hprod := integral_prod_mul (μ := _root_.GD.N0232.N0720.N1341.d004416 k) (ν := Measure.volumeIoiPow k)
    (fun u : _root_.GD.N0232.N0720.N1341.d004415 k ↦ d u ^ 2) (fun r : Ioi (0 : ℝ) ↦ _root_.GD.N0232.N0720.N1341.d004427 r.1)
  simpa only [_root_.GD.N0232.N0720.N1341.d004431, mul_comm] using! hprod

def d004435 (h : _root_.GD.N0232.N0720.N1341.d004417 k) : ℝ :=
  ∫ x, _root_.GD.N0232.N0720.N1341.d004418 h x ^ 2 * _root_.GD.N0232.N0720.N1341.d004426 x

theorem d004436 (h : _root_.GD.N0232.N0720.N1341.d004417 k) :
    Integrable (fun x ↦ _root_.GD.N0232.N0720.N1341.d004418 h x ^ 2 * _root_.GD.N0232.N0720.N1341.d004426 x) := by
  apply _root_.GD.N0232.N0720.N1341.d004433 _ (_root_.GD.N0232.N0720.N1341.d004419 h)
  simpa only [_root_.GD.N0232.N0720.N1341.d004420] using (Lp.memLp h).integrable_sq

theorem d004437 (h : _root_.GD.N0232.N0720.N1341.d004417 k) :
    _root_.GD.N0232.N0720.N1341.d004435 h = _root_.GD.N0232.N0720.N1341.d004428 k * ‖h‖ ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1341.d004435
  rw [_root_.GD.N0232.N0720.N1341.d004434 _ (_root_.GD.N0232.N0720.N1341.d004419 h)]
  simp only [_root_.GD.N0232.N0720.N1341.d004420]
  congr 1
  rw [← real_inner_self_eq_norm_sq h, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u ↦ by
    change h u ^ 2 = h u * h u
    exact pow_two _)

theorem d004438 : Continuous (_root_.GD.N0232.N0720.N1341.d004435 (k := k)) := by
  change Continuous (fun h : _root_.GD.N0232.N0720.N1341.d004417 k ↦ _root_.GD.N0232.N0720.N1341.d004435 h)
  simp_rw [_root_.GD.N0232.N0720.N1341.d004437]
  fun_prop

theorem d004439 {h : _root_.GD.N0232.N0720.N1341.d004417 k} {cap : ℝ}
    (hcap : _root_.GD.N0232.N0720.N1341.d004435 h ≤ cap) :
    ‖h‖ ^ 2 ≤ cap / _root_.GD.N0232.N0720.N1341.d004428 k := by
  apply (le_div_iff₀ (_root_.GD.N0232.N0720.N1341.d004429 k)).mpr
  simpa only [_root_.GD.N0232.N0720.N1341.d004437, mul_comm] using hcap

end
end GD.N0232.N0720.N1341

#print axioms _root_.GD.N0232.N0720.N1341.d004436
#print axioms _root_.GD.N0232.N0720.N1341.d004437
#print axioms _root_.GD.N0232.N0720.N1341.d004439
