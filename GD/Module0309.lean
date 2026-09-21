import GD.Module0306
import GD.Module0206
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space


















open MeasureTheory Set
open scoped Topology

namespace GD.N0232.N0720.N1393

open _root_.GD.N0232.N0720.N1377
open _root_.GD.N0238.N0753

noncomputable section

abbrev d004492 := EuclideanSpace ℝ (Fin 4)

abbrev d004493 := Metric.sphere (0 : _root_.GD.N0232.N0720.N1393.d004492) 1


def d004494 : Measure _root_.GD.N0232.N0720.N1393.d004493 := (volume : Measure _root_.GD.N0232.N0720.N1393.d004492).toSphere

instance : IsFiniteMeasure _root_.GD.N0232.N0720.N1393.d004494 := by
  unfold _root_.GD.N0232.N0720.N1393.d004494
  infer_instance

abbrev d004495 := Lp ℝ 2 _root_.GD.N0232.N0720.N1393.d004494



def d004496 (h : _root_.GD.N0232.N0720.N1393.d004493 → ℝ) : _root_.GD.N0232.N0720.N1393.d004492 → ℝ :=
  _root_.GD.N0238.N0753.d004402 (fun u : _root_.GD.N0238.N0753.d004398 _root_.GD.N0232.N0720.N1393.d004492 ↦
    h ⟨u.1, mem_sphere_zero_iff_norm.mpr u.2⟩)

theorem d004497 (h : _root_.GD.N0232.N0720.N1393.d004493 → ℝ) :
    _root_.GD.N0238.N0753.d004397 (_root_.GD.N0232.N0720.N1393.d004496 h) :=
  _root_.GD.N0238.N0753.d004403 _

theorem d004498 (h : _root_.GD.N0232.N0720.N1393.d004493 → ℝ) (u : _root_.GD.N0232.N0720.N1393.d004493) :
    _root_.GD.N0232.N0720.N1393.d004496 h u = h u := by
  have hu : ‖(u : _root_.GD.N0232.N0720.N1393.d004492)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  exact _root_.GD.N0238.N0753.d004404 _ ⟨u.1, hu⟩

theorem d004499 (h : _root_.GD.N0232.N0720.N1393.d004493 → ℝ) (u : _root_.GD.N0232.N0720.N1393.d004493)
    (r : Ioi (0 : ℝ)) :
    _root_.GD.N0232.N0720.N1393.d004496 h (r.1 • (u : _root_.GD.N0232.N0720.N1393.d004492)) = r.1 * h u := by
  rw [_root_.GD.N0232.N0720.N1393.d004497 h r.1 r.2, _root_.GD.N0232.N0720.N1393.d004498]
  rfl


theorem d004500 (f : _root_.GD.N0232.N0720.N1393.d004492 → ℝ) :
    (∫ x, f x) =
      ∫ p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ), f (p.2.1 • (p.1 : _root_.GD.N0232.N0720.N1393.d004492))
        ∂_root_.GD.N0232.N0720.N1393.d004494.prod (Measure.volumeIoiPow 3) := by
  calc
    (∫ x, f x) =
        ∫ x : ({0}ᶜ : Set _root_.GD.N0232.N0720.N1393.d004492), f x.1 ∂(volume.comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f,
        restrict_compl_singleton]
    _ = _ := by
      have h := (volume : Measure _root_.GD.N0232.N0720.N1393.d004492).measurePreserving_homeomorphUnitSphereProd
        |>.integral_comp (Homeomorph.measurableEmbedding _)
          (fun p ↦ f ((homeomorphUnitSphereProd _root_.GD.N0232.N0720.N1393.d004492).symm p).1)
      simpa only [Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace_fin, Nat.reduceSub, _root_.GD.N0232.N0720.N1393.d004494] using h



theorem d004501 (f : _root_.GD.N0232.N0720.N1393.d004492 → ℝ) :
    Integrable f ↔
      Integrable (fun p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ↦
        f (p.2.1 • (p.1 : _root_.GD.N0232.N0720.N1393.d004492)))
        (_root_.GD.N0232.N0720.N1393.d004494.prod (Measure.volumeIoiPow 3)) := by
  calc
    Integrable f ↔ IntegrableOn f ({0}ᶜ : Set _root_.GD.N0232.N0720.N1393.d004492) := by
      simp only [IntegrableOn, restrict_compl_singleton]
    _ ↔ Integrable (fun x : ({0}ᶜ : Set _root_.GD.N0232.N0720.N1393.d004492) ↦ f x.1)
        (volume.comap Subtype.val) := by
      simpa only [Function.comp_def] using!
        (integrableOn_iff_comap_subtypeVal (f := f) (μ := volume)
          (measurableSet_singleton (0 : _root_.GD.N0232.N0720.N1393.d004492)).compl)
    _ ↔ Integrable (fun p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ↦
        f (p.2.1 • (p.1 : _root_.GD.N0232.N0720.N1393.d004492)))
        (_root_.GD.N0232.N0720.N1393.d004494.prod (Measure.volumeIoiPow 3)) := by
      have h := (volume : Measure _root_.GD.N0232.N0720.N1393.d004492).measurePreserving_homeomorphUnitSphereProd
        |>.integrable_comp_emb (Homeomorph.measurableEmbedding _)
          (g := fun p ↦ f ((homeomorphUnitSphereProd _root_.GD.N0232.N0720.N1393.d004492).symm p).1)
      simp only [Function.comp_def,
        homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace_fin, Nat.reduceSub] at h
      have hcompose : (fun x : ({0}ᶜ : Set _root_.GD.N0232.N0720.N1393.d004492) ↦
          f (((homeomorphUnitSphereProd _root_.GD.N0232.N0720.N1393.d004492) x).2.1 •
            (((homeomorphUnitSphereProd _root_.GD.N0232.N0720.N1393.d004492) x).1 : _root_.GD.N0232.N0720.N1393.d004492))) =
          (fun x : ({0}ᶜ : Set _root_.GD.N0232.N0720.N1393.d004492) ↦ f x.1) := by
        funext x
        have heq := congrArg (fun y : ({0}ᶜ : Set _root_.GD.N0232.N0720.N1393.d004492) ↦ f y.1)
          ((homeomorphUnitSphereProd _root_.GD.N0232.N0720.N1393.d004492).symm_apply_apply x)
        simpa only [homeomorphUnitSphereProd_symm_apply_coe] using heq
      rw [hcompose] at h
      exact h


theorem d004502 (n : ℕ) (f : ℝ → ℝ) :
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

theorem d004503 (n : ℕ) (f : ℝ → ℝ) :
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

def d004504 (x : _root_.GD.N0232.N0720.N1393.d004492) : ℝ :=
  (Real.pi ^ 2)⁻¹ * Real.exp (-‖x‖ ^ 2)

def d004505 (r : ℝ) : ℝ :=
  r ^ 2 * ((Real.pi ^ 2)⁻¹ * Real.exp (-r ^ 2))

def d004506 : ℝ :=
  (Real.pi ^ 2)⁻¹ * _root_.GD.N0232.N0720.N1377.d002852 5 2 0

theorem d004507 : 0 < _root_.GD.N0232.N0720.N1393.d004506 :=
  mul_pos (inv_pos.mpr (sq_pos_of_pos Real.pi_pos))
    (_root_.GD.N0232.N0720.N1377.d002861 5 (by norm_num) 0)

theorem d004508 :
    Integrable (fun r : Ioi (0 : ℝ) ↦ _root_.GD.N0232.N0720.N1393.d004505 r.1)
      (Measure.volumeIoiPow 3) := by
  rw [_root_.GD.N0232.N0720.N1393.d004503]
  have h := (_root_.GD.N0232.N0720.N1377.d002860 5 (show (0 : ℝ) < 2 by norm_num) 0)
    |>.const_mul ((Real.pi ^ 2)⁻¹)
  have heq : (fun r : ℝ ↦ r ^ 3 * _root_.GD.N0232.N0720.N1393.d004505 r) =
      (fun r : ℝ ↦ (Real.pi ^ 2)⁻¹ * _root_.GD.N0232.N0720.N1377.d002851 5 2 0 r) := by
    funext r
    have hexp : -(2 : ℝ) / 2 * r ^ 2 + 0 * r = -r ^ 2 := by ring
    simp only [_root_.GD.N0232.N0720.N1393.d004505, _root_.GD.N0232.N0720.N1377.d002851, hexp]
    ring
  rw [heq]
  exact h

theorem d004509 :
    (∫ r : Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1393.d004505 r.1 ∂Measure.volumeIoiPow 3) =
      _root_.GD.N0232.N0720.N1393.d004506 := by
  rw [_root_.GD.N0232.N0720.N1393.d004502]
  unfold _root_.GD.N0232.N0720.N1393.d004506 _root_.GD.N0232.N0720.N1377.d002852
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  have hexp : -(2 : ℝ) / 2 * r ^ 2 + 0 * r = -r ^ 2 := by ring
  simp only [_root_.GD.N0232.N0720.N1393.d004505, _root_.GD.N0232.N0720.N1377.d002851, hexp]
  ring

theorem d004510 (d : _root_.GD.N0232.N0720.N1393.d004492 → ℝ)
    (hd : _root_.GD.N0238.N0753.d004397 d) (p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ)) :
    d (p.2.1 • (p.1 : _root_.GD.N0232.N0720.N1393.d004492)) ^ 2 *
        _root_.GD.N0232.N0720.N1393.d004504 (p.2.1 • (p.1 : _root_.GD.N0232.N0720.N1393.d004492)) =
      d p.1 ^ 2 * _root_.GD.N0232.N0720.N1393.d004505 p.2.1 := by
  have hu : ‖(p.1 : _root_.GD.N0232.N0720.N1393.d004492)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp p.1.2
  have hr : 0 < p.2.1 := p.2.2
  rw [hd p.2.1 p.2.2]
  simp only [_root_.GD.N0232.N0720.N1393.d004504, _root_.GD.N0232.N0720.N1393.d004505, smul_eq_mul, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, hu, mul_one]
  ring


theorem d004511 (d : _root_.GD.N0232.N0720.N1393.d004492 → ℝ)
    (hd : _root_.GD.N0238.N0753.d004397 d)
    (hangular : Integrable (fun u : _root_.GD.N0232.N0720.N1393.d004493 ↦ d u ^ 2) _root_.GD.N0232.N0720.N1393.d004494) :
    Integrable (fun x ↦ d x ^ 2 * _root_.GD.N0232.N0720.N1393.d004504 x) := by
  rw [_root_.GD.N0232.N0720.N1393.d004501]
  have hp := hangular.mul_prod _root_.GD.N0232.N0720.N1393.d004508
  exact hp.congr (Filter.Eventually.of_forall (fun p ↦ (_root_.GD.N0232.N0720.N1393.d004510 d hd p).symm))



theorem d004512 (d : _root_.GD.N0232.N0720.N1393.d004492 → ℝ)
    (hd : _root_.GD.N0238.N0753.d004397 d) :
    (∫ x, d x ^ 2 * _root_.GD.N0232.N0720.N1393.d004504 x) =
      _root_.GD.N0232.N0720.N1393.d004506 * ∫ u : _root_.GD.N0232.N0720.N1393.d004493, d u ^ 2 ∂_root_.GD.N0232.N0720.N1393.d004494 := by
  rw [_root_.GD.N0232.N0720.N1393.d004500]
  simp_rw [_root_.GD.N0232.N0720.N1393.d004510 d hd]
  have hprod := integral_prod_mul (μ := _root_.GD.N0232.N0720.N1393.d004494) (ν := Measure.volumeIoiPow 3)
    (fun u : _root_.GD.N0232.N0720.N1393.d004493 ↦ d u ^ 2) (fun r : Ioi (0 : ℝ) ↦ _root_.GD.N0232.N0720.N1393.d004505 r.1)
  simpa only [_root_.GD.N0232.N0720.N1393.d004509, mul_comm] using! hprod

def d004513 (h : _root_.GD.N0232.N0720.N1393.d004495) : ℝ :=
  ∫ x, _root_.GD.N0232.N0720.N1393.d004496 h x ^ 2 * _root_.GD.N0232.N0720.N1393.d004504 x

theorem d004514 (h : _root_.GD.N0232.N0720.N1393.d004495) :
    Integrable (fun x ↦ _root_.GD.N0232.N0720.N1393.d004496 h x ^ 2 * _root_.GD.N0232.N0720.N1393.d004504 x) := by
  apply _root_.GD.N0232.N0720.N1393.d004511 _ (_root_.GD.N0232.N0720.N1393.d004497 h)
  simpa only [_root_.GD.N0232.N0720.N1393.d004498] using (Lp.memLp h).integrable_sq



theorem d004515 (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1393.d004513 h = _root_.GD.N0232.N0720.N1393.d004506 * ‖h‖ ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1393.d004513
  rw [_root_.GD.N0232.N0720.N1393.d004512 _ (_root_.GD.N0232.N0720.N1393.d004497 h)]
  simp only [_root_.GD.N0232.N0720.N1393.d004498]
  congr 1
  rw [← real_inner_self_eq_norm_sq h, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u ↦ by
    change h u ^ 2 = h u * h u
    exact pow_two _)

theorem d004516 : Continuous _root_.GD.N0232.N0720.N1393.d004513 := by
  change Continuous (fun h : _root_.GD.N0232.N0720.N1393.d004495 ↦ _root_.GD.N0232.N0720.N1393.d004513 h)
  simp_rw [_root_.GD.N0232.N0720.N1393.d004515]
  fun_prop


theorem d004517 {h : _root_.GD.N0232.N0720.N1393.d004495} {cap : ℝ}
    (hcap : _root_.GD.N0232.N0720.N1393.d004513 h ≤ cap) :
    ‖h‖ ^ 2 ≤ cap / _root_.GD.N0232.N0720.N1393.d004506 := by
  apply (le_div_iff₀ _root_.GD.N0232.N0720.N1393.d004507).mpr
  simpa only [_root_.GD.N0232.N0720.N1393.d004515, mul_comm] using hcap

end

end GD.N0232.N0720.N1393

#print axioms _root_.GD.N0232.N0720.N1393.d004514
#print axioms _root_.GD.N0232.N0720.N1393.d004515
#print axioms _root_.GD.N0232.N0720.N1393.d004517
