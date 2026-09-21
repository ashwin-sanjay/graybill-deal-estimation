import GD.Module0936












open MeasureTheory Set
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1381

open _root_.GD.N0232.N0720.N1393 _root_.GD.N0232.N0720.N1388
open _root_.GD.N0238.N0753

noncomputable section


theorem d014705 {h k : _root_.GD.N0232.N0720.N1393.d004493 → ℝ}
    (hhk : h =ᵐ[_root_.GD.N0232.N0720.N1393.d004494] k) :
    _root_.GD.N0232.N0720.N1393.d004496 h =ᵐ[volume] _root_.GD.N0232.N0720.N1393.d004496 k := by
  have hprod :
      (fun p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ↦
        _root_.GD.N0232.N0720.N1393.d004496 h (((homeomorphUnitSphereProd _root_.GD.N0232.N0720.N1393.d004492).symm p).1)) =ᵐ[
          _root_.GD.N0232.N0720.N1393.d004494.prod (Measure.volumeIoiPow 3)]
      (fun p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ↦
        _root_.GD.N0232.N0720.N1393.d004496 k (((homeomorphUnitSphereProd _root_.GD.N0232.N0720.N1393.d004492).symm p).1)) := by
    have hfst : (fun p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ↦ h p.1) =ᵐ[
        _root_.GD.N0232.N0720.N1393.d004494.prod (Measure.volumeIoiPow 3)] (fun p ↦ k p.1) :=
      (Measure.quasiMeasurePreserving_fst
        (μ := _root_.GD.N0232.N0720.N1393.d004494) (ν := Measure.volumeIoiPow 3)).ae_eq_comp hhk
    filter_upwards [hfst] with p hp
    simp only [homeomorphUnitSphereProd_symm_apply_coe, _root_.GD.N0232.N0720.N1393.d004499]
    exact congrArg (fun v : ℝ ↦ p.2.1 * v) hp
  have hpolar := (volume : Measure _root_.GD.N0232.N0720.N1393.d004492).measurePreserving_homeomorphUnitSphereProd
  have hsub : (fun x : ({0}ᶜ : Set _root_.GD.N0232.N0720.N1393.d004492) ↦ _root_.GD.N0232.N0720.N1393.d004496 h x.1) =ᵐ[
      volume.comap Subtype.val] (fun x ↦ _root_.GD.N0232.N0720.N1393.d004496 k x.1) := by
    have hh := hpolar.quasiMeasurePreserving.ae_eq_comp (by
      simpa only [finrank_euclideanSpace_fin, Nat.reduceSub, _root_.GD.N0232.N0720.N1393.d004494] using hprod)
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hh
  have hr : _root_.GD.N0232.N0720.N1393.d004496 h =ᵐ[
      (volume : Measure _root_.GD.N0232.N0720.N1393.d004492).restrict ({0}ᶜ : Set _root_.GD.N0232.N0720.N1393.d004492)] _root_.GD.N0232.N0720.N1393.d004496 k :=
    (ae_restrict_iff_subtype (μ := (volume : Measure _root_.GD.N0232.N0720.N1393.d004492))
      (p := fun x : _root_.GD.N0232.N0720.N1393.d004492 ↦ _root_.GD.N0232.N0720.N1393.d004496 h x = _root_.GD.N0232.N0720.N1393.d004496 k x)
      (measurableSet_singleton (0 : _root_.GD.N0232.N0720.N1393.d004492)).compl).2 hsub
  simpa only [restrict_compl_singleton] using hr

theorem d014706 (f : _root_.GD.N0232.N0720.N1393.d004492 → ℝ)
    (hf : _root_.GD.N0238.N0753.d004397 f) :
    _root_.GD.N0232.N0720.N1393.d004496 (fun u : _root_.GD.N0232.N0720.N1393.d004493 ↦ f u) = f := by
  apply _root_.GD.N0238.N0753.d004410 _ _ (_root_.GD.N0232.N0720.N1393.d004497 _) hf
  intro u
  exact _root_.GD.N0232.N0720.N1393.d004498 _ ⟨u.1, mem_sphere_zero_iff_norm.mpr u.2⟩

theorem d014707 (f : _root_.GD.N0232.N0720.N1393.d004492 → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ u : _root_.GD.N0232.N0720.N1393.d004493, ‖f u‖ ≤ C) :
    MemLp (fun u : _root_.GD.N0232.N0720.N1393.d004493 ↦ f u) 2 _root_.GD.N0232.N0720.N1393.d004494 := by
  exact MemLp.of_bound (hf.comp measurable_subtype_coe).aestronglyMeasurable C
    (ae_of_all _ hbound)



def d014708 (f : _root_.GD.N0232.N0720.N1393.d004492 → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ u : _root_.GD.N0232.N0720.N1393.d004493, ‖f u‖ ≤ C) : _root_.GD.N0232.N0720.N1393.d004495 :=
  (_root_.GD.N0232.N0720.N1381.d014707 f hf C hbound).toLp (fun u : _root_.GD.N0232.N0720.N1393.d004493 ↦ f u)

theorem d014709 (f : _root_.GD.N0232.N0720.N1393.d004492 → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ u : _root_.GD.N0232.N0720.N1393.d004493, ‖f u‖ ≤ C) :
    _root_.GD.N0232.N0720.N1381.d014708 f hf C hbound =ᵐ[_root_.GD.N0232.N0720.N1393.d004494] (fun u : _root_.GD.N0232.N0720.N1393.d004493 ↦ f u) :=
  (_root_.GD.N0232.N0720.N1381.d014707 f hf C hbound).coeFn_toLp



theorem d014710 (f : _root_.GD.N0232.N0720.N1393.d004492 → ℝ) (hf : Measurable f)
    (hhom : _root_.GD.N0238.N0753.d004397 f) (C : ℝ)
    (hbound : ∀ u : _root_.GD.N0232.N0720.N1393.d004493, ‖f u‖ ≤ C) :
    _root_.GD.N0232.N0720.N1393.d004496 (_root_.GD.N0232.N0720.N1381.d014708 f hf C hbound) =ᵐ[volume] f := by
  have h := _root_.GD.N0232.N0720.N1381.d014705 (_root_.GD.N0232.N0720.N1381.d014709 f hf C hbound)
  rwa [_root_.GD.N0232.N0720.N1381.d014706 f hhom] at h

end

end GD.N0232.N0720.N1381

#print axioms _root_.GD.N0232.N0720.N1381.d014705
#print axioms _root_.GD.N0232.N0720.N1381.d014710
