import GD.Module0667

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0213.N0479

noncomputable section

open _root_.GD.N0232.N0719.N0977
open _root_.GD.N0232.N0720.N1341

variable {d : ℕ}

theorem d009787 (c a b : ℝ) (v : _root_.GD.N0232.N0719.N0977.d009765 d) :
    _root_.GD.N0232.N0719.N0977.d009774 d c a (_root_.GD.N0232.N0719.N0977.d009768 d (b, v)) =
      _root_.GD.N0232.N0719.N0977.d009768 d (c + a * b, a • v) := by
  rw [_root_.GD.N0232.N0719.N0977.d009769, _root_.GD.N0232.N0719.N0977.d009769]
  funext i
  cases i using Fin.cases <;> simp [_root_.GD.N0232.N0719.N0977.d009774]
  ring

theorem d009788 (d : ℕ) : Measure.volumeIoiPow d ≠ 0 := by
  intro hz
  have h := _root_.GD.N0232.N0720.N1341.d004431 d
  rw [hz, integral_zero_measure] at h
  exact (_root_.GD.N0232.N0720.N1341.d004429 d).ne' h.symm

theorem d009789
    (P : _root_.GD.N0232.N0719.N0977.d009764 d → Prop)
    (hinvariant : ∀ (c a : ℝ), 0 < a → ∀ z,
      P (_root_.GD.N0232.N0719.N0977.d009774 d c a z) ↔ P z)
    (hraw : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d)), P z) :
    ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, P (_root_.GD.N0232.N0719.N0977.d009773 d u) := by
  have hchart := (_root_.GD.N0232.N0719.N0977.d009770 d).quasiMeasurePreserving.ae hraw
  change ∀ᵐ p ∂(volume : Measure ℝ).prod (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)),
    P (_root_.GD.N0232.N0719.N0977.d009768 d p) at hchart
  obtain ⟨c, hc⟩ := (Measure.ae_ae_of_ae_prod hchart).exists
  have hv : ∀ᵐ v ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)), P (_root_.GD.N0232.N0719.N0977.d009768 d (0, v)) := by
    filter_upwards [hc] with v hv
    have hi := hinvariant c 1 zero_lt_one (_root_.GD.N0232.N0719.N0977.d009768 d (0, v))
    rw [_root_.GD.N0213.N0479.d009787] at hi
    simp only [mul_zero, add_zero, one_smul] at hi
    exact hi.mp hv
  have hsub : ∀ᵐ x : ({0}ᶜ : Set (_root_.GD.N0232.N0719.N0977.d009765 d)) ∂volume.comap Subtype.val,
      P (_root_.GD.N0232.N0719.N0977.d009768 d (0, x.1)) := by
    apply (ae_restrict_iff_subtype (μ := (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)))
      (p := fun x => P (_root_.GD.N0232.N0719.N0977.d009768 d (0, x))) (measurableSet_singleton _).compl).1
    exact ae_restrict_of_ae hv
  have hpolar := (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)).measurePreserving_homeomorphUnitSphereProd
  have hback := MeasurePreserving.symm
    (homeomorphUnitSphereProd (_root_.GD.N0232.N0719.N0977.d009765 d)).toMeasurableEquiv hpolar
  have hp := hback.quasiMeasurePreserving.ae hsub
  have hs : ∀ᵐ p : _root_.GD.N0232.N0720.N1341.d004415 d × Ioi (0 : ℝ)
      ∂(_root_.GD.N0232.N0720.N1341.d004416 d).prod (Measure.volumeIoiPow d), P (_root_.GD.N0232.N0719.N0977.d009773 d p.1) := by
    simp only [finrank_euclideanSpace_fin, Nat.add_sub_cancel] at hp
    filter_upwards [hp] with p hp
    change P (_root_.GD.N0232.N0719.N0977.d009768 d (0,
      ((homeomorphUnitSphereProd (_root_.GD.N0232.N0719.N0977.d009765 d)).symm p).1)) at hp
    rw [homeomorphUnitSphereProd_symm_apply_coe, _root_.GD.N0232.N0719.N0977.d009775] at hp
    exact (hinvariant 0 p.2.1 p.2.2 (_root_.GD.N0232.N0719.N0977.d009773 d p.1)).mp hp
  letI : NeZero (Measure.volumeIoiPow d) := ⟨_root_.GD.N0213.N0479.d009788 d⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with u hu
  exact hu.exists.choose_spec

theorem d009790
    (P : _root_.GD.N0232.N0719.N0977.d009764 d → Prop)
    (hinvariant : ∀ (c a : ℝ), 0 < a → ∀ z,
      P (_root_.GD.N0232.N0719.N0977.d009774 d c a z) ↔ P z)
    (hshape : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, P (_root_.GD.N0232.N0719.N0977.d009773 d u)) :
    ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d)), P z := by
  have hprod : ∀ᵐ p : _root_.GD.N0232.N0720.N1341.d004415 d × Ioi (0 : ℝ)
      ∂(_root_.GD.N0232.N0720.N1341.d004416 d).prod (Measure.volumeIoiPow d),
      P (_root_.GD.N0232.N0719.N0977.d009768 d (0,
        ((homeomorphUnitSphereProd (_root_.GD.N0232.N0719.N0977.d009765 d)).symm p).1)) := by
    have hh := (Measure.quasiMeasurePreserving_fst
      (μ := _root_.GD.N0232.N0720.N1341.d004416 d) (ν := Measure.volumeIoiPow d)).ae hshape
    filter_upwards [hh] with p hp
    rw [homeomorphUnitSphereProd_symm_apply_coe, _root_.GD.N0232.N0719.N0977.d009775]
    exact (hinvariant 0 p.2.1 p.2.2 (_root_.GD.N0232.N0719.N0977.d009773 d p.1)).mpr hp
  have hpolar := (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)).measurePreserving_homeomorphUnitSphereProd
  have hsub : ∀ᵐ x : ({0}ᶜ : Set (_root_.GD.N0232.N0719.N0977.d009765 d)) ∂volume.comap Subtype.val,
      P (_root_.GD.N0232.N0719.N0977.d009768 d (0, x.1)) := by
    have hh := hpolar.quasiMeasurePreserving.ae (by
      simpa only [finrank_euclideanSpace_fin, Nat.add_sub_cancel, _root_.GD.N0232.N0720.N1341.d004416] using hprod)
    simpa only [Homeomorph.symm_apply_apply] using hh
  have hv : ∀ᵐ v ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)), P (_root_.GD.N0232.N0719.N0977.d009768 d (0, v)) := by
    have hh := (ae_restrict_iff_subtype (μ := (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)))
      (p := fun x => P (_root_.GD.N0232.N0719.N0977.d009768 d (0, x))) (measurableSet_singleton _).compl).2 hsub
    simpa only [restrict_compl_singleton] using hh
  have hchart : ∀ᵐ p ∂(volume : Measure ℝ).prod (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)),
      P (_root_.GD.N0232.N0719.N0977.d009768 d p) := by
    have hh := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)))).ae hv
    filter_upwards [hh] with p hp
    have hi := hinvariant p.1 1 zero_lt_one (_root_.GD.N0232.N0719.N0977.d009768 d (0, p.2))
    rw [_root_.GD.N0213.N0479.d009787] at hi
    simp only [mul_zero, add_zero, one_smul] at hi
    exact hi.mpr hp
  have hh := (MeasurePreserving.symm (_root_.GD.N0232.N0719.N0977.d009768 d)
    (_root_.GD.N0232.N0719.N0977.d009770 d)).quasiMeasurePreserving.ae hchart
  simpa only [MeasurableEquiv.apply_symm_apply] using hh

theorem d009791
    (P : _root_.GD.N0232.N0719.N0977.d009764 d → Prop)
    (hinvariant : ∀ (c a : ℝ), 0 < a → ∀ z,
      P (_root_.GD.N0232.N0719.N0977.d009774 d c a z) ↔ P z) :
    (∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d)), P z) ↔
      ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, P (_root_.GD.N0232.N0719.N0977.d009773 d u) :=
  ⟨_root_.GD.N0213.N0479.d009789 P hinvariant,
    _root_.GD.N0213.N0479.d009790 P hinvariant⟩

end
end GD.N0213.N0479

#print axioms _root_.GD.N0213.N0479.d009787
#print axioms _root_.GD.N0213.N0479.d009788
#print axioms _root_.GD.N0213.N0479.d009789
#print axioms _root_.GD.N0213.N0479.d009790
#print axioms _root_.GD.N0213.N0479.d009791
