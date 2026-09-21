import GD.Module0667

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0102.N0419

open _root_.GD.N0232.N0719.N0977
open _root_.GD.N0232.N0720.N1341

noncomputable section
variable {d : ℕ}





theorem d009792
    (P : _root_.GD.N0232.N0719.N0977.d009764 d → Prop)
    (hinvariant : ∀ (c a : ℝ), 0 < a → ∀ z,
      P z → P (_root_.GD.N0232.N0719.N0977.d009774 d c a z))
    (hsphere : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, P (_root_.GD.N0232.N0719.N0977.d009773 d u)) :
    ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d)), P z := by
  have hp : ∀ᵐ p : _root_.GD.N0232.N0720.N1341.d004415 d × Ioi (0 : ℝ)
      ∂(_root_.GD.N0232.N0720.N1341.d004416 d).prod (Measure.volumeIoiPow d),
      ∀ c : ℝ, P (_root_.GD.N0232.N0719.N0977.d009768 d (c, p.2.1 • (p.1 : _root_.GD.N0232.N0719.N0977.d009765 d))) := by
    have hs := (Measure.quasiMeasurePreserving_fst
      (μ := _root_.GD.N0232.N0720.N1341.d004416 d) (ν := Measure.volumeIoiPow d)).ae hsphere
    filter_upwards [hs] with p hp
    intro c
    rw [_root_.GD.N0232.N0719.N0977.d009775]
    exact hinvariant c p.2.1 p.2.2 (_root_.GD.N0232.N0719.N0977.d009773 d p.1) hp
  have hsub : ∀ᵐ x : ({0}ᶜ : Set (_root_.GD.N0232.N0719.N0977.d009765 d)) ∂volume.comap Subtype.val,
      ∀ c : ℝ, P (_root_.GD.N0232.N0719.N0977.d009768 d (c, x.1)) := by
    have hpolar := (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)).measurePreserving_homeomorphUnitSphereProd
    have hh := hpolar.quasiMeasurePreserving.ae (by
      simpa only [finrank_euclideanSpace_fin, Nat.add_sub_cancel, _root_.GD.N0232.N0720.N1341.d004416,
        ← homeomorphUnitSphereProd_symm_apply_coe] using hp)
    simpa only [Homeomorph.symm_apply_apply] using hh
  have hv : ∀ᵐ v ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)),
      ∀ c : ℝ, P (_root_.GD.N0232.N0719.N0977.d009768 d (c, v)) := by
    have hr := (ae_restrict_iff_subtype (μ := (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)))
      (p := fun v => ∀ c : ℝ, P (_root_.GD.N0232.N0719.N0977.d009768 d (c, v)))
      (measurableSet_singleton (0 : _root_.GD.N0232.N0719.N0977.d009765 d)).compl).2 hsub
    simpa only [restrict_compl_singleton] using hr
  have hprod : ∀ᵐ p ∂(volume : Measure ℝ).prod (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)),
      P (_root_.GD.N0232.N0719.N0977.d009768 d p) := by
    have hh := (Measure.quasiMeasurePreserving_snd
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)))).ae hv
    filter_upwards [hh] with p hp
    exact hp p.1
  have hback := MeasurePreserving.symm (_root_.GD.N0232.N0719.N0977.d009768 d) (_root_.GD.N0232.N0719.N0977.d009770 d)
  have hh := hback.quasiMeasurePreserving.ae hprod
  simpa only [MeasurableEquiv.apply_symm_apply] using hh




theorem d009793
    (R : _root_.GD.N0232.N0719.N0977.d009764 d → Prop) (f g : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ)
    (hR : ∀ (c a : ℝ), 0 < a → ∀ z,
      R (_root_.GD.N0232.N0719.N0977.d009774 d c a z) ↔ R z)
    (hf : ∀ (c a : ℝ), 0 < a → ∀ z, R z →
      f (_root_.GD.N0232.N0719.N0977.d009774 d c a z) = c + a * f z)
    (hg : ∀ (c a : ℝ), 0 < a → ∀ z, R z →
      g (_root_.GD.N0232.N0719.N0977.d009774 d c a z) = c + a * g z)
    (hsphere : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      R (_root_.GD.N0232.N0719.N0977.d009773 d u) → f (_root_.GD.N0232.N0719.N0977.d009773 d u) = g (_root_.GD.N0232.N0719.N0977.d009773 d u)) :
    ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d)), R z → f z = g z := by
  apply _root_.GD.N0102.N0419.d009792
    (fun z => R z → f z = g z) _ hsphere
  intro c a ha z hz hregular
  have hr := (hR c a ha z).mp hregular
  rw [hf c a ha z hr, hg c a ha z hr, hz hr]

end
end GD.N0102.N0419

#print axioms _root_.GD.N0102.N0419.d009792
#print axioms _root_.GD.N0102.N0419.d009793
