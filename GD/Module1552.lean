import GD.Module1229
import GD.Module1283
import GD.Module1551
import GD.Module1454

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0212.N0461

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0988 _root_.GD.N0232.N0719.N0996
open _root_.GD.N0232.N0719.N0977 _root_.GD.N0232.N0719.N0976
open _root_.GD.N0232.N0719.N0983 _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0211.N0459

noncomputable section
variable {k d : ℕ}



theorem d023995 (c a b : ℝ) (v : _root_.GD.N0232.N0719.N0977.d009765 d) :
    _root_.GD.N0232.N0719.N0977.d009774 d c a (_root_.GD.N0232.N0719.N0977.d009768 d (b, v)) = _root_.GD.N0232.N0719.N0977.d009768 d (c + a * b, a • v) := by
  rw [_root_.GD.N0232.N0719.N0977.d009769, _root_.GD.N0232.N0719.N0977.d009769]
  funext i
  cases i using Fin.cases <;> simp [_root_.GD.N0232.N0719.N0977.d009774]
  ring

theorem d023996 (d : ℕ) : Measure.volumeIoiPow d ≠ 0 := by
  intro hz
  have h := _root_.GD.N0232.N0720.N1341.d004431 d
  rw [hz, integral_zero_measure] at h
  exact (_root_.GD.N0232.N0720.N1341.d004429 d).ne' h.symm

theorem d023997
    (P : _root_.GD.N0232.N0719.N0977.d009764 d → Prop)
    (hinvariant : ∀ (c a : ℝ), 0 < a → ∀ z, P (_root_.GD.N0232.N0719.N0977.d009774 d c a z) ↔ P z)
    (hraw : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d)), P z) :
    ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, P (_root_.GD.N0232.N0719.N0977.d009773 d u) := by
  have hchart := (_root_.GD.N0232.N0719.N0977.d009770 d).quasiMeasurePreserving.ae hraw
  change ∀ᵐ p ∂(volume : Measure ℝ).prod (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)),
    P (_root_.GD.N0232.N0719.N0977.d009768 d p) at hchart
  obtain ⟨c, hc⟩ := (Measure.ae_ae_of_ae_prod hchart).exists
  have hv : ∀ᵐ v ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)), P (_root_.GD.N0232.N0719.N0977.d009768 d (0, v)) := by
    filter_upwards [hc] with v hv
    have hi := hinvariant c 1 zero_lt_one (_root_.GD.N0232.N0719.N0977.d009768 d (0, v))
    rw [_root_.GD.N0212.N0461.d023995] at hi
    simp only [mul_zero, add_zero, one_smul] at hi
    exact hi.mp hv
  have hsub : ∀ᵐ x : ({0}ᶜ : Set (_root_.GD.N0232.N0719.N0977.d009765 d)) ∂volume.comap Subtype.val,
      P (_root_.GD.N0232.N0719.N0977.d009768 d (0, x.1)) := by
    apply (ae_restrict_iff_subtype (μ := (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)))
      (p := fun x => P (_root_.GD.N0232.N0719.N0977.d009768 d (0, x))) (measurableSet_singleton _).compl).1
    exact ae_restrict_of_ae hv
  have hpolar := (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)).measurePreserving_homeomorphUnitSphereProd
  have hback := MeasurePreserving.symm (homeomorphUnitSphereProd (_root_.GD.N0232.N0719.N0977.d009765 d)).toMeasurableEquiv hpolar
  have hp := hback.quasiMeasurePreserving.ae hsub
  have hs : ∀ᵐ p : _root_.GD.N0232.N0720.N1341.d004415 d × Ioi (0 : ℝ)
      ∂(_root_.GD.N0232.N0720.N1341.d004416 d).prod (Measure.volumeIoiPow d), P (_root_.GD.N0232.N0719.N0977.d009773 d p.1) := by
    simp only [finrank_euclideanSpace_fin, Nat.add_sub_cancel] at hp
    filter_upwards [hp] with p hp
    change P (_root_.GD.N0232.N0719.N0977.d009768 d (0,
      ((homeomorphUnitSphereProd (_root_.GD.N0232.N0719.N0977.d009765 d)).symm p).1)) at hp
    rw [homeomorphUnitSphereProd_symm_apply_coe, _root_.GD.N0232.N0719.N0977.d009775] at hp
    exact (hinvariant 0 p.2.1 p.2.2 (_root_.GD.N0232.N0719.N0977.d009773 d p.1)).mp hp
  letI : NeZero (Measure.volumeIoiPow d) := ⟨_root_.GD.N0212.N0461.d023996 d⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with u hu
  exact hu.exists.choose_spec

variable (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 2)

theorem d023998 :
    MeasurePreserving (_root_.GD.N0211.N0459.d020003 sizes hdim) volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (d + 2))).comp
    (_root_.GD.N0232.N0719.N0997.d019809 sizes hdim)

def d023999 (z : _root_.GD.N0232.N0719.N0977.d009764 d) : Prop :=
  _root_.GD.N0232.N0719.N0986.d020362 sizes ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm z) ∈ _root_.GD.N0232.N0719.N0982.d020342

theorem d024000 (hn : ∀ i, 0 < sizes i) (c a : ℝ) (ha : 0 < a)
    (z : _root_.GD.N0232.N0719.N0977.d009764 d) :
    _root_.GD.N0212.N0461.d023999 sizes hdim (_root_.GD.N0232.N0719.N0977.d009774 d c a z) ↔ _root_.GD.N0212.N0461.d023999 sizes hdim z := by
  unfold _root_.GD.N0212.N0461.d023999
  rw [_root_.GD.N0211.N0459.d020005]
  exact _root_.GD.N0212.N0474.d023994 sizes hn c a ha _

theorem d024001 (hn : ∀ i, 2 ≤ sizes i) :
    ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d)), _root_.GD.N0212.N0461.d023999 sizes hdim z := by
  have heuc : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0211.N0459.d019970 d)),
      _root_.GD.N0232.N0719.N0986.d020362 sizes ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x) ∈ _root_.GD.N0232.N0719.N0982.d020342 := by
    apply _root_.GD.N0212.N0470.d023016 sizes hdim (_root_.GD.N0232.N0719.N0988.d019778 k)
    have h := _root_.GD.N0212.N0464.d020737 sizes hn
      (_root_.GD.N0232.N0719.N0996.d019935 (_root_.GD.N0232.N0719.N0988.d019778 k))
    simpa only [MeasurableEquiv.symm_apply_apply, _root_.GD.N0232.N0719.N0859.d010812,
      _root_.GD.N0232.N0719.N0996.d019935] using h
  exact (PiLp.volume_preserving_toLp (Fin (d + 2))).quasiMeasurePreserving.ae heuc

theorem d024002 (hn : ∀ i, 2 ≤ sizes i) :
    ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, _root_.GD.N0212.N0461.d023999 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u) :=
  _root_.GD.N0212.N0461.d023997 (_root_.GD.N0212.N0461.d023999 sizes hdim)
    (_root_.GD.N0212.N0461.d024000 sizes hdim (fun i => lt_of_lt_of_le (by decide : 0 < 2) (hn i)))
    (_root_.GD.N0212.N0461.d024001 sizes hdim hn)

end
end GD.N0212.N0461

#print axioms _root_.GD.N0212.N0461.d023997
#print axioms _root_.GD.N0212.N0461.d024001
#print axioms _root_.GD.N0212.N0461.d024002
