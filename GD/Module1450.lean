import GD.Module1449
import GD.Module0669
import GD.Module1263

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0102.N0425

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0983
open _root_.GD.N0232.N0720.N1341 (d004415 d004416)
open _root_.GD.N0213.N0477 (d020379)
open _root_.GD.N0232.N0719.N0977 (d009774 d009773)

noncomputable section
variable {k d : ℕ} (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 2)



def d022967 : _root_.GD.N0232.N0719.N0997.d019804 sizes ≃ᵐ _root_.GD.N0232.N0719.N0977.d009764 d :=
  (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).trans (MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).symm

theorem d022968 :
    (_root_.GD.N0102.N0425.d022967 sizes hdim).symm = _root_.GD.N0213.N0477.d020379 sizes hdim := by
  rfl

theorem d022969 (z : _root_.GD.N0232.N0719.N0997.d019804 sizes) :
    _root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0102.N0425.d022967 sizes hdim z) = z := by
  rw [← _root_.GD.N0102.N0425.d022968]
  exact (_root_.GD.N0102.N0425.d022967 sizes hdim).symm_apply_apply z

theorem d022970 :
    MeasurePreserving (_root_.GD.N0102.N0425.d022967 sizes hdim) volume volume := by
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (d + 2))).comp
    (_root_.GD.N0232.N0719.N0997.d019809 sizes hdim)

theorem d022971 (c a : ℝ) (z : _root_.GD.N0232.N0719.N0977.d009764 d) :
    _root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009774 d c a z) =
      fun i j => c + a * _root_.GD.N0213.N0477.d020379 sizes hdim z i j := by
  rfl





theorem d022972
    (hn : ∀ i, 0 < sizes i) (q : ℝ) (μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ)
    (hs : ∀ (c a : ℝ), 0 < a → ∀ z : _root_.GD.N0232.N0719.N0997.d019804 sizes,
      s (fun i j => c + a * z i j) = c + a * s z)
    (hshape : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      (∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)) i) →
      s (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)) =
        _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
          (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
          (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))) :
    ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)),
      (∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes z i) →
      s z = _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes z) (_root_.GD.N0232.N0719.N0986.d020361 sizes z)
        (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  let R : _root_.GD.N0232.N0719.N0977.d009764 d → Prop :=
    fun z => ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z) i
  let f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ := fun z => s (_root_.GD.N0213.N0477.d020379 sizes hdim z)
  let g : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ := fun z =>
    _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z))
      (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z)) (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
  have hflat : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d)),
      R z → f z = g z := by
    apply _root_.GD.N0102.N0419.d009793
      R f g _ _ _ hshape
    · intro c a ha z
      change (∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009774 d c a z)) i) ↔ _
      rw [_root_.GD.N0102.N0425.d022971]
      simp_rw [_root_.GD.N0102.N0424.d022965 sizes hn]
      exact forall_congr' fun _ => mul_pos_iff_of_pos_left (sq_pos_of_pos ha)
    · intro c a ha z _
      change s (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009774 d c a z)) = c + a * s _
      rw [_root_.GD.N0102.N0425.d022971]
      exact hs c a ha _
    · intro c a ha z hz
      change _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009774 d c a z)))
        (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009774 d c a z)))
        (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) = c + a * _root_.GD.N0232.N0719.N0983.d009724 q _ _ _
      rw [_root_.GD.N0102.N0425.d022971]
      exact _root_.GD.N0102.N0424.d022966 sizes hn q (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) _ hz c a ha.ne'
  have hp := (_root_.GD.N0102.N0425.d022970 sizes hdim).quasiMeasurePreserving.ae hflat
  filter_upwards [hp] with z hz
  simpa only [R, f, g, _root_.GD.N0102.N0425.d022969] using hz




theorem d022973
    (hn : ∀ i, 0 < sizes i) (q : ℝ) (μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ)
    (hs : ∀ (c a : ℝ), 0 < a → ∀ z : _root_.GD.N0232.N0719.N0997.d019804 sizes,
      s (fun i j => c + a * z i j) = c + a * s z)
    (hregular : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)),
      ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes z i)
    (hshape : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      s (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)) =
        _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
          (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
          (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))) :
    ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)),
      s z = _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes z) (_root_.GD.N0232.N0719.N0986.d020361 sizes z)
        (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) := by
  have hh := _root_.GD.N0102.N0425.d022972 sizes hdim hn q μ s hs
    (hshape.mono fun _ hx _ => hx)
  filter_upwards [hh, hregular] with z hz hregularz
  exact hz hregularz

end
end GD.N0102.N0425

#print axioms _root_.GD.N0102.N0425.d022970
#print axioms _root_.GD.N0102.N0425.d022972
#print axioms _root_.GD.N0102.N0425.d022973
