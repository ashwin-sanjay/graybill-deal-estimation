import GD.Module0937
import GD.Module0932










open MeasureTheory Set
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1392

open _root_.GD.N0232.N0720.N1393 _root_.GD.N0232.N0720.N1372
open _root_.GD.N0232.N0720.N1388 _root_.GD.N0232.N0720.N1389 _root_.GD.N0232.N0720.N1387
open _root_.GD.N0232.N0720.N1381
open _root_.GD.N0238.N0753
open _root_.GD.N0230.N0556
open _root_.GD.N0232.N0720.N1159

noncomputable section

theorem d014711 :
    Measure.QuasiMeasurePreserving _root_.GD.N0232.N0720.N1389.d012529
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) volume := by
  refine ⟨_root_.GD.N0232.N0720.N1389.d012530, ?_⟩
  have hmap := _root_.GD.N0232.N0720.N1389.d012531 _root_.GD.N0232.N0720.N1372.d004566
  have hfirst : _root_.GD.N0232.N0720.N1389.d012523 _root_.GD.N0232.N0720.N1372.d004566 = 1 := by
    norm_num [_root_.GD.N0232.N0720.N1389.d012523, _root_.GD.N0232.N0720.N1372.d004566]
  have hsecond : _root_.GD.N0232.N0720.N1389.d012524 _root_.GD.N0232.N0720.N1372.d004566 = 1 := by
    norm_num [_root_.GD.N0232.N0720.N1389.d012524, _root_.GD.N0232.N0720.N1372.d004566]
  rw [hfirst, hsecond] at hmap
  have href : (_root_.GD.N0232.N0720.N1080.d014172 2 2).map _root_.GD.N0232.N0720.N1389.d012529 =
      volume.withDensity (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1372.d004523 _root_.GD.N0232.N0720.N1372.d004566 x)) := by
    simpa only [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014171,
      _root_.GD.N0232.N0720.N1080.d014169, _root_.GD.N0232.N0720.N1372.d004566] using hmap
  rw [href]
  exact withDensity_absolutelyContinuous _ _



theorem d014712 {f g : _root_.GD.N0232.N0720.N1393.d004492 → ℝ}
    (hfg : f =ᵐ[volume] g) (θ : _root_.GD.N0232.N0720.N1387.d014682) :
    f ∘ _root_.GD.N0232.N0720.N1389.d012529 =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 θ] g ∘ _root_.GD.N0232.N0720.N1389.d012529 := by
  exact (_root_.GD.N0232.N0720.N1080.d014173 2 2 θ).ae_le
    (_root_.GD.N0232.N0720.N1392.d014711.ae_eq_comp hfg)

theorem d014713 (f : _root_.GD.N0232.N0720.N1393.d004492 → ℝ)
    (hf : Measurable f) (hhom : _root_.GD.N0238.N0753.d004397 f) (C : ℝ)
    (hbound : ∀ u : _root_.GD.N0232.N0720.N1393.d004493, ‖f u‖ ≤ C) (θ : _root_.GD.N0232.N0720.N1387.d014682) :
    _root_.GD.N0232.N0720.N1389.d012534 (_root_.GD.N0232.N0720.N1381.d014708 f hf C hbound) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 θ]
      f ∘ _root_.GD.N0232.N0720.N1389.d012529 :=
  _root_.GD.N0232.N0720.N1392.d014712 (_root_.GD.N0232.N0720.N1381.d014710 f hf hhom C hbound) θ





theorem d014714
    {d : _root_.GD.N0232.N0720.N1387.d014681 → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d)
    (f : _root_.GD.N0232.N0720.N1393.d004492 → ℝ) (hf : Measurable f)
    (hhom : _root_.GD.N0238.N0753.d004397 f) (C : ℝ) (hbound : ∀ u : _root_.GD.N0232.N0720.N1393.d004493, ‖f u‖ ≤ C)
    (hrep : ∀ θ : _root_.GD.N0232.N0720.N1387.d014682,
      f ∘ _root_.GD.N0232.N0720.N1389.d012529 =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 θ] d) :
    _root_.GD.N0230.N0556.d000031 _root_.GD.N0232.N0720.N1372.d004546 (_root_.GD.N0232.N0720.N1381.d014708 f hf C hbound) := by
  let h := _root_.GD.N0232.N0720.N1381.d014708 f hf C hbound
  have heq : ∀ θ : _root_.GD.N0232.N0720.N1387.d014682,
      _root_.GD.N0232.N0720.N1389.d012534 h =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 θ] d :=
    fun θ ↦ (_root_.GD.N0232.N0720.N1392.d014713 f hf hhom C hbound θ).trans (hrep θ)
  have hrisk : ∀ θ : _root_.GD.N0232.N0720.N1387.d014682,
      _root_.GD.N0232.N0720.N1080.d014197 2 2 θ (_root_.GD.N0232.N0720.N1389.d012534 h) =
        _root_.GD.N0232.N0720.N1080.d014197 2 2 θ d :=
    fun θ ↦ _root_.GD.N0232.N0720.N1159.d014662 2 2 θ (heq θ)
  apply _root_.GD.N0232.N0720.N1387.d014704
  rintro ⟨e, he, hweak, θ, hstrict⟩
  have hterm := hd.2.2.2 e he (fun q ↦ (hweak q).trans (hrisk q).le) θ
  have heRisk := _root_.GD.N0232.N0720.N1159.d014662 2 2 θ hterm
  rw [heRisk, hrisk θ] at hstrict
  exact lt_irrefl _ hstrict

end

end GD.N0232.N0720.N1392

#print axioms _root_.GD.N0232.N0720.N1392.d014712
#print axioms _root_.GD.N0232.N0720.N1392.d014714
