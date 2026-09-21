import GD.Module0960
import GD.Module1030



















open Filter MeasureTheory
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1054

noncomputable section

open _root_.GD.N0232.N0720.N1068
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

private noncomputable local instance d016438 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance


def d016439 (t : ℝ) : _root_.GD.N0232.N0719.N0946.d009229 where
  shift := t
  logScale := 0

@[simp] theorem d016440 (t : ℝ) :
    (_root_.GD.N0232.N0720.N1054.d016439 t).shift = t := rfl

@[simp] theorem d016441 (t : ℝ) :
    (_root_.GD.N0232.N0720.N1054.d016439 t).d009239 = 1 := by
  simp [_root_.GD.N0232.N0720.N1054.d016439, _root_.GD.N0232.N0719.N0946.d009229.d009239]







theorem d016442
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (B : ℝ)
    (hp : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, |p omega| ≤ B) :
    ¬ _root_.GD.N0232.N0720.N1159.d014652 m n p := by
  intro hrep
  obtain ⟨repaired, _hrepairedMeasurable, hrepairedClass,
    hrepairedEquivariant⟩ := hrep
  have hclassReference :
      repaired =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1214.d014265 m n p := by
    simpa [_root_.GD.N0232.N0720.N1080.d014172] using
      hrepairedClass (_root_.GD.N0232.N0720.N1080.d014169 : _root_.GD.N0232.N0720.N1080.d014168)
  have hrepairedReference :
      repaired =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] fun omega ↦ p omega := by
    exact hclassReference.trans
      (_root_.GD.N0232.N0720.N1214.d014267 m n p)
  have hrepairedBound :
      ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, |repaired omega| ≤ B := by
    filter_upwards [hrepairedReference, hp] with omega hclass hbound
    simpa [hclass] using hbound
  let g : _root_.GD.N0232.N0719.N0946.d009229 := _root_.GD.N0232.N0720.N1054.d016439 (2 * B + 1)
  have htranslatedBound :
      ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, |repaired (g • omega)| ≤ B :=
    (_root_.GD.N0232.N0720.N1068.d015083 m n g).ae
      hrepairedBound
  obtain ⟨omega, homega, htranslated⟩ :=
    (hrepairedBound.and htranslatedBound).exists
  have hequivariant := hrepairedEquivariant g omega
  have hright : |2 * B + 1 + repaired omega| ≤ B := by
    rw [hequivariant] at htranslated
    simpa [g, _root_.GD.N0232.N0720.N1054.d016439, _root_.GD.N0232.N0719.N0946.d009229.d009244,
      _root_.GD.N0232.N0719.N0946.d009229.d009239] using htranslated
  have homegaBounds := abs_le.mp homega
  have hrightBounds := abs_le.mp hright
  linarith



theorem d016443
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n p)
    (B : ℝ) :
    ¬ (∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, |p omega| ≤ B) := by
  exact fun hp ↦
    _root_.GD.N0232.N0720.N1054.d016442
      p B hp hrep





theorem d016444
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight omega| ≤
        _root_.GD.N0232.N0720.N1126.d016418 packet := by
  filter_upwards [_root_.GD.N0232.N0720.N1126.d016427
      packet weight hweight] with omega hclass
  rw [hclass]
  exact _root_.GD.N0232.N0720.N1126.d016424
    packet weight hweight omega



theorem d016445
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    ¬ _root_.GD.N0232.N0720.N1159.d014652 m n
      (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight) := by
  exact _root_.GD.N0232.N0720.N1054.d016442
    (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight)
    (_root_.GD.N0232.N0720.N1126.d016418 packet)
    (_root_.GD.N0232.N0720.N1054.d016444 packet weight hweight)



theorem d016446
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1159.d014637 m n
        (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight) ∧
      ¬ _root_.GD.N0232.N0720.N1159.d014652 m n
        (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight) := by
  exact ⟨_root_.GD.N0232.N0720.N1126.d016428 packet weight hweight,
    _root_.GD.N0232.N0720.N1054.d016445
      packet weight hweight⟩





theorem d016447
    (pseq : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (B : ℝ)
    (hconv : Tendsto pseq atTop (nhds p))
    (hbound : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |pseq j omega| ≤ B) :
    ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, |p omega| ≤ B := by
  obtain ⟨subseq, _hsubseq, hpointwise⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  filter_upwards [hpointwise, eventually_countable_forall.mpr hbound] with
      omega homega hbounds
  have habsConv :
      Tendsto (fun j ↦ |pseq (subseq j) omega|) atTop
        (nhds |p omega|) :=
    (continuous_abs.tendsto (p omega)).comp homega
  exact le_of_tendsto' habsConv (fun j ↦ hbounds (subseq j))




theorem d016448
    (pseq : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hconv : Tendsto pseq atTop (nhds p))
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n p)
    (B : ℝ) :
    ∃ j, ¬ (∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, |pseq j omega| ≤ B) := by
  by_contra hescape
  push Not at hescape
  have hpBound := _root_.GD.N0232.N0720.N1054.d016447
    pseq p B hconv hescape
  exact
    (_root_.GD.N0232.N0720.N1054.d016443
      p hrep B) hpBound




theorem d016449
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ℕ → ι → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hconv : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j)
        (hweight j)) atTop (nhds p))
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n p)
    (B : ℝ) :
    ∃ j, B < _root_.GD.N0232.N0720.N1126.d016418 (packet j) := by
  by_contra hescape
  push Not at hescape
  have huniform : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j) omega| ≤
        B := by
    intro j
    filter_upwards [_root_.GD.N0232.N0720.N1054.d016444
        (packet j) (weight j) (hweight j)] with omega hpacket
    exact hpacket.trans (hescape j)
  have hpBound : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, |p omega| ≤ B :=
    _root_.GD.N0232.N0720.N1054.d016447
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j)
        (hweight j)) p B hconv huniform
  exact
    (_root_.GD.N0232.N0720.N1054.d016443
      p hrep B) hpBound

end

end N1054
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1054.d016442
#print axioms _root_.GD.N0232.N0720.N1054.d016445
#print axioms _root_.GD.N0232.N0720.N1054.d016446
#print axioms _root_.GD.N0232.N0720.N1054.d016447
#print axioms _root_.GD.N0232.N0720.N1054.d016448
#print axioms _root_.GD.N0232.N0720.N1054.d016449
