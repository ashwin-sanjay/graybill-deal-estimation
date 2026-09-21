import GD.Module1031
import GD.Module1067
import GD.Module1075
























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1055

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1054
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1105
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1128
open _root_.GD.N0232.N0720.N1137
open _root_.GD.N0232.N0720.N1139
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

private noncomputable local instance d017237 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance










theorem d017238
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (B : ℝ)
    (hp : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, |p omega| ≤ B) :
    ¬ _root_.GD.N0232.N0720.N1159.d014638 m n p := by
  intro hcharacter
  let R : ℝ := (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p).toReal
  let M : ℝ := R + 1
  let a : ℝ := B + M
  let theta : _root_.GD.N0232.N0720.N1080.d014168 :=
    _root_.GD.N0232.N0720.N1215.d014272 (_root_.GD.N0232.N0720.N1054.d016439 a) _root_.GD.N0232.N0720.N1080.d014169

  have hR : 0 ≤ R := ENNReal.toReal_nonneg
  have hMpos : 0 < M := by
    dsimp only [M]
    linarith
  have hR_lt_M_sq : R < M ^ 2 := by
    dsimp only [M]
    nlinarith [sq_nonneg R]
  have hthetaLocation : theta.location = a := by
    simp [theta, _root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0720.N1080.d014169, _root_.GD.N0232.N0720.N1054.d016439]

  have hriskCharacter :
      _root_.GD.N0232.N0720.N1080.d014182 m n theta p = _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p := by
    have hraw := hcharacter (_root_.GD.N0232.N0720.N1054.d016439 a) _root_.GD.N0232.N0720.N1080.d014169
    simpa [theta, _root_.GD.N0232.N0720.N1054.d016439, _root_.GD.N0232.N0719.N0946.d009229.d009239] using hraw
  have hrefFinite : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p ≠ ⊤ := by
    rw [_root_.GD.N0232.N0720.N1080.d014190]
    exact ENNReal.ofReal_ne_top
  have hthetaFinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≠ ⊤ := by
    rw [hriskCharacter]
    exact hrefFinite

  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    unfold _root_.GD.N0232.N0720.N1080.d014171
    infer_instance

  have hpTheta : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta, |p omega| ≤ B :=
    (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le hp
  have herrorIntegrable : Integrable
      (fun omega ↦ (p omega - theta.location) ^ 2) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
    _root_.GD.N0232.N0720.N1078.d016376 m n theta p hthetaFinite
  have hriskLower : M ^ 2 ≤ (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal := by
    rw [_root_.GD.N0232.N0720.N1128.d017097 m n theta p hthetaFinite]
    have hconst : Integrable (fun _ : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ M ^ 2)
        (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := integrable_const _
    have hpoint : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta,
        M ^ 2 ≤ (p omega - theta.location) ^ 2 := by
      filter_upwards [hpTheta] with omega hbound
      have hpUpper : p omega ≤ B := (abs_le.mp hbound).2
      have hdiff : M ≤ a - p omega := by
        dsimp only [a]
        linarith
      have hprod :
          0 ≤ (a - p omega - M) * (a - p omega + M) :=
        mul_nonneg (sub_nonneg.mpr hdiff)
          (add_nonneg (hMpos.le.trans hdiff) hMpos.le)
      rw [hthetaLocation]
      nlinarith
    have hintegral := integral_mono_ae hconst herrorIntegrable hpoint
    simpa using hintegral
  have hriskReal : (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal = R := by
    rw [hriskCharacter]
  rw [hriskReal] at hriskLower
  exact (not_lt_of_ge hriskLower) hR_lt_M_sq




theorem d017239
    (kappa : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (B : ℝ)
    (hp : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, |p omega| ≤ B) :
    ¬ (p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value ∧
      _root_.GD.N0232.N0720.N1159.d014638 m n p ∧
      _root_.GD.N0232.N0720.N1105.d017112 m n p s.value ∧
      ‖p‖ ^ 2 ≤ ‖s.value‖ ^ 2 -
        kappa * _root_.GD.N0232.N0720.N1201.d015333 m n s) := by
  intro hwitness
  exact (_root_.GD.N0232.N0720.N1055.d017238 p B hp) hwitness.2.1





theorem d017240
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    ¬ _root_.GD.N0232.N0720.N1159.d014638 m n
      (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight) := by
  exact _root_.GD.N0232.N0720.N1055.d017238
    (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight)
    (_root_.GD.N0232.N0720.N1126.d016418 packet)
    (_root_.GD.N0232.N0720.N1054.d016444 packet weight hweight)



theorem d017241
    (kappa : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    ¬ (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          packet weight hweight ∈
          _root_.GD.N0232.N0720.N1159.d014630 m n s.value ∧
      _root_.GD.N0232.N0720.N1159.d014638 m n
        (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          packet weight hweight) ∧
      _root_.GD.N0232.N0720.N1105.d017112 m n
        (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          packet weight hweight) s.value ∧
      ‖_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          packet weight hweight‖ ^ 2 ≤
        ‖s.value‖ ^ 2 - kappa * _root_.GD.N0232.N0720.N1201.d015333 m n s) := by
  exact _root_.GD.N0232.N0720.N1055.d017239 kappa s
    (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight)
    (_root_.GD.N0232.N0720.N1126.d016418 packet)
    (_root_.GD.N0232.N0720.N1054.d016444 packet weight hweight)



theorem d017242
    {k : ℕ} (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (hdelta : 0 < delta) :
    ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1139.d017218 s packet delta omega| ≤
        _root_.GD.N0232.N0720.N1126.d016418 packet := by
  obtain ⟨weight, hweight, hprojection, _hreserve,
    _hcomplementarity⟩ :=
    _root_.GD.N0232.N0720.N1139.d017229
      s packet delta hdelta
  rw [hprojection]
  exact _root_.GD.N0232.N0720.N1054.d016444 packet weight hweight



theorem d017243
    {k : ℕ} (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168)
    (delta : NNReal) (hdelta : 0 < delta) :
    ¬ _root_.GD.N0232.N0720.N1159.d014638 m n
      (_root_.GD.N0232.N0720.N1139.d017218 s packet delta) := by
  exact _root_.GD.N0232.N0720.N1055.d017238
    (_root_.GD.N0232.N0720.N1139.d017218 s packet delta)
    (_root_.GD.N0232.N0720.N1126.d016418 packet)
    (_root_.GD.N0232.N0720.N1055.d017242 s packet delta hdelta)




theorem d017244
    {k : ℕ} (kappa : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : Fin k → _root_.GD.N0232.N0720.N1080.d014168) (delta : NNReal) (hdelta : 0 < delta) :
    ¬ (_root_.GD.N0232.N0720.N1139.d017218 s packet delta ∈
          _root_.GD.N0232.N0720.N1159.d014630 m n s.value ∧
      _root_.GD.N0232.N0720.N1159.d014638 m n
        (_root_.GD.N0232.N0720.N1139.d017218 s packet delta) ∧
      _root_.GD.N0232.N0720.N1105.d017112 m n
        (_root_.GD.N0232.N0720.N1139.d017218 s packet delta) s.value ∧
      ‖_root_.GD.N0232.N0720.N1139.d017218 s packet delta‖ ^ 2 ≤
        ‖s.value‖ ^ 2 - kappa * _root_.GD.N0232.N0720.N1201.d015333 m n s) := by
  exact _root_.GD.N0232.N0720.N1055.d017239 kappa s
    (_root_.GD.N0232.N0720.N1139.d017218 s packet delta)
    (_root_.GD.N0232.N0720.N1126.d016418 packet)
    (_root_.GD.N0232.N0720.N1055.d017242 s packet delta hdelta)



theorem d017245
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (N : ℕ) :
    ¬ _root_.GD.N0232.N0720.N1159.d014638 m n
      (_root_.GD.N0232.N0720.N1139.d017232 s N) := by
  unfold _root_.GD.N0232.N0720.N1139.d017232
  exact _root_.GD.N0232.N0720.N1055.d017243
    s (_root_.GD.N0232.N0720.N1139.d017231 N) (_root_.GD.N0232.N0720.N1137.d017205 N)
      (_root_.GD.N0232.N0720.N1139.d017233 N)







theorem d017246
    (pseq : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hconv : Tendsto pseq atTop (nhds p))
    (hcharacter : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (B : ℝ) :
    ∃ j, ¬ (∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, |pseq j omega| ≤ B) := by
  by_contra hescape
  push Not at hescape
  have hpBound := _root_.GD.N0232.N0720.N1054.d016447
    pseq p B hconv hescape
  exact (_root_.GD.N0232.N0720.N1055.d017238 p B hpBound) hcharacter




theorem d017247
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ℕ → ι → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hconv : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j)
        (hweight j)) atTop (nhds p))
    (hcharacter : _root_.GD.N0232.N0720.N1159.d014638 m n p)
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
  exact (_root_.GD.N0232.N0720.N1055.d017238 p B hpBound) hcharacter

end

end N1055
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1055.d017238
#print axioms _root_.GD.N0232.N0720.N1055.d017240
#print axioms _root_.GD.N0232.N0720.N1055.d017243
#print axioms _root_.GD.N0232.N0720.N1055.d017247
