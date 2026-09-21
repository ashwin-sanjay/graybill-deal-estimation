import GD.Module1035
import GD.Module1036
import GD.Module1068




















































open Filter MeasureTheory Topology
open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1031

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1037
open _root_.GD.N0232.N0720.N1039
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1113
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false





theorem d017129 (x : ℝ) :
    _root_.GD.N0232.N0719.N0932.d009204 0 1 x = 1 := by
  rw [_root_.GD.N0232.N0720.N1124.d016497 0 1 x one_pos]
  simp


theorem d017130 (N : ℕ)
    (x : _root_.GD.N0137.d008894 N) :
    _root_.GD.N0232.N0719.N0932.d009213 N 0 1 x = 1 := by
  unfold _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  simp [_root_.GD.N0232.N0720.N1031.d017129]


theorem d017131 (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1499.d015001 m n _root_.GD.N0232.N0720.N1080.d014169 omega = 1 := by
  unfold _root_.GD.N0232.N0720.N1499.d015001
  simp only [_root_.GD.N0232.N0720.N1080.d014169]
  rw [_root_.GD.N0232.N0720.N1031.d017130, _root_.GD.N0232.N0720.N1031.d017130]
  ring




theorem d017132 (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega *
      _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) = 1 := by
  have h := _root_.GD.N0232.N0720.N1124.d016500 g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) omega
  rw [_root_.GD.N0232.N0720.N1215.d014279, _root_.GD.N0232.N0720.N1031.d017131] at h
  unfold _root_.GD.N0232.N0720.N1037.d016512
  linarith [h]





def d017133 (a b A M c : ℝ) : ℝ :=
  c * (b * (A - 1) + a * M) ^ 2 / _root_.GD.N0232.N0720.N1039.d016521 A c


theorem d017134 {a A M c : ℝ}
    (hA : A ≠ 0) (ht : _root_.GD.N0232.N0720.N1039.d016521 A c ≠ 0) :
    _root_.GD.N0232.N0720.N1031.d017133 a 0 A M c =
      a ^ 2 * M ^ 2 / A +
        a ^ 2 * M ^ 2 * (c - 1) / (A * _root_.GD.N0232.N0720.N1039.d016521 A c) := by
  unfold _root_.GD.N0232.N0720.N1031.d017133 _root_.GD.N0232.N0720.N1039.d016521 at *
  field_simp
  ring




theorem d017135 {a c A M T : ℝ} (hA : A ≠ 0) (hT : T ≠ 0) (ha : a ≠ 0) :
    1 / a ^ 2 * (a ^ 2 * M ^ 2 / A + a ^ 2 * M ^ 2 * (c - 1) / (A * T) -
        a ^ 2 * (M ^ 2 / A)) =
      M ^ 2 * (c - 1) / (A * T) := by
  field_simp
  ring




theorem d017136 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    Integrable (_root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 (m := m) (n := n) packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet)) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0230.N0617.d000183 (_root_.GD.N0232.N0720.N1080.d014172 m n) weight
    (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) hweight
    (_root_.GD.N0232.N0720.N1126.d016419 packet)
    (fun i ↦ _root_.GD.N0232.N0720.N1126.d016420 (m := m) (n := n) packet i)
    (fun i ↦ _root_.GD.N0232.N0720.N1126.d016421 (m := m) (n := n) packet i)




theorem d017137 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (F : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hFmeas : Measurable F)
    (hF : Integrable F (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * F (g • omega))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hG : Measurable (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g • omega) := by
    change Measurable (_root_.GD.N0107.d009024 m n g.shift g.d009239 g.d009239)
    exact _root_.GD.N0107.d009026 m n _ _ _
  have hGinv : Measurable (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g⁻¹ • omega) := by
    change Measurable
      (_root_.GD.N0107.d009024 m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239)
    exact _root_.GD.N0107.d009026 m n _ _ _

  have hmap : (_root_.GD.N0232.N0720.N1080.d014172 m n).map
        (_root_.GD.N0107.d009024 m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239) =
      _root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) :=
    _root_.GD.N0232.N0720.N1215.d014282 m n g⁻¹ _root_.GD.N0232.N0720.N1080.d014169
  have hcomp : Integrable (fun omega ↦ F (g • omega))
      (_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)) := by
    rw [← hmap]
    have hmeasF : AEStronglyMeasurable (fun omega ↦ F (g • omega))
        ((_root_.GD.N0232.N0720.N1080.d014172 m n).map
          (_root_.GD.N0107.d009024 m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239)) :=
      (hFmeas.comp hG).aestronglyMeasurable
    rw [integrable_map_measure hmeasF hGinv.aemeasurable]
    have hcancel : ∀ omega : _root_.GD.N0232.N0720.N1080.d014170 m n, g • g⁻¹ • omega = omega := by
      intro omega
      rw [smul_smul, mul_inv_cancel]
      exact one_smul _ _
    refine hF.congr ?_
    filter_upwards with omega
    show F omega = F (g • g⁻¹ • omega)
    rw [hcancel]
  rw [_root_.GD.N0232.N0720.N1499.d015006 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169),
    integrable_withDensity_iff (by fun_prop)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)] at hcomp
  refine hcomp.congr ?_
  filter_upwards with omega
  rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1499.d015003 m n _ omega)]
  show F (g • omega) * _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega = _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * F (g • omega)
  ring




theorem d017138 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (i : ι) :
    _root_.GD.N0232.N0720.N1126.d016431 s (fun k ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet k)) i =
      g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1126.d016431 s packet i := by
  unfold _root_.GD.N0232.N0720.N1126.d016431
  rw [s.riskCharacter g (packet i), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _)]




theorem d017139 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega *
        _root_.GD.N0230.N0617.d000167 weight
          (_root_.GD.N0232.N0720.N1126.d016413 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))
          (_root_.GD.N0232.N0720.N1126.d016414 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))) (g • omega) =
      _root_.GD.N0232.N0720.N1031.d017133 g.d009239 g.shift
        (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
        (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
        (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) := by
  unfold _root_.GD.N0230.N0617.d000167 _root_.GD.N0232.N0720.N1031.d017133 _root_.GD.N0232.N0720.N1039.d016521
  have hmass := _root_.GD.N0232.N0720.N1124.d016508 (m := m) (n := n) g packet weight omega
  have hmom := _root_.GD.N0232.N0720.N1124.d016509 (m := m) (n := n) g packet weight omega
  change _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega *
      (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))
          (_root_.GD.N0232.N0720.N1126.d016414 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))) (g • omega) ^ 2 /
        _root_.GD.N0232.N0720.N1126.d016415 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight (g • omega)) = _
  rw [hmass, hmom]
  have hrec := _root_.GD.N0232.N0720.N1031.d017132 g omega
  set c := _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) with hc
  set A := _root_.GD.N0232.N0720.N1126.d016415 packet weight omega with hA
  set M := _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega with hM
  set w := _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega with hw
  have hcpos : 0 < c := _root_.GD.N0232.N0720.N1499.d015005 m n _ _
  have hA1 : 1 ≤ A := _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
    (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
  have hAg : 0 < 1 + c * (A - 1) := by nlinarith
  have hwc : w = c⁻¹ := by
    have := hrec
    field_simp at this ⊢
    linarith
  rw [hwc]
  field_simp


theorem d017140 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1031.d017133 g.d009239 g.shift
      (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hmeas : Measurable (_root_.GD.N0230.N0617.d000167 weight
      (_root_.GD.N0232.N0720.N1126.d016413 (m := m) (n := n) (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))
      (_root_.GD.N0232.N0720.N1126.d016414 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))) :=
    _root_.GD.N0230.N0617.d000180 weight
      (_root_.GD.N0232.N0720.N1126.d016413 (m := m) (n := n) (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))
      (_root_.GD.N0232.N0720.N1126.d016414 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))
      (fun i ↦ _root_.GD.N0232.N0720.N1126.d016420 (m := m) (n := n) _ i)
  have hint := _root_.GD.N0232.N0720.N1031.d017137 g _ hmeas
    (_root_.GD.N0232.N0720.N1031.d017136 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight hweight)
  refine hint.congr ?_
  filter_upwards with omega
  exact _root_.GD.N0232.N0720.N1031.d017139 g packet weight hweight omega




theorem d017141 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1126.d016432 s (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight =
      g.d009239 ^ 2 * (∑ i, weight i * (_root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2 - _root_.GD.N0232.N0720.N1126.d016431 s packet i)) +
        (∑ i, weight i * (2 * g.d009239 * g.shift * _root_.GD.N0232.N0720.N1126.d016414 packet i + g.shift ^ 2)) -
        ∫ omega, _root_.GD.N0232.N0720.N1031.d017133 g.d009239 g.shift
          (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
          (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
          (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  unfold _root_.GD.N0232.N0720.N1126.d016432 _root_.GD.N0230.N0617.d000186

  have hsum : (∑ i, weight i *
      (_root_.GD.N0232.N0720.N1126.d016414 (fun k ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet k)) i ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016431 s (fun k ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet k)) i)) =
      g.d009239 ^ 2 * (∑ i, weight i * (_root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2 - _root_.GD.N0232.N0720.N1126.d016431 s packet i)) +
        (∑ i, weight i * (2 * g.d009239 * g.shift * _root_.GD.N0232.N0720.N1126.d016414 packet i + g.shift ^ 2)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [_root_.GD.N0232.N0720.N1031.d017138]
    unfold _root_.GD.N0232.N0720.N1126.d016414
    rw [_root_.GD.N0232.N0720.N1215.d014273]
    ring
  rw [hsum]
  congr 1

  have hmeas : Measurable (_root_.GD.N0230.N0617.d000167 weight
      (_root_.GD.N0232.N0720.N1126.d016413 (m := m) (n := n) (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))
      (_root_.GD.N0232.N0720.N1126.d016414 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))) :=
    _root_.GD.N0230.N0617.d000180 weight
      (_root_.GD.N0232.N0720.N1126.d016413 (m := m) (n := n) (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))
      (_root_.GD.N0232.N0720.N1126.d016414 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)))
      (fun i ↦ _root_.GD.N0232.N0720.N1126.d016420 (m := m) (n := n) _ i)
  have hG : Measurable (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g • omega) := by
    change Measurable (_root_.GD.N0107.d009024 m n g.shift g.d009239 g.d009239)
    exact _root_.GD.N0107.d009026 m n _ _ _
  rw [_root_.GD.N0232.N0720.N1037.d016519 g _ ((hmeas.comp hG).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards with omega
  exact _root_.GD.N0232.N0720.N1031.d017139 g packet weight hweight omega


theorem d017142 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1126.d016432 s packet weight -
        _root_.GD.N0232.N0720.N1126.d016432 s (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight =
      (∫ omega, _root_.GD.N0232.N0720.N1031.d017133 g.d009239 g.shift
          (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
          (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
          (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n -
        ∫ omega, _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) -
      (g.d009239 ^ 2 - 1) * (∑ i, weight i * (_root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2 - _root_.GD.N0232.N0720.N1126.d016431 s packet i)) -
      (∑ i, weight i * (2 * g.d009239 * g.shift * _root_.GD.N0232.N0720.N1126.d016414 packet i + g.shift ^ 2)) := by
  rw [_root_.GD.N0232.N0720.N1031.d017141 s g packet weight hweight]
  unfold _root_.GD.N0232.N0720.N1126.d016432 _root_.GD.N0230.N0617.d000186
  ring





def d017143 (m n : ℕ) (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) : ℝ :=
  ∫ omega,
    (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega) ^ 2 *
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) - 1) /
      (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
        _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
          (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)))
    ∂_root_.GD.N0232.N0720.N1080.d014172 m n




theorem d017144 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (hg : g.shift = 0) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hcorr : Integrable (fun omega ↦ _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet) omega) (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hexcess : Integrable (fun omega ↦
      (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega) ^ 2 *
        (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) - 1) /
        (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
          _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
            (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))))
      (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    (∫ omega, _root_.GD.N0232.N0720.N1031.d017133 g.d009239 g.shift
        (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
        (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega)
        (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      g.d009239 ^ 2 * (∫ omega, _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
          (_root_.GD.N0232.N0720.N1126.d016414 packet) omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
        g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1031.d017143 m n g packet weight := by
  unfold _root_.GD.N0232.N0720.N1031.d017143
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
    ← integral_add (hcorr.const_mul _) (hexcess.const_mul _)]
  apply integral_congr_ae
  filter_upwards with omega
  have hA1 : 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega :=
    _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
      (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
  have hcpos : 0 < _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) :=
    _root_.GD.N0232.N0720.N1499.d015005 m n _ _
  have hAne : _root_.GD.N0232.N0720.N1126.d016415 packet weight omega ≠ 0 := by linarith
  have htne : _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) ≠ 0 :=
    (_root_.GD.N0232.N0720.N1039.d016524 hA1 hcpos).ne'
  rw [hg, _root_.GD.N0232.N0720.N1031.d017134 hAne htne]
  unfold _root_.GD.N0230.N0617.d000167
  change _ = g.d009239 ^ 2 * (_ ^ 2 / _root_.GD.N0232.N0720.N1126.d016415 packet weight omega) + _
  ring


theorem d017145 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (hg : g.shift = 0) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hcorr : Integrable (fun omega ↦ _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet) omega) (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hexcess : Integrable (fun omega ↦
      (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega) ^ 2 *
        (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) - 1) /
        (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
          _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
            (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))))
      (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1126.d016432 s packet weight -
        _root_.GD.N0232.N0720.N1126.d016432 s (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight =
      (1 - g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1126.d016432 s packet weight +
        g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1031.d017143 m n g packet weight := by
  rw [_root_.GD.N0232.N0720.N1031.d017142 s g packet weight hweight,
    _root_.GD.N0232.N0720.N1031.d017144 g hg packet weight hweight hcorr hexcess]
  simp only [hg, mul_zero, zero_mul, add_zero, zero_pow (two_ne_zero), Finset.sum_const_zero]
  unfold _root_.GD.N0232.N0720.N1126.d016432 _root_.GD.N0230.N0617.d000186
  ring




theorem d017146 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (hcorr : Integrable (fun omega ↦ _root_.GD.N0230.N0617.d000167 candidate.weight
      (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet) omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hexcess : Integrable (fun omega ↦
      (_root_.GD.N0230.N0617.d000164 candidate.weight (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet)
        (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet) omega) ^ 2 *
        (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) - 1) /
        (_root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega *
          _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega)
            (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))))
      (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1126.d016432 s candidate.packet candidate.weight -
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 / g.d009239 ^ 2 ≤
      _root_.GD.N0232.N0720.N1031.d017143 m n g candidate.packet candidate.weight := by
  have hlaw := _root_.GD.N0232.N0720.N1031.d017145 s g hg candidate.packet candidate.weight
    candidate.weight_nonneg hcorr hexcess

  let image : _root_.GD.N0232.N0720.N1130.d017074 :=
    { width := candidate.width
      packet := fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (candidate.packet i)
      weight := candidate.weight
      weight_nonneg := candidate.weight_nonneg }
  have hbound := _root_.GD.N0232.N0720.N1113.d017125 m n s image
  have ha : 0 < g.d009239 ^ 2 := pow_pos g.d009240 2
  have himg : _root_.GD.N0232.N0720.N1126.d016432 s (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (candidate.packet i))
      candidate.weight = _root_.GD.N0232.N0720.N1126.d016432 s image.packet image.weight := rfl
  rw [himg] at hlaw
  set R := _root_.GD.N0232.N0720.N1126.d016432 s candidate.packet candidate.weight
  set R' := _root_.GD.N0232.N0720.N1126.d016432 s image.packet image.weight
  set E := _root_.GD.N0232.N0720.N1031.d017143 m n g candidate.packet candidate.weight
  set P := ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2
  have hR' : R' = g.d009239 ^ 2 * R - g.d009239 ^ 2 * E := by linarith
  have h1 : g.d009239 ^ 2 * (R - E) ≤ P := by
    rw [hR'] at hbound
    linarith
  have h2 : R - E ≤ P / g.d009239 ^ 2 := by
    rw [le_div_iff₀ ha]
    linarith [h1]
  linarith [h2]





theorem d017147 (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    Integrable (fun omega ↦
      (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega) ^ 2 *
        (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) - 1) /
        (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
          _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
            (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega))))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have ha : (0 : ℝ) < g.d009239 ^ 2 := pow_pos g.d009240 2
  have htcd := _root_.GD.N0232.N0720.N1031.d017140 (m := m) (n := n) g packet weight hweight
  have hcorr := _root_.GD.N0232.N0720.N1031.d017136 (m := m) (n := n) packet weight hweight
  have hdiff := (htcd.sub (hcorr.const_mul (g.d009239 ^ 2))).const_mul (1 / g.d009239 ^ 2)
  refine hdiff.congr ?_
  filter_upwards with omega
  have hA1 : 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet weight omega :=
    _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
      (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
  have hcpos : 0 < _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) :=
    _root_.GD.N0232.N0720.N1499.d015005 m n _ _
  have hAne : _root_.GD.N0232.N0720.N1126.d016415 packet weight omega ≠ 0 := by linarith
  have htne : _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)) ≠ 0 :=
    (_root_.GD.N0232.N0720.N1039.d016524 hA1 hcpos).ne'
  show 1 / g.d009239 ^ 2 * (_root_.GD.N0232.N0720.N1031.d017133 g.d009239 g.shift _ _ _ -
      g.d009239 ^ 2 * _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega) = _
  rw [hg, _root_.GD.N0232.N0720.N1031.d017134 hAne htne]
  unfold _root_.GD.N0230.N0617.d000167
  exact _root_.GD.N0232.N0720.N1031.d017135 hAne htne g.d009240.ne'


theorem d017148 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (hg : g.shift = 0) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1126.d016432 s packet weight -
        _root_.GD.N0232.N0720.N1126.d016432 s (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight =
      (1 - g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1126.d016432 s packet weight +
        g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1031.d017143 m n g packet weight :=
  _root_.GD.N0232.N0720.N1031.d017145 s g hg packet weight hweight
    (_root_.GD.N0232.N0720.N1031.d017136 (m := m) (n := n) packet weight hweight)
    (_root_.GD.N0232.N0720.N1031.d017147 (m := m) (n := n) g hg packet weight hweight)




theorem d017149 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1126.d016432 s candidate.packet candidate.weight -
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 / g.d009239 ^ 2 ≤
      _root_.GD.N0232.N0720.N1031.d017143 m n g candidate.packet candidate.weight :=
  _root_.GD.N0232.N0720.N1031.d017146 s g hg candidate
    (_root_.GD.N0232.N0720.N1031.d017136 (m := m) (n := n) candidate.packet candidate.weight
      candidate.weight_nonneg)
    (_root_.GD.N0232.N0720.N1031.d017147 (m := m) (n := n) g hg candidate.packet candidate.weight
      candidate.weight_nonneg)





theorem d017150 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (hg : g.shift = 0) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1126.d016432 s (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight =
        _root_.GD.N0232.N0720.N1126.d016432 s packet weight ↔
      g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1031.d017143 m n g packet weight =
        (g.d009239 ^ 2 - 1) * _root_.GD.N0232.N0720.N1126.d016432 s packet weight := by
  have hlaw := _root_.GD.N0232.N0720.N1031.d017148 s g hg packet weight hweight
  constructor
  · intro h
    linear_combination -hlaw - h
  · intro h
    linear_combination -hlaw - h


theorem d017151 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0) (hg2 : g.d009239 = 2)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1126.d016432 s (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) weight =
        _root_.GD.N0232.N0720.N1126.d016432 s packet weight ↔
      4 * _root_.GD.N0232.N0720.N1031.d017143 m n g packet weight = 3 * _root_.GD.N0232.N0720.N1126.d016432 s packet weight := by
  rw [_root_.GD.N0232.N0720.N1031.d017150 s g hg packet weight hweight, hg2]
  norm_num





theorem d017152 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hR : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
      atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)))
    (hstable : Tendsto (fun j ↦
      _root_.GD.N0232.N0720.N1126.d016432 s (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i))
          (candidate j).weight -
        _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight) atTop (𝓝 0)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1031.d017143 m n g (candidate j).packet (candidate j).weight) atTop
      (𝓝 ((1 - 1 / g.d009239 ^ 2) * ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)) := by
  have ha : g.d009239 ^ 2 ≠ 0 := (pow_pos g.d009240 2).ne'
  have hform : ∀ j, _root_.GD.N0232.N0720.N1031.d017143 m n g (candidate j).packet (candidate j).weight =
      ((g.d009239 ^ 2 - 1) *
          _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight -
        (_root_.GD.N0232.N0720.N1126.d016432 s (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i))
            (candidate j).weight -
          _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)) /
        g.d009239 ^ 2 := by
    intro j
    have hlaw := _root_.GD.N0232.N0720.N1031.d017148 s g hg (candidate j).packet (candidate j).weight
      (candidate j).weight_nonneg
    rw [eq_div_iff ha]
    linear_combination (-1 : ℝ) * hlaw
  have hval : (1 - 1 / g.d009239 ^ 2) * ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 =
      ((g.d009239 ^ 2 - 1) * ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 - 0) / g.d009239 ^ 2 := by
    field_simp
    ring
  simp only [hform]
  rw [hval]
  exact ((hR.const_mul (g.d009239 ^ 2 - 1)).sub hstable).div_const (g.d009239 ^ 2)

end

end N1031
end N0720
end N0232
end GD
