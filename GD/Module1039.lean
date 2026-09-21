import GD.Module0047
import GD.Module1034
import Mathlib.Topology.Bases














open Filter MeasureTheory Set Topology
open scoped ENNReal BigOperators Topology

namespace GD
namespace N0232
namespace N0720
namespace N1133

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0591
open _root_.GD.N0230.N0598
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0685
open _root_.GD.N0232.N0719.N0932

variable {m n : ℕ}





noncomputable instance d016564 :
    SecondCountableTopology _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1499.d014996.isEmbedding.secondCountableTopology

instance d016565 : Nonempty _root_.GD.N0232.N0720.N1080.d014168 :=
  ⟨_root_.GD.N0232.N0720.N1080.d014169⟩



noncomputable def d016566 : ℕ → _root_.GD.N0232.N0720.N1080.d014168 :=
  TopologicalSpace.denseSeq _root_.GD.N0232.N0720.N1080.d014168

theorem d016567 :
    DenseRange _root_.GD.N0232.N0720.N1133.d016566 := by
  change DenseRange (TopologicalSpace.denseSeq _root_.GD.N0232.N0720.N1080.d014168)
  exact TopologicalSpace.denseRange_denseSeq _root_.GD.N0232.N0720.N1080.d014168





theorem d016568
    (location anchor scale anchorScale x : ℝ)
    (hscale : 0 < scale) (hanchor : scale < anchorScale) :
    (x - anchor) ^ 2 / (2 * anchorScale ^ 2) -
        (x - location) ^ 2 / (2 * scale ^ 2) ≤
      (location - anchor) ^ 2 /
        (2 * (anchorScale ^ 2 - scale ^ 2)) := by
  have hanchor_pos : 0 < anchorScale := lt_trans hscale hanchor
  have hgap : 0 < anchorScale ^ 2 - scale ^ 2 := by
    nlinarith [sq_nonneg (anchorScale - scale)]
  have hidentity :
      (location - anchor) ^ 2 /
            (2 * (anchorScale ^ 2 - scale ^ 2)) -
          ((x - anchor) ^ 2 / (2 * anchorScale ^ 2) -
            (x - location) ^ 2 / (2 * scale ^ 2)) =
        (((anchorScale ^ 2 - scale ^ 2) * x -
              (anchorScale ^ 2 * location - scale ^ 2 * anchor)) ^ 2) /
          (2 * anchorScale ^ 2 * scale ^ 2 *
            (anchorScale ^ 2 - scale ^ 2)) := by
    field_simp [hscale.ne', hanchor_pos.ne', hgap.ne']
    ring
  apply sub_nonneg.mp
  rw [hidentity]
  positivity



theorem d016569
    (location anchor scale anchorScale x : ℝ)
    (hscale : 0 < scale) (hanchor : scale < anchorScale) :
    _root_.GD.N0232.N0719.N0932.d009204 location scale x ≤
      (anchorScale / scale) *
          Real.exp ((location - anchor) ^ 2 /
            (2 * (anchorScale ^ 2 - scale ^ 2))) *
        _root_.GD.N0232.N0719.N0932.d009204 anchor anchorScale x := by
  have hanchor_pos : 0 < anchorScale := lt_trans hscale hanchor
  rw [_root_.GD.N0232.N0720.N1124.d016497
      location scale x hscale,
    _root_.GD.N0232.N0720.N1124.d016497
      anchor anchorScale x hanchor_pos]
  have hexponent :
      x ^ 2 / 2 - (x - location) ^ 2 / (2 * scale ^ 2) ≤
        (location - anchor) ^ 2 /
            (2 * (anchorScale ^ 2 - scale ^ 2)) +
          (x ^ 2 / 2 - (x - anchor) ^ 2 /
            (2 * anchorScale ^ 2)) := by
    have hrelative := _root_.GD.N0232.N0720.N1133.d016568
      location anchor scale anchorScale x hscale hanchor
    linarith
  calc
    scale⁻¹ * Real.exp
          (x ^ 2 / 2 - (x - location) ^ 2 / (2 * scale ^ 2)) ≤
        scale⁻¹ * Real.exp
          ((location - anchor) ^ 2 /
              (2 * (anchorScale ^ 2 - scale ^ 2)) +
            (x ^ 2 / 2 - (x - anchor) ^ 2 /
              (2 * anchorScale ^ 2))) := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hexponent) (inv_nonneg.mpr hscale.le)
    _ = (anchorScale / scale) *
          Real.exp ((location - anchor) ^ 2 /
            (2 * (anchorScale ^ 2 - scale ^ 2))) *
        (anchorScale⁻¹ * Real.exp
          (x ^ 2 / 2 - (x - anchor) ^ 2 /
            (2 * anchorScale ^ 2))) := by
      rw [Real.exp_add]
      field_simp [hscale.ne', hanchor_pos.ne']



def d016570 : ℝ := 8 * Real.exp 1

theorem d016571 : 0 < _root_.GD.N0232.N0720.N1133.d016570 := by
  unfold _root_.GD.N0232.N0720.N1133.d016570
  positivity





theorem d016572
    (location anchor scale centralScale x : ℝ)
    (hcentral : 0 < centralScale)
    (hscale_lower : centralScale / 2 < scale)
    (hscale_upper : scale < 2 * centralScale)
    (hlocation : |location - anchor| < centralScale) :
    _root_.GD.N0232.N0719.N0932.d009204 location scale x ≤
      _root_.GD.N0232.N0720.N1133.d016570 *
        _root_.GD.N0232.N0719.N0932.d009204 anchor (4 * centralScale) x := by
  have hscale : 0 < scale := by linarith
  have hwide : scale < 4 * centralScale := by linarith
  have hratio : (4 * centralScale) / scale ≤ 8 := by
    rw [div_le_iff₀ hscale]
    linarith
  have hscale_sq : scale ^ 2 < (2 * centralScale) ^ 2 := by
    have hleft : 0 < 2 * centralScale - scale := by linarith
    have hright : 0 < 2 * centralScale + scale := by positivity
    nlinarith [mul_pos hleft hright]
  have hlocation_sq : (location - anchor) ^ 2 < centralScale ^ 2 := by
    rcases abs_lt.mp hlocation with ⟨hlower, hupper⟩
    have hleft : 0 < centralScale - (location - anchor) := by linarith
    have hright : 0 < centralScale + (location - anchor) := by linarith
    nlinarith [mul_pos hleft hright]
  have hdenominator :
      0 < 2 * ((4 * centralScale) ^ 2 - scale ^ 2) := by
    nlinarith [sq_pos_of_pos hcentral]
  have hexponent :
      (location - anchor) ^ 2 /
          (2 * ((4 * centralScale) ^ 2 - scale ^ 2)) ≤ 1 := by
    rw [div_le_one₀ hdenominator]
    nlinarith [sq_pos_of_pos hcentral]
  have hcoefficient :
      ((4 * centralScale) / scale) *
          Real.exp ((location - anchor) ^ 2 /
            (2 * ((4 * centralScale) ^ 2 - scale ^ 2))) ≤
        _root_.GD.N0232.N0720.N1133.d016570 := by
    unfold _root_.GD.N0232.N0720.N1133.d016570
    exact mul_le_mul hratio (Real.exp_le_exp.mpr hexponent)
      (Real.exp_pos _).le (by norm_num)
  calc
    _root_.GD.N0232.N0719.N0932.d009204 location scale x ≤
        ((4 * centralScale) / scale) *
            Real.exp ((location - anchor) ^ 2 /
              (2 * ((4 * centralScale) ^ 2 - scale ^ 2))) *
          _root_.GD.N0232.N0719.N0932.d009204 anchor (4 * centralScale) x :=
      _root_.GD.N0232.N0720.N1133.d016569
        location anchor scale (4 * centralScale) x hscale hwide
    _ ≤ _root_.GD.N0232.N0720.N1133.d016570 *
          _root_.GD.N0232.N0719.N0932.d009204 anchor (4 * centralScale) x :=
      mul_le_mul_of_nonneg_right hcoefficient
        (_root_.GD.N0232.N0719.N0932.d009205 anchor (4 * centralScale) x)



theorem d016573
    (sampleSize : ℕ) (location anchor scale centralScale : ℝ)
    (hcentral : 0 < centralScale)
    (hscale_lower : centralScale / 2 < scale)
    (hscale_upper : scale < 2 * centralScale)
    (hlocation : |location - anchor| < centralScale)
    (x : _root_.GD.N0137.d008894 sampleSize) :
    _root_.GD.N0232.N0719.N0932.d009213 sampleSize location scale x ≤
      _root_.GD.N0232.N0720.N1133.d016570 ^ sampleSize *
        _root_.GD.N0232.N0719.N0932.d009213 sampleSize anchor
          (4 * centralScale) x := by
  unfold _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  calc
    (∏ i : Fin sampleSize, _root_.GD.N0232.N0719.N0932.d009204 location scale (x i)) ≤
        ∏ i : Fin sampleSize,
          (_root_.GD.N0232.N0720.N1133.d016570 *
            _root_.GD.N0232.N0719.N0932.d009204 anchor (4 * centralScale) (x i)) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact _root_.GD.N0232.N0719.N0932.d009205 location scale (x i)
      · intro i hi
        exact _root_.GD.N0232.N0720.N1133.d016572
          location anchor scale centralScale (x i) hcentral
          hscale_lower hscale_upper hlocation
    _ = _root_.GD.N0232.N0720.N1133.d016570 ^ sampleSize *
          ∏ i : Fin sampleSize,
            _root_.GD.N0232.N0719.N0932.d009204 anchor (4 * centralScale) (x i) := by
      rw [Finset.prod_mul_distrib]
      simp





def d016574 (theta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := theta.location
  scale₁ := 4 * theta.scale₁
  scale₂ := 4 * theta.scale₂
  scale₁_pos := mul_pos (by norm_num) theta.scale₁_pos
  scale₂_pos := mul_pos (by norm_num) theta.scale₂_pos


def d016575 (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  min theta.scale₁ theta.scale₂

theorem d016576 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0232.N0720.N1133.d016575 theta := by
  exact lt_min theta.scale₁_pos theta.scale₂_pos



def d016577 (theta : _root_.GD.N0232.N0720.N1080.d014168) : Set _root_.GD.N0232.N0720.N1080.d014168 :=
  {eta | theta.scale₁ / 2 < eta.scale₁} ∩
  {eta | eta.scale₁ < 2 * theta.scale₁} ∩
  {eta | theta.scale₂ / 2 < eta.scale₂} ∩
  {eta | eta.scale₂ < 2 * theta.scale₂} ∩
  {eta | |eta.location - theta.location| < _root_.GD.N0232.N0720.N1133.d016575 theta}

theorem d016578 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    IsOpen (_root_.GD.N0232.N0720.N1133.d016577 theta) := by
  unfold _root_.GD.N0232.N0720.N1133.d016577
  exact
    ((((isOpen_lt continuous_const _root_.GD.N0232.N0720.N1499.d014999).inter
      (isOpen_lt _root_.GD.N0232.N0720.N1499.d014999 continuous_const)).inter
      (isOpen_lt continuous_const _root_.GD.N0232.N0720.N1499.d015000)).inter
      (isOpen_lt _root_.GD.N0232.N0720.N1499.d015000 continuous_const)).inter
      (isOpen_lt
        (_root_.GD.N0232.N0720.N1499.d014998.sub continuous_const).abs
        continuous_const)

theorem d016579 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    theta ∈ _root_.GD.N0232.N0720.N1133.d016577 theta := by
  have hradius := _root_.GD.N0232.N0720.N1133.d016576 theta
  simp only [_root_.GD.N0232.N0720.N1133.d016577, mem_inter_iff, mem_setOf_eq,
    sub_self, abs_zero]
  constructor
  · constructor
    · constructor
      · constructor <;> linarith [theta.scale₁_pos]
      · linarith [theta.scale₂_pos]
    · linarith [theta.scale₂_pos]
  · exact hradius

theorem d016580 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1133.d016577 theta ∈ nhds theta :=
  (_root_.GD.N0232.N0720.N1133.d016578 theta).mem_nhds
    (_root_.GD.N0232.N0720.N1133.d016579 theta)



theorem d016581
    (m n : ℕ) (theta eta : _root_.GD.N0232.N0720.N1080.d014168)
    (heta : eta ∈ _root_.GD.N0232.N0720.N1133.d016577 theta)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1499.d015001 m n eta omega ≤
      _root_.GD.N0232.N0720.N1133.d016570 ^ (m + n) *
        _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1133.d016574 theta) omega := by
  rcases heta with ⟨⟨⟨⟨hscale₁_lower, hscale₁_upper⟩,
    hscale₂_lower⟩, hscale₂_upper⟩, hlocation⟩
  have hlocation₁ :
      |eta.location - theta.location| < theta.scale₁ :=
    lt_of_lt_of_le hlocation (min_le_left _ _)
  have hlocation₂ :
      |eta.location - theta.location| < theta.scale₂ :=
    lt_of_lt_of_le hlocation (min_le_right _ _)
  have hfirst := _root_.GD.N0232.N0720.N1133.d016573
    m eta.location theta.location eta.scale₁ theta.scale₁
    theta.scale₁_pos hscale₁_lower hscale₁_upper hlocation₁ omega.1
  have hsecond := _root_.GD.N0232.N0720.N1133.d016573
    n eta.location theta.location eta.scale₂ theta.scale₂
    theta.scale₂_pos hscale₂_lower hscale₂_upper hlocation₂ omega.2
  unfold _root_.GD.N0232.N0720.N1499.d015001 _root_.GD.N0232.N0720.N1133.d016574 at *
  calc
    _root_.GD.N0232.N0719.N0932.d009213 m eta.location eta.scale₁ omega.1 *
        _root_.GD.N0232.N0719.N0932.d009213 n eta.location eta.scale₂ omega.2 ≤
      (_root_.GD.N0232.N0720.N1133.d016570 ^ m *
          _root_.GD.N0232.N0719.N0932.d009213 m theta.location
            (4 * theta.scale₁) omega.1) *
        (_root_.GD.N0232.N0720.N1133.d016570 ^ n *
          _root_.GD.N0232.N0719.N0932.d009213 n theta.location
            (4 * theta.scale₂) omega.2) := by
      exact mul_le_mul hfirst hsecond
        (_root_.GD.N0232.N0719.N0932.d009215
          n eta.location eta.scale₂ omega.2)
        (mul_nonneg (pow_nonneg _root_.GD.N0232.N0720.N1133.d016571.le _)
          (_root_.GD.N0232.N0719.N0932.d009215
            m theta.location (4 * theta.scale₁) omega.1))
    _ = _root_.GD.N0232.N0720.N1133.d016570 ^ (m + n) *
        (_root_.GD.N0232.N0719.N0932.d009213 m theta.location
            (4 * theta.scale₁) omega.1 *
          _root_.GD.N0232.N0719.N0932.d009213 n theta.location
            (4 * theta.scale₂) omega.2) := by
      rw [pow_add]
      ring




def d016582
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  (2 * _root_.GD.N0232.N0720.N1133.d016570 ^ (m + n)) *
    (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1133.d016574 theta) omega *
        (q omega - theta.location) ^ 2 +
      _root_.GD.N0232.N0720.N1133.d016575 theta ^ 2 *
        _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1133.d016574 theta) omega)

theorem d016583
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1133.d016582 m n theta q omega := by
  unfold _root_.GD.N0232.N0720.N1133.d016582
  apply mul_nonneg
  · exact mul_nonneg (by norm_num)
      (pow_nonneg _root_.GD.N0232.N0720.N1133.d016571.le _)
  · exact add_nonneg
      (mul_nonneg
        (_root_.GD.N0232.N0720.N1499.d015003 m n
          (_root_.GD.N0232.N0720.N1133.d016574 theta) omega)
        (sq_nonneg _))
      (mul_nonneg (sq_nonneg _)
        (_root_.GD.N0232.N0720.N1499.d015003 m n
          (_root_.GD.N0232.N0720.N1133.d016574 theta) omega))



theorem d016584
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q) :
    Integrable (_root_.GD.N0232.N0720.N1133.d016582 m n theta q) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hweighted : Integrable (fun omega ↦
      _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1133.d016574 theta) omega *
        (q omega - theta.location) ^ 2) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    simpa [_root_.GD.N0232.N0720.N1133.d016574] using
      _root_.GD.N0232.N0720.N1126.d016429
        (m := m) (n := n) (_root_.GD.N0232.N0720.N1133.d016574 theta) q
          (hq (_root_.GD.N0232.N0720.N1133.d016574 theta))
  have hlikelihood : Integrable
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1133.d016574 theta))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1484.d015103 m n (_root_.GD.N0232.N0720.N1133.d016574 theta)
  have hsum := hweighted.add
    (hlikelihood.const_mul (_root_.GD.N0232.N0720.N1133.d016575 theta ^ 2))
  have hscaled := hsum.const_mul
    (2 * _root_.GD.N0232.N0720.N1133.d016570 ^ (m + n))
  change Integrable (fun omega ↦
    (2 * _root_.GD.N0232.N0720.N1133.d016570 ^ (m + n)) *
      (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1133.d016574 theta) omega *
          (q omega - theta.location) ^ 2 +
        _root_.GD.N0232.N0720.N1133.d016575 theta ^ 2 *
          _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1133.d016574 theta) omega))
    (_root_.GD.N0232.N0720.N1080.d014172 m n)
  simpa only [Pi.add_apply] using hscaled



theorem d016585
    (m n : ℕ) (theta eta : _root_.GD.N0232.N0720.N1080.d014168)
    (heta : eta ∈ _root_.GD.N0232.N0720.N1133.d016577 theta)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1499.d015001 m n eta omega *
        (q omega - eta.location) ^ 2 ≤
      _root_.GD.N0232.N0720.N1133.d016582 m n theta q omega := by
  have hdensity := _root_.GD.N0232.N0720.N1133.d016581
    m n theta eta heta omega
  have hlocation := heta.2
  have hlocation' :
      |theta.location - eta.location| < _root_.GD.N0232.N0720.N1133.d016575 theta := by
    simpa [abs_sub_comm] using hlocation
  have hlocation_sq :
      (theta.location - eta.location) ^ 2 ≤
        _root_.GD.N0232.N0720.N1133.d016575 theta ^ 2 := by
    rcases abs_lt.mp hlocation' with ⟨hlower, hupper⟩
    have hleft :
        0 < _root_.GD.N0232.N0720.N1133.d016575 theta -
          (theta.location - eta.location) := by linarith
    have hright :
        0 < _root_.GD.N0232.N0720.N1133.d016575 theta +
          (theta.location - eta.location) := by linarith
    nlinarith [mul_pos hleft hright]
  have herror :
      (q omega - eta.location) ^ 2 ≤
        2 * ((q omega - theta.location) ^ 2 +
          _root_.GD.N0232.N0720.N1133.d016575 theta ^ 2) := by
    have hsplit :
        q omega - eta.location =
          (q omega - theta.location) +
            (theta.location - eta.location) := by ring
    rw [hsplit]
    nlinarith [sq_nonneg
      ((q omega - theta.location) -
        (theta.location - eta.location))]
  calc
    _root_.GD.N0232.N0720.N1499.d015001 m n eta omega *
        (q omega - eta.location) ^ 2 ≤
      (_root_.GD.N0232.N0720.N1133.d016570 ^ (m + n) *
          _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1133.d016574 theta) omega) *
        (2 * ((q omega - theta.location) ^ 2 +
          _root_.GD.N0232.N0720.N1133.d016575 theta ^ 2)) := by
      exact mul_le_mul hdensity herror (sq_nonneg _)
        (mul_nonneg (pow_nonneg _root_.GD.N0232.N0720.N1133.d016571.le _)
          (_root_.GD.N0232.N0720.N1499.d015003 m n
            (_root_.GD.N0232.N0720.N1133.d016574 theta) omega))
    _ = _root_.GD.N0232.N0720.N1133.d016582 m n theta q omega := by
      unfold _root_.GD.N0232.N0720.N1133.d016582
      ring



theorem d016586
    (m n : ℕ) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    ∃ U ∈ nhds theta, ∃ bound : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ≥0∞,
      (∫⁻ omega, bound omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≠ ∞ ∧
      ∀ eta ∈ U, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
        ENNReal.ofReal
            (_root_.GD.N0232.N0720.N1499.d015001 m n eta omega *
              (q omega - eta.location) ^ 2) ≤ bound omega := by
  refine ⟨_root_.GD.N0232.N0720.N1133.d016577 theta,
    _root_.GD.N0232.N0720.N1133.d016580 theta,
    fun omega ↦ ENNReal.ofReal
      (_root_.GD.N0232.N0720.N1133.d016582 m n theta q omega), ?_, ?_⟩
  · exact
      (lintegral_ofReal_ne_top_iff_integrable
        (_root_.GD.N0232.N0720.N1133.d016584 m n theta q hq).aestronglyMeasurable
        (ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 m n) fun omega ↦
          _root_.GD.N0232.N0720.N1133.d016583 m n theta q omega)).2
        (_root_.GD.N0232.N0720.N1133.d016584 m n theta q hq)
  · intro eta heta
    exact ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 m n) fun omega ↦
      ENNReal.ofReal_le_ofReal
        (_root_.GD.N0232.N0720.N1133.d016585
          m n theta eta heta q omega)

set_option maxHeartbeats 800000 in




theorem d016587
    (m n : ℕ) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q) :
    Continuous (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta q) := by
  simpa only [_root_.GD.N0232.N0720.N1080.d014182] using
    _root_.GD.N0230.N0591.d000132
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n)
      (_root_.GD.N0232.N0720.N1499.d015001 m n) _root_.GD.N0232.N0720.N1080.d014168.location q
      (_root_.GD.N0232.N0720.N1499.d015006 m n)
      (_root_.GD.N0232.N0720.N1499.d015002 m n)
      (_root_.GD.N0232.N0720.N1499.d015003 m n)
      (_root_.GD.N0232.N0720.N1499.d015007 m n)
      _root_.GD.N0232.N0720.N1499.d014998
      (_root_.GD.N0232.N0720.N1133.d016586 m n q hq)



theorem d016588
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Continuous (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value) :=
  _root_.GD.N0232.N0720.N1133.d016587 m n s.value s.finiteRisk



theorem d016589
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    UpperSemicontinuous
      (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value) :=
  (_root_.GD.N0232.N0720.N1133.d016588 m n s).upperSemicontinuous





theorem d016590
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0230.N0598.d000587 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (fun theta ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value)
        _root_.GD.N0232.N0720.N1133.d016566 =
      _root_.GD.N0232.N0720.N1159.d014630 m n s.value := by
  have h := _root_.GD.N0230.N0598.d000596
    (_root_.GD.N0232.N0720.N1080.d014182 m n) (fun theta ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value)
    _root_.GD.N0232.N0720.N1133.d016566 _root_.GD.N0232.N0720.N1133.d016567
    (_root_.GD.N0232.N0720.N1133.d016589 m n s)
    (fun d _ ↦ _root_.GD.N0232.N0720.N1499.d015008 m n d)
  simpa [_root_.GD.N0230.N0598.d000586, _root_.GD.N0232.N0720.N1159.d014630, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672] using h



theorem d016591
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (⋂ N, _root_.GD.N0230.N0598.d000588 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (fun theta ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value)
        _root_.GD.N0232.N0720.N1133.d016566 N) =
      _root_.GD.N0232.N0720.N1159.d014630 m n s.value := by
  rw [_root_.GD.N0230.N0598.d000598]
  exact _root_.GD.N0232.N0720.N1133.d016590 m n s


def d016592
    (m n : ℕ) (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (theta : _root_.GD.N0232.N0720.N1080.d014168) : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {d | _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta s}

theorem d016593
    (m n : ℕ) (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    IsClosed (_root_.GD.N0232.N0720.N1133.d016592 m n s theta) := by
  simpa [_root_.GD.N0232.N0720.N1133.d016592, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122
      (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun _ : Unit ↦ _root_.GD.N0232.N0720.N1080.d014171 m n theta)
      (fun _ : Unit ↦ theta.location)
      (fun _ : Unit ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s)
      (fun _ : Unit ↦ _root_.GD.N0232.N0720.N1080.d014173 m n theta))

theorem d016594
    (m n : ℕ) (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    Convex ℝ (_root_.GD.N0232.N0720.N1133.d016592 m n s theta) := by
  simpa [_root_.GD.N0232.N0720.N1133.d016592, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123
      (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun _ : Unit ↦ _root_.GD.N0232.N0720.N1080.d014171 m n theta)
      (fun _ : Unit ↦ theta.location)
      (fun _ : Unit ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s)
      (fun _ : Unit ↦ _root_.GD.N0232.N0720.N1080.d014173 m n theta))



theorem d016595
    (m n N : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0230.N0598.d000588 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (fun theta ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value)
        _root_.GD.N0232.N0720.N1133.d016566 N =
      ⋂ i : Fin N,
        _root_.GD.N0232.N0720.N1133.d016592 m n s.value (_root_.GD.N0232.N0720.N1133.d016566 i) := by
  ext d
  constructor
  · intro hd
    rw [mem_iInter]
    intro i
    exact hd i i.isLt
  · intro hd j hj
    exact mem_iInter.mp hd ⟨j, hj⟩

theorem d016596
    (m n N : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    IsClosed (_root_.GD.N0230.N0598.d000588 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (fun theta ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value)
      _root_.GD.N0232.N0720.N1133.d016566 N) := by
  rw [_root_.GD.N0232.N0720.N1133.d016595 m n N s]
  exact isClosed_iInter fun i ↦
    _root_.GD.N0232.N0720.N1133.d016593 m n s.value (_root_.GD.N0232.N0720.N1133.d016566 i)

theorem d016597
    (m n N : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Convex ℝ (_root_.GD.N0230.N0598.d000588 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (fun theta ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value)
      _root_.GD.N0232.N0720.N1133.d016566 N) := by
  rw [_root_.GD.N0232.N0720.N1133.d016595 m n N s]
  exact convex_iInter fun i ↦
    _root_.GD.N0232.N0720.N1133.d016594 m n s.value (_root_.GD.N0232.N0720.N1133.d016566 i)

theorem d016598
    (m n N : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (_root_.GD.N0230.N0598.d000588 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (fun theta ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value)
      _root_.GD.N0232.N0720.N1133.d016566 N).Nonempty := by
  exact ⟨s.value, fun _ _ ↦ le_rfl⟩


noncomputable def d016599
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (N : ℕ) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  Classical.choose <| _root_.GD.N0230.N0685.d000521
    (_root_.GD.N0232.N0720.N1133.d016598 m n N s)
    (_root_.GD.N0232.N0720.N1133.d016596 m n N s).isComplete
    (_root_.GD.N0232.N0720.N1133.d016597 m n N s)
    0

theorem d016600
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (N : ℕ) :
    _root_.GD.N0230.N0685.d000511
      (_root_.GD.N0230.N0598.d000588 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (fun theta ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value)
        _root_.GD.N0232.N0720.N1133.d016566 N)
      0 (_root_.GD.N0232.N0720.N1133.d016599 m n s N) :=
  Classical.choose_spec <| _root_.GD.N0230.N0685.d000521
    (_root_.GD.N0232.N0720.N1133.d016598 m n N s)
    (_root_.GD.N0232.N0720.N1133.d016596 m n N s).isComplete
    (_root_.GD.N0232.N0720.N1133.d016597 m n N s)
    0



theorem d016601
    (m n : ℕ) (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0230.N0685.d000511 (_root_.GD.N0232.N0720.N1159.d014630 m n s) 0
      (_root_.GD.N0232.N0720.N1159.d014633 m n s) := by
  let C : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) := _root_.GD.N0232.N0720.N1159.d014630 m n s
  let p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := _root_.GD.N0232.N0720.N1159.d014633 m n s
  have hpC : p ∈ C := (_root_.GD.N0232.N0720.N1159.d014634 m n s).1
  letI : Nonempty C := ⟨⟨p, hpC⟩⟩
  have hnormMin : ‖(0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) - p‖ =
      ⨅ w : C, ‖(0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) -
        (w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      have hrisk := (_root_.GD.N0232.N0720.N1159.d014634 m n s).2.2
        (w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) w.property
      rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at hrisk
      simp only [zero_sub, norm_neg] at hrisk ⊢
      have hsq : ‖p‖ ^ 2 ≤
          ‖(w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))‖ ^ 2 :=
        (ENNReal.ofReal_le_ofReal_iff
          (sq_nonneg ‖(w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))‖)).mp hrisk
      nlinarith [norm_nonneg p,
        norm_nonneg (w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))]
    · have hbdd : BddBelow
          (Set.range (fun w : C ↦
            ‖(0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) -
              (w : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))‖)) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨w, rfl⟩
        exact norm_nonneg _
      exact ciInf_le hbdd ⟨p, hpC⟩
  refine ⟨hpC, ?_⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero
    (_root_.GD.N0232.N0720.N1159.d014632 m n s) hpC).1 hnormMin

theorem d016602
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0230.N0685.d000511
      (_root_.GD.N0230.N0598.d000586 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (fun theta ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value))
      0 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by
  simpa [_root_.GD.N0230.N0598.d000586, _root_.GD.N0232.N0720.N1159.d014630, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672] using
    _root_.GD.N0232.N0720.N1133.d016601 m n s.value



theorem d016603
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Tendsto (_root_.GD.N0232.N0720.N1133.d016599 m n s) atTop
      (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)) := by
  exact _root_.GD.N0230.N0598.d000602
    (_root_.GD.N0232.N0720.N1080.d014182 m n) (fun theta ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value)
    _root_.GD.N0232.N0720.N1133.d016566 _root_.GD.N0232.N0720.N1133.d016567
    (_root_.GD.N0232.N0720.N1133.d016599 m n s)
    (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
    (_root_.GD.N0232.N0720.N1133.d016589 m n s)
    (fun d _ ↦ _root_.GD.N0232.N0720.N1499.d015008 m n d)
    (fun N ↦ _root_.GD.N0232.N0720.N1133.d016596 m n N s)
    (_root_.GD.N0232.N0720.N1133.d016600 m n s)
    (_root_.GD.N0232.N0720.N1133.d016602 m n s)

end

end N1133
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1133.d016569
#print axioms _root_.GD.N0232.N0720.N1133.d016581
#print axioms _root_.GD.N0232.N0720.N1133.d016587
#print axioms _root_.GD.N0232.N0720.N1133.d016590
#print axioms _root_.GD.N0232.N0720.N1133.d016603
