import GD.Module0965


























open Filter Function Topology
open scoped NNReal

namespace GD
namespace N0232
namespace N0720
namespace N1273

noncomputable section

set_option maxHeartbeats 800000

open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0719.N0946.d009229

variable {E : Type*} [NormedAddCommGroup E]


def d015593 (F : E → E) (x : E) : ℝ := ‖F x - x‖


def d015594 (F G : E → E) (x : E) : ℝ :=
  _root_.GD.N0232.N0720.N1273.d015593 F x + _root_.GD.N0232.N0720.N1273.d015593 G x


def d015595 (F G : E → E) (x : E) : ℝ :=
  _root_.GD.N0232.N0720.N1273.d015593 F x ^ 2 + _root_.GD.N0232.N0720.N1273.d015593 G x ^ 2

theorem d015596 (F : E → E) (x : E) :
    0 ≤ _root_.GD.N0232.N0720.N1273.d015593 F x := norm_nonneg _

theorem d015597 (F G : E → E) (x : E) :
    0 ≤ _root_.GD.N0232.N0720.N1273.d015594 F G x := by
  exact add_nonneg (_root_.GD.N0232.N0720.N1273.d015596 F x) (_root_.GD.N0232.N0720.N1273.d015596 G x)

theorem d015598 (F G : E → E) (x : E) :
    0 ≤ _root_.GD.N0232.N0720.N1273.d015595 F G x := by
  unfold _root_.GD.N0232.N0720.N1273.d015595
  positivity





theorem d015599
    {F : E → E} {K : ℝ≥0} {u x : E}
    (hF : LipschitzWith K F) (hu : F u = u) :
    _root_.GD.N0232.N0720.N1273.d015593 F x ≤ (K : ℝ) * ‖x - u‖ + ‖x - u‖ := by
  have hid : F x - x = (F x - F u) + (u - x) := by
    rw [hu]
    abel
  rw [_root_.GD.N0232.N0720.N1273.d015593, hid]
  calc
    ‖(F x - F u) + (u - x)‖ ≤ ‖F x - F u‖ + ‖u - x‖ :=
      norm_add_le _ _
    _ ≤ (K : ℝ) * ‖x - u‖ + ‖u - x‖ := by
      gcongr
      simpa only [dist_eq_norm] using hF.dist_le_mul x u
    _ = (K : ℝ) * ‖x - u‖ + ‖x - u‖ := by
      rw [norm_sub_rev]



theorem d015600
    {F G : E → E} {KF KG : ℝ≥0} {u x : E}
    (hF : LipschitzWith KF F) (hG : LipschitzWith KG G)
    (huF : F u = u) (huG : G u = u) :
    _root_.GD.N0232.N0720.N1273.d015594 F G x ≤
      ((KF : ℝ) + 1 + ((KG : ℝ) + 1)) * ‖x - u‖ := by
  unfold _root_.GD.N0232.N0720.N1273.d015594
  calc
    _root_.GD.N0232.N0720.N1273.d015593 F x + _root_.GD.N0232.N0720.N1273.d015593 G x ≤
        ((KF : ℝ) * ‖x - u‖ + ‖x - u‖) +
          ((KG : ℝ) * ‖x - u‖ + ‖x - u‖) := by
      gcongr
      · exact _root_.GD.N0232.N0720.N1273.d015599 hF huF
      · exact _root_.GD.N0232.N0720.N1273.d015599 hG huG
    _ = ((KF : ℝ) + 1 + ((KG : ℝ) + 1)) * ‖x - u‖ := by ring



theorem d015601
    {F G : E → E} {KF KG : ℝ≥0} {u : E}
    (hF : LipschitzWith KF F) (hG : LipschitzWith KG G)
    (huF : F u = u) (huG : G u = u)
    (q : ℕ → E) (hq : Tendsto q atTop (nhds u)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1273.d015594 F G (q j)) atTop (nhds 0) := by
  have hnorm : Tendsto (fun j ↦ ‖q j - u‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hq
  apply squeeze_zero
    (fun j ↦ _root_.GD.N0232.N0720.N1273.d015597 F G (q j))
    (fun j ↦ _root_.GD.N0232.N0720.N1273.d015600
      hF hG huF huG)
  simpa only [mul_zero] using
    hnorm.const_mul ((KF : ℝ) + 1 + ((KG : ℝ) + 1))



theorem d015602
    {F G : E → E} {KF KG : ℝ≥0} {u : E}
    (hF : LipschitzWith KF F) (hG : LipschitzWith KG G)
    (huF : F u = u) (huG : G u = u)
    (q : ℕ → E) (hq : Tendsto q atTop (nhds u)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1273.d015595 F G (q j))
      atTop (nhds 0) := by
  have hsum := _root_.GD.N0232.N0720.N1273.d015601
    hF hG huF huG q hq
  have hFle : ∀ j, _root_.GD.N0232.N0720.N1273.d015593 F (q j) ≤ _root_.GD.N0232.N0720.N1273.d015594 F G (q j) := by
    intro j
    unfold _root_.GD.N0232.N0720.N1273.d015594
    exact le_add_of_nonneg_right (_root_.GD.N0232.N0720.N1273.d015596 G (q j))
  have hGle : ∀ j, _root_.GD.N0232.N0720.N1273.d015593 G (q j) ≤ _root_.GD.N0232.N0720.N1273.d015594 F G (q j) := by
    intro j
    unfold _root_.GD.N0232.N0720.N1273.d015594
    exact le_add_of_nonneg_left (_root_.GD.N0232.N0720.N1273.d015596 F (q j))
  have hFzero : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1273.d015593 F (q j)) atTop (nhds 0) :=
    squeeze_zero (fun j ↦ _root_.GD.N0232.N0720.N1273.d015596 F (q j)) hFle hsum
  have hGzero : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1273.d015593 G (q j)) atTop (nhds 0) :=
    squeeze_zero (fun j ↦ _root_.GD.N0232.N0720.N1273.d015596 G (q j)) hGle hsum
  have henergy := (hFzero.pow 2).add (hGzero.pow 2)
  change Tendsto
    (fun j ↦ _root_.GD.N0232.N0720.N1273.d015593 F (q j) ^ 2 + _root_.GD.N0232.N0720.N1273.d015593 G (q j) ^ 2)
    atTop (nhds 0)
  convert henergy using 1 <;> norm_num





theorem d015603
    {F : E → E} {K : ℝ≥0} {u : E}
    (hF : LipschitzWith K F)
    (q : ℕ → E) (hq : Tendsto q atTop (nhds u)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1273.d015593 F (q j)) atTop
      (nhds (_root_.GD.N0232.N0720.N1273.d015593 F u)) := by
  exact ((hF.continuous.comp continuous_id).sub continuous_id).norm
    |>.continuousAt.tendsto.comp hq


theorem d015604
    {F : E → E} {K : ℝ≥0} {u : E}
    (hF : LipschitzWith K F)
    (q : ℕ → E) (hq : Tendsto q atTop (nhds u)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1273.d015593 F (q j)) atTop (nhds 0) ↔
      F u = u := by
  constructor
  · intro hzero
    have hlimit := _root_.GD.N0232.N0720.N1273.d015603 hF q hq
    have hnorm : _root_.GD.N0232.N0720.N1273.d015593 F u = 0 := tendsto_nhds_unique hlimit hzero
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · intro hu
    have hnorm : Tendsto (fun j ↦ ‖q j - u‖) atTop (nhds 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hq
    apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1273.d015596 F (q j))
      (fun j ↦ _root_.GD.N0232.N0720.N1273.d015599 hF hu)
    simpa only [mul_zero, zero_add] using
      (hnorm.const_mul (K : ℝ)).add hnorm




theorem d015605
    {F G : E → E} {KF KG : ℝ≥0} {u : E}
    (hF : LipschitzWith KF F) (hG : LipschitzWith KG G)
    (q : ℕ → E) (hq : Tendsto q atTop (nhds u)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1273.d015594 F G (q j)) atTop (nhds 0) ↔
      F u = u ∧ G u = u := by
  constructor
  · intro hsum
    have hFzero : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1273.d015593 F (q j))
        atTop (nhds 0) := by
      exact squeeze_zero
        (fun j ↦ _root_.GD.N0232.N0720.N1273.d015596 F (q j))
        (fun j ↦ by
          unfold _root_.GD.N0232.N0720.N1273.d015594
          exact le_add_of_nonneg_right (_root_.GD.N0232.N0720.N1273.d015596 G (q j)))
        hsum
    have hGzero : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1273.d015593 G (q j))
        atTop (nhds 0) := by
      exact squeeze_zero
        (fun j ↦ _root_.GD.N0232.N0720.N1273.d015596 G (q j))
        (fun j ↦ by
          unfold _root_.GD.N0232.N0720.N1273.d015594
          exact le_add_of_nonneg_left (_root_.GD.N0232.N0720.N1273.d015596 F (q j)))
        hsum
    exact ⟨
      (_root_.GD.N0232.N0720.N1273.d015604 hF q hq).1 hFzero,
      (_root_.GD.N0232.N0720.N1273.d015604 hG q hq).1 hGzero⟩
  · rintro ⟨huF, huG⟩
    exact _root_.GD.N0232.N0720.N1273.d015601
      hF hG huF huG q hq




theorem d015606
    {F G : E → E} {KF KG : ℝ≥0} {u : E}
    (hF : LipschitzWith KF F) (hG : LipschitzWith KG G)
    (q : ℕ → E) (hq : Tendsto q atTop (nhds u))
    (hnot : ¬ (F u = u ∧ G u = u)) :
    ∀ᶠ j in atTop,
      _root_.GD.N0232.N0720.N1273.d015594 F G u / 2 < _root_.GD.N0232.N0720.N1273.d015594 F G (q j) := by
  have hlimit : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1273.d015594 F G (q j)) atTop
      (nhds (_root_.GD.N0232.N0720.N1273.d015594 F G u)) := by
    simpa only [_root_.GD.N0232.N0720.N1273.d015594] using
      (_root_.GD.N0232.N0720.N1273.d015603 hF q hq).add
        (_root_.GD.N0232.N0720.N1273.d015603 hG q hq)
  have hne : _root_.GD.N0232.N0720.N1273.d015594 F G u ≠ 0 := by
    intro hzero
    have hparts : _root_.GD.N0232.N0720.N1273.d015593 F u = 0 ∧ _root_.GD.N0232.N0720.N1273.d015593 G u = 0 := by
      exact add_eq_zero_iff_of_nonneg
        (_root_.GD.N0232.N0720.N1273.d015596 F u) (_root_.GD.N0232.N0720.N1273.d015596 G u) |>.mp hzero
    apply hnot
    exact ⟨sub_eq_zero.mp (norm_eq_zero.mp hparts.1),
      sub_eq_zero.mp (norm_eq_zero.mp hparts.2)⟩
  have hpos : 0 < _root_.GD.N0232.N0720.N1273.d015594 F G u :=
    lt_of_le_of_ne (_root_.GD.N0232.N0720.N1273.d015597 F G u) (Ne.symm hne)
  exact (tendsto_order.1 hlimit).1 _ (by linarith)


theorem d015607
    {F G : E → E} {KF KG : ℝ≥0} {u : E}
    (hF : LipschitzWith KF F) (hG : LipschitzWith KG G)
    (q : ℕ → E) (hq : Tendsto q atTop (nhds u)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1273.d015595 F G (q j))
      atTop (nhds 0) ↔ F u = u ∧ G u = u := by
  constructor
  · intro henergy
    have hFpow : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1273.d015593 F (q j) ^ 2)
        atTop (nhds 0) := by
      exact squeeze_zero
        (fun j ↦ sq_nonneg (_root_.GD.N0232.N0720.N1273.d015593 F (q j)))
        (fun j ↦ by
          unfold _root_.GD.N0232.N0720.N1273.d015595
          exact le_add_of_nonneg_right (sq_nonneg (_root_.GD.N0232.N0720.N1273.d015593 G (q j))))
        henergy
    have hGpow : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1273.d015593 G (q j) ^ 2)
        atTop (nhds 0) := by
      exact squeeze_zero
        (fun j ↦ sq_nonneg (_root_.GD.N0232.N0720.N1273.d015593 G (q j)))
        (fun j ↦ by
          unfold _root_.GD.N0232.N0720.N1273.d015595
          exact le_add_of_nonneg_left (sq_nonneg (_root_.GD.N0232.N0720.N1273.d015593 F (q j))))
        henergy
    have hFlimit := (_root_.GD.N0232.N0720.N1273.d015603 hF q hq).pow 2
    have hGlimit := (_root_.GD.N0232.N0720.N1273.d015603 hG q hq).pow 2
    have hFzero : _root_.GD.N0232.N0720.N1273.d015593 F u = 0 := by
      have : _root_.GD.N0232.N0720.N1273.d015593 F u ^ 2 = 0 := tendsto_nhds_unique hFlimit hFpow
      nlinarith [_root_.GD.N0232.N0720.N1273.d015596 F u]
    have hGzero : _root_.GD.N0232.N0720.N1273.d015593 G u = 0 := by
      have : _root_.GD.N0232.N0720.N1273.d015593 G u ^ 2 = 0 := tendsto_nhds_unique hGlimit hGpow
      nlinarith [_root_.GD.N0232.N0720.N1273.d015596 G u]
    exact ⟨sub_eq_zero.mp (norm_eq_zero.mp hFzero),
      sub_eq_zero.mp (norm_eq_zero.mp hGzero)⟩
  · rintro ⟨huF, huG⟩
    exact _root_.GD.N0232.N0720.N1273.d015602
      hF hG huF huG q hq



variable {m n : ℕ}



theorem d015608
    (u : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (huTwo : _root_.GD.N0232.N0720.N1146.d015228 m n u = u)
    (huThree : _root_.GD.N0232.N0720.N1146.d015229 m n u = u)
    (q : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : Tendsto q atTop (nhds u)) :
    Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n (q j) - q j‖ +
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (q j) - q j‖)
      atTop (nhds 0) := by
  simpa only [_root_.GD.N0232.N0720.N1273.d015594, _root_.GD.N0232.N0720.N1273.d015593,
    _root_.GD.N0232.N0720.N1146.d015228,
    _root_.GD.N0232.N0720.N1146.d015229] using
    _root_.GD.N0232.N0720.N1273.d015601
      (_root_.GD.N0232.N0720.N1146.d015216 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n))
      (_root_.GD.N0232.N0720.N1146.d015216 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n))
      huTwo huThree q hq



theorem d015609
    (u : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (q : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : Tendsto q atTop (nhds u)) :
    Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n (q j) - q j‖ +
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (q j) - q j‖)
      atTop (nhds 0) ↔
      _root_.GD.N0232.N0720.N1146.d015228 m n u = u ∧
        _root_.GD.N0232.N0720.N1146.d015229 m n u = u := by
  simpa only [_root_.GD.N0232.N0720.N1273.d015594, _root_.GD.N0232.N0720.N1273.d015593,
    _root_.GD.N0232.N0720.N1146.d015228,
    _root_.GD.N0232.N0720.N1146.d015229] using
    _root_.GD.N0232.N0720.N1273.d015605
      (_root_.GD.N0232.N0720.N1146.d015216 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n))
      (_root_.GD.N0232.N0720.N1146.d015216 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n))
      q hq





theorem d015610
    (u : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hu : _root_.GD.N0232.N0720.N1159.d014637 m n u)
    (q : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : Tendsto q atTop (nhds u)) :
    Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n (q j) - q j‖ +
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (q j) - q j‖)
      atTop (nhds 0) ↔
      ∀ g : _root_.GD.N0232.N0720.N1482.d015118,
        _root_.GD.N0232.N0720.N1159.d014642 m n g u hu = u := by
  constructor
  · intro hcurrent
    have hfixed :=
      (_root_.GD.N0232.N0720.N1273.d015609
        u q hq).1 hcurrent
    have hTwo : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 u hu = u := by
      rw [← _root_.GD.N0232.N0720.N1146.d015218 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) u hu]
      exact hfixed.1
    have hThree :
        _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 u hu = u := by
      rw [← _root_.GD.N0232.N0720.N1146.d015218 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) u hu]
      exact hfixed.2
    exact _root_.GD.N0232.N0720.N1482.d015167
      (m := m) (n := n) u hu hTwo hThree
  · intro hall
    apply
      (_root_.GD.N0232.N0720.N1273.d015609
        u q hq).2
    constructor
    · change _root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) u = u
      rw [_root_.GD.N0232.N0720.N1146.d015218 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) u hu]
      exact hall _root_.GD.N0232.N0720.N1482.d015130
    · change _root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) u = u
      rw [_root_.GD.N0232.N0720.N1146.d015218 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) u hu]
      exact hall _root_.GD.N0232.N0720.N1482.d015131







theorem d015611
    (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) → Prop) :
    (∃ (u : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
        (hu : _root_.GD.N0232.N0720.N1159.d014637 m n u),
        P u ∧ ∃ q : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
            Tendsto q atTop (nhds u) ∧
            Tendsto
              (fun j ↦
                ‖_root_.GD.N0232.N0720.N1146.d015228 m n (q j) - q j‖ +
                ‖_root_.GD.N0232.N0720.N1146.d015229 m n (q j) -
                  q j‖)
              atTop (nhds 0)) ↔
      ∃ (u : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
          (hu : _root_.GD.N0232.N0720.N1159.d014637 m n u),
        P u ∧ ∀ g : _root_.GD.N0232.N0720.N1482.d015118,
          _root_.GD.N0232.N0720.N1159.d014642 m n g u hu = u := by
  constructor
  · rintro ⟨u, hu, hP, q, hq, hcurrent⟩
    refine ⟨u, hu, hP, ?_⟩
    exact
      (_root_.GD.N0232.N0720.N1273.d015610
        u hu q hq).1 hcurrent
  · rintro ⟨u, hu, hP, hall⟩
    refine ⟨u, hu, hP, fun _ ↦ u, tendsto_const_nhds, ?_⟩
    exact
      (_root_.GD.N0232.N0720.N1273.d015610
        u hu (fun _ ↦ u) tendsto_const_nhds).2 hall






theorem d015612 :
    Tendsto (fun _ : ℕ ↦ _root_.GD.N0232.N0720.N1273.d015593 id (1 : ℝ)) atTop (nhds 0) ∧
      ¬ Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 0) := by
  constructor
  · simpa [_root_.GD.N0232.N0720.N1273.d015593]
  · intro hzero
    have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
    norm_num at this



theorem d015613 :
    LipschitzWith 1 (fun x : ℝ ↦ x + 1) ∧
      Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) ∧
      ¬ Tendsto
        (fun _ : ℕ ↦ _root_.GD.N0232.N0720.N1273.d015593 (fun x : ℝ ↦ x + 1) 0)
        atTop (nhds 0) := by
  refine ⟨?_, tendsto_const_nhds, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq]
  · intro hzero
    have hone : Tendsto
        (fun _ : ℕ ↦ _root_.GD.N0232.N0720.N1273.d015593 (fun x : ℝ ↦ x + 1) 0)
        atTop (nhds 1) := by
      simpa [_root_.GD.N0232.N0720.N1273.d015593] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
          atTop (nhds 1))
    have : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
    norm_num at this


def d015614 (x : ℝ) : ℝ := if x = 0 then 0 else 1

theorem d015615 : _root_.GD.N0232.N0720.N1273.d015614 0 = 0 := by
  simp [_root_.GD.N0232.N0720.N1273.d015614]




theorem d015616 :
    _root_.GD.N0232.N0720.N1273.d015614 0 = 0 ∧
      Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) atTop (nhds 0) ∧
      Tendsto
        (fun j : ℕ ↦
          _root_.GD.N0232.N0720.N1273.d015593 _root_.GD.N0232.N0720.N1273.d015614 (1 / ((j : ℝ) + 1)))
        atTop (nhds 1) ∧
      ¬ Tendsto
        (fun j : ℕ ↦
          _root_.GD.N0232.N0720.N1273.d015593 _root_.GD.N0232.N0720.N1273.d015614 (1 / ((j : ℝ) + 1)))
        atTop (nhds 0) := by
  have hrow : Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have heq :
      (fun j : ℕ ↦ _root_.GD.N0232.N0720.N1273.d015593 _root_.GD.N0232.N0720.N1273.d015614 (1 / ((j : ℝ) + 1))) =
        fun j : ℕ ↦ |1 - 1 / ((j : ℝ) + 1)| := by
    funext j
    have hden : ((j : ℝ) + 1) ≠ 0 := by positivity
    simp [_root_.GD.N0232.N0720.N1273.d015593, _root_.GD.N0232.N0720.N1273.d015614, hden, Real.norm_eq_abs]
  have hone : Tendsto
      (fun j : ℕ ↦ _root_.GD.N0232.N0720.N1273.d015593 _root_.GD.N0232.N0720.N1273.d015614 (1 / ((j : ℝ) + 1)))
      atTop (nhds 1) := by
    rw [heq]
    have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [sub_zero, abs_one] using (hconst.sub hrow).abs
  refine ⟨_root_.GD.N0232.N0720.N1273.d015615, hrow, hone, ?_⟩
  intro hzero
  have : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
  norm_num at this





def d015617 (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)


theorem d015618 :
    Tendsto _root_.GD.N0232.N0720.N1273.d015617 atTop (nhds 0) := by
  change Tendsto (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat


theorem d015619 :
    Tendsto
      (fun j : ℕ ↦ _root_.GD.N0232.N0720.N1273.d015593 (fun x : ℝ ↦ 2 * x)
        (_root_.GD.N0232.N0720.N1273.d015617 j))
      atTop (nhds 0) := by
  have heq :
      (fun j : ℕ ↦ _root_.GD.N0232.N0720.N1273.d015593 (fun x : ℝ ↦ 2 * x)
        (_root_.GD.N0232.N0720.N1273.d015617 j)) = _root_.GD.N0232.N0720.N1273.d015617 := by
    funext j
    have hpos : 0 < (j : ℝ) + 1 := by positivity
    have hxpos : 0 < _root_.GD.N0232.N0720.N1273.d015617 j := by
      exact one_div_pos.mpr hpos
    rw [_root_.GD.N0232.N0720.N1273.d015593, show
      2 * _root_.GD.N0232.N0720.N1273.d015617 j - _root_.GD.N0232.N0720.N1273.d015617 j =
        _root_.GD.N0232.N0720.N1273.d015617 j by ring]
    exact Real.norm_of_nonneg hxpos.le
  rw [heq]
  exact _root_.GD.N0232.N0720.N1273.d015618





theorem d015620 (j : ℕ) :
    (((j : ℝ) + 1) ^ 2) *
        _root_.GD.N0232.N0720.N1273.d015593 (fun x : ℝ ↦ 2 * x) (_root_.GD.N0232.N0720.N1273.d015617 j) ^ 2 = 1 := by
  have hpos : 0 < (j : ℝ) + 1 := by positivity
  have hne : (j : ℝ) + 1 ≠ 0 := ne_of_gt hpos
  rw [show _root_.GD.N0232.N0720.N1273.d015593 (fun x : ℝ ↦ 2 * x) (_root_.GD.N0232.N0720.N1273.d015617 j) =
      1 / ((j : ℝ) + 1) by
    rw [_root_.GD.N0232.N0720.N1273.d015593, _root_.GD.N0232.N0720.N1273.d015617]
    have hsub : 2 * (1 / ((j : ℝ) + 1)) - 1 / ((j : ℝ) + 1) =
        1 / ((j : ℝ) + 1) := by ring
    rw [hsub, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hpos)]]
  field_simp




theorem d015621 :
    (fun x : ℝ ↦ 2 * x) 0 = 0 ∧
      Tendsto _root_.GD.N0232.N0720.N1273.d015617 atTop (nhds 0) ∧
      Tendsto
        (fun j : ℕ ↦ _root_.GD.N0232.N0720.N1273.d015593 (fun x : ℝ ↦ 2 * x)
          (_root_.GD.N0232.N0720.N1273.d015617 j))
        atTop (nhds 0) ∧
      (∀ j : ℕ,
        (((j : ℝ) + 1) ^ 2) *
          _root_.GD.N0232.N0720.N1273.d015593 (fun x : ℝ ↦ 2 * x)
            (_root_.GD.N0232.N0720.N1273.d015617 j) ^ 2 = 1) := by
  exact ⟨by norm_num, _root_.GD.N0232.N0720.N1273.d015618,
    _root_.GD.N0232.N0720.N1273.d015619,
    _root_.GD.N0232.N0720.N1273.d015620⟩

end

end N1273
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1273.d015600
#print axioms _root_.GD.N0232.N0720.N1273.d015605
#print axioms _root_.GD.N0232.N0720.N1273.d015606
#print axioms _root_.GD.N0232.N0720.N1273.d015607
#print axioms _root_.GD.N0232.N0720.N1273.d015609
#print axioms _root_.GD.N0232.N0720.N1273.d015610
#print axioms _root_.GD.N0232.N0720.N1273.d015611
#print axioms _root_.GD.N0232.N0720.N1273.d015612
#print axioms _root_.GD.N0232.N0720.N1273.d015613
#print axioms _root_.GD.N0232.N0720.N1273.d015616
#print axioms _root_.GD.N0232.N0720.N1273.d015621
