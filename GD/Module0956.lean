import GD.Module0923
import GD.Module0955











open Filter Set Topology

namespace GD
namespace N0232
namespace N0720
namespace N1072

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0230.N0718

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



def d015009 (t : ℝ) : ℝ :=
  Real.sqrt (((n : ℝ) * t) / ((m : ℝ) * (1 - t)))

include hm hn in
theorem d015010
    {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    0 < _root_.GD.N0232.N0720.N1072.d015009 m n t := by
  unfold _root_.GD.N0232.N0720.N1072.d015009
  apply Real.sqrt_pos.2
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  exact div_pos (mul_pos hnpos ht₀)
    (mul_pos hmpos (sub_pos.mpr ht₁))

include hm hn in


def d015011
    (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1) : _root_.GD.N0232.N0720.N1080.d014168 := by
  let r := _root_.GD.N0232.N0720.N1072.d015009 m n t
  have hr : 0 < r := _root_.GD.N0232.N0720.N1072.d015010 m n hm hn ht₀ ht₁
  exact
    { location := 0
      scale₁ := 1 / (1 + r)
      scale₂ := r / (1 + r)
      scale₁_pos := by positivity
      scale₂_pos := by positivity }

@[simp] theorem d015012
    (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1) :
    (_root_.GD.N0232.N0720.N1072.d015011 m n hm hn t ht₀ ht₁).location = 0 := rfl

@[simp] theorem d015013
    (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1) :
    (_root_.GD.N0232.N0720.N1072.d015011 m n hm hn t ht₀ ht₁).scale₁ =
      1 / (1 + _root_.GD.N0232.N0720.N1072.d015009 m n t) := rfl

@[simp] theorem d015014
    (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1) :
    (_root_.GD.N0232.N0720.N1072.d015011 m n hm hn t ht₀ ht₁).scale₂ =
      _root_.GD.N0232.N0720.N1072.d015009 m n t /
        (1 + _root_.GD.N0232.N0720.N1072.d015009 m n t) := rfl

include hm hn in


theorem d015015
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    theta.scale₂ / theta.scale₁ =
      _root_.GD.N0232.N0720.N1072.d015009 m n
        (_root_.GD.N0232.N0720.N1067.d014408 m n theta) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hm)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  have hs₁ : theta.scale₁ ≠ 0 := theta.scale₁_pos.ne'
  have htotal :
      0 < theta.scale₁ ^ 2 / (m : ℝ) +
        theta.scale₂ ^ 2 / (n : ℝ) := by positivity
  have hratioSq :
      (theta.scale₂ / theta.scale₁) ^ 2 =
        ((n : ℝ) * _root_.GD.N0232.N0720.N1067.d014408 m n theta) /
          ((m : ℝ) *
            (1 - _root_.GD.N0232.N0720.N1067.d014408 m n theta)) := by
    unfold _root_.GD.N0232.N0720.N1067.d014408
    unfold _root_.GD.N0107.d009046
      _root_.GD.N0107.d009045
      _root_.GD.N0107.d009043
      _root_.GD.N0107.d009044
    field_simp [hs₁, ne_of_gt hmpos, ne_of_gt hnpos, ne_of_gt htotal]
    ring
  unfold _root_.GD.N0232.N0720.N1072.d015009
  rw [← hratioSq, Real.sqrt_sq_eq_abs,
    abs_of_pos (div_pos theta.scale₂_pos theta.scale₁_pos)]

theorem d015016
    (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (hsum : theta.scale₁ + theta.scale₂ = 1) :
    theta.scale₁ = 1 / (1 + theta.scale₂ / theta.scale₁) := by
  field_simp [theta.scale₁_pos.ne']
  linarith

theorem d015017
    (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (hsum : theta.scale₁ + theta.scale₂ = 1) :
    theta.scale₂ =
      (theta.scale₂ / theta.scale₁) /
        (1 + theta.scale₂ / theta.scale₁) := by
  have hden :
      1 + theta.scale₂ / theta.scale₁ = 1 / theta.scale₁ := by
    field_simp [theta.scale₁_pos.ne']
    exact hsum
  rw [hden]
  field_simp [theta.scale₁_pos.ne']

include hm in
theorem d015018
    {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    ContinuousAt (_root_.GD.N0232.N0720.N1072.d015009 m n) t := by
  unfold _root_.GD.N0232.N0720.N1072.d015009
  apply Real.continuous_sqrt.continuousAt.comp
  apply ContinuousAt.div
  · exact continuousAt_const.mul continuousAt_id
  · exact continuousAt_const.mul (continuousAt_const.sub continuousAt_id)
  · have hmzero : (m : ℝ) ≠ 0 := by
      exact_mod_cast (show m ≠ 0 by omega)
    exact mul_ne_zero hmzero (sub_ne_zero.mpr (ne_of_gt ht₁))



theorem d015019
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ)
    (ht₀ : 0 < t) (ht₁ : t < 1)
    (hlocation : ∀ j, (thetaSeq j).location = 0)
    (hscaleSum : ∀ j, (thetaSeq j).scale₁ + (thetaSeq j).scale₂ = 1)
    (hfraction : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1067.d014408 m n (thetaSeq j))
      atTop (nhds t)) :
    Tendsto thetaSeq atTop
      (nhds (_root_.GD.N0232.N0720.N1072.d015011 m n hm hn t ht₀ ht₁)) := by
  let ratioSeq : ℕ → ℝ :=
    fun j ↦ (thetaSeq j).scale₂ / (thetaSeq j).scale₁
  let r := _root_.GD.N0232.N0720.N1072.d015009 m n t
  have hratio : Tendsto ratioSeq atTop (nhds r) := by
    have hcomp :=
      (_root_.GD.N0232.N0720.N1072.d015018 m n hm ht₀ ht₁).tendsto.comp
        hfraction
    apply hcomp.congr'
    exact Filter.Eventually.of_forall fun j ↦
      (_root_.GD.N0232.N0720.N1072.d015015
        m n hm hn (thetaSeq j)).symm
  have hrpos : 0 < r := _root_.GD.N0232.N0720.N1072.d015010 m n hm hn ht₀ ht₁
  have hscale₁ : Tendsto (fun j ↦ (thetaSeq j).scale₁) atTop
      (nhds (1 / (1 + r))) := by
    have hcont : ContinuousAt (fun x : ℝ ↦ 1 / (1 + x)) r := by
      exact continuousAt_const.div
        (continuousAt_const.add continuousAt_id)
        (by linarith [hrpos])
    apply (hcont.tendsto.comp hratio).congr'
    exact Filter.Eventually.of_forall fun j ↦
      (_root_.GD.N0232.N0720.N1072.d015016 (thetaSeq j) (hscaleSum j)).symm
  have hscale₂ : Tendsto (fun j ↦ (thetaSeq j).scale₂) atTop
      (nhds (r / (1 + r))) := by
    have hcont : ContinuousAt (fun x : ℝ ↦ x / (1 + x)) r := by
      exact continuousAt_id.div
        (continuousAt_const.add continuousAt_id)
        (by linarith [hrpos])
    apply (hcont.tendsto.comp hratio).congr'
    exact Filter.Eventually.of_forall fun j ↦
      (_root_.GD.N0232.N0720.N1072.d015017 (thetaSeq j) (hscaleSum j)).symm
  rw [_root_.GD.N0232.N0720.N1499.d014996.tendsto_nhds_iff]
  change Tendsto
    (fun j ↦ ((thetaSeq j).location,
      ((thetaSeq j).scale₁, (thetaSeq j).scale₂))) atTop
    (nhds (0, (1 / (1 + r), r / (1 + r))))
  exact
    (tendsto_const_nhds.congr'
      (Filter.Eventually.of_forall fun j ↦ (hlocation j).symm)).prodMk_nhds
      (hscale₁.prodMk_nhds hscale₂)


theorem d015020
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168) (t : ℝ)
    (ht₀ : 0 < t) (ht₁ : t < 1)
    (hfraction : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1067.d014408 m n
        (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))) atTop (nhds t)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j)) atTop
      (nhds (_root_.GD.N0232.N0720.N1072.d015011 m n hm hn t ht₀ ht₁)) := by
  apply _root_.GD.N0232.N0720.N1072.d015019
    m n hm hn (fun j ↦ _root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j)) t ht₀ ht₁
  · exact fun j ↦ _root_.GD.N0232.N0720.N1067.d014403 (thetaSeq j)
  · exact fun j ↦ _root_.GD.N0232.N0720.N1067.d014406 (thetaSeq j)
  · exact hfraction

end

end N1072
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1072.d015015
#print axioms _root_.GD.N0232.N0720.N1072.d015020
