import GD.Module0015
import GD.Module0632
import GD.Module0912
import Mathlib.Topology.MetricSpace.Isometry














open Function MeasureTheory Set Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1499

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0591
open _root_.GD.N0232.N0719.N0932


def d014993 : _root_.GD.N0232.N0720.N1080.d014168 → ℝ × (ℝ × ℝ) :=
  fun theta ↦ (theta.location, (theta.scale₁, theta.scale₂))

theorem d014994 :
    Function.Injective _root_.GD.N0232.N0720.N1499.d014993 := by
  intro theta eta h
  cases theta with
  | mk thetaLocation thetaScale₁ thetaScale₂ htheta₁ htheta₂ =>
    cases eta with
    | mk etaLocation etaScale₁ etaScale₂ heta₁ heta₂ =>
      simp only [_root_.GD.N0232.N0720.N1499.d014993, Prod.mk.injEq] at h
      rcases h with ⟨hlocation, hscale₁, hscale₂⟩
      subst etaLocation
      subst etaScale₁
      subst etaScale₂
      rfl



noncomputable instance d014995 : MetricSpace _root_.GD.N0232.N0720.N1080.d014168 :=
  MetricSpace.induced _root_.GD.N0232.N0720.N1499.d014993 _root_.GD.N0232.N0720.N1499.d014994
    inferInstance

theorem d014996 : Isometry _root_.GD.N0232.N0720.N1499.d014993 :=
  MetricSpace.isometry_induced _root_.GD.N0232.N0720.N1499.d014993
    _root_.GD.N0232.N0720.N1499.d014994

@[fun_prop]
theorem d014997 : Continuous _root_.GD.N0232.N0720.N1499.d014993 :=
  _root_.GD.N0232.N0720.N1499.d014996.continuous

@[fun_prop]
theorem d014998 :
    Continuous (_root_.GD.N0232.N0720.N1080.d014168.location : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) := by
  change Continuous (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ (_root_.GD.N0232.N0720.N1499.d014993 theta).1)
  exact continuous_fst.comp _root_.GD.N0232.N0720.N1499.d014997

@[fun_prop]
theorem d014999 :
    Continuous (_root_.GD.N0232.N0720.N1080.d014168.scale₁ : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) := by
  change Continuous
    (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ (_root_.GD.N0232.N0720.N1499.d014993 theta).2.1)
  exact continuous_fst.comp
    (continuous_snd.comp _root_.GD.N0232.N0720.N1499.d014997)

@[fun_prop]
theorem d015000 :
    Continuous (_root_.GD.N0232.N0720.N1080.d014168.scale₂ : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) := by
  change Continuous
    (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ (_root_.GD.N0232.N0720.N1499.d014993 theta).2.2)
  exact continuous_snd.comp
    (continuous_snd.comp _root_.GD.N0232.N0720.N1499.d014997)



def d015001
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  _root_.GD.N0232.N0719.N0932.d009213
      m theta.location theta.scale₁ omega.1 *
    _root_.GD.N0232.N0719.N0932.d009213
      n theta.location theta.scale₂ omega.2

@[fun_prop]
theorem d015002
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    Measurable (_root_.GD.N0232.N0720.N1499.d015001 m n theta) := by
  exact
    ((_root_.GD.N0232.N0719.N0932.d009214
      m theta.location theta.scale₁).comp measurable_fst).mul
    ((_root_.GD.N0232.N0719.N0932.d009214
      n theta.location theta.scale₂).comp measurable_snd)

theorem d015003
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1499.d015001 m n theta omega := by
  exact mul_nonneg
    (_root_.GD.N0232.N0719.N0932.d009215
      m theta.location theta.scale₁ omega.1)
    (_root_.GD.N0232.N0719.N0932.d009215
      n theta.location theta.scale₂ omega.2)

theorem d015004
    (sampleSize : ℕ) (location scale : ℝ) (hscale : scale ≠ 0)
    (x : _root_.GD.N0137.d008894 sampleSize) :
    0 < _root_.GD.N0232.N0719.N0932.d009213 sampleSize location scale x := by
  unfold _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  apply Finset.prod_pos
  intro i hi
  unfold _root_.GD.N0232.N0719.N0932.d009204
  exact ENNReal.toReal_pos
    (ne_of_gt (_root_.GD.N0232.N0719.N0932.d009200 location scale (x i) hscale))
    (_root_.GD.N0232.N0719.N0932.d009199 location scale (x i))

theorem d015005
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 < _root_.GD.N0232.N0720.N1499.d015001 m n theta omega := by
  exact mul_pos
    (_root_.GD.N0232.N0720.N1499.d015004
      m theta.location theta.scale₁ theta.scale₁_pos.ne' omega.1)
    (_root_.GD.N0232.N0720.N1499.d015004
      n theta.location theta.scale₂ theta.scale₂_pos.ne' omega.2)


theorem d015006
    (m n : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014171 m n theta =
      (_root_.GD.N0232.N0720.N1080.d014172 m n).withDensity
        (fun omega ↦ ENNReal.ofReal
          (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega)) := by
  change _root_.GD.N0107.d009030
      m n theta.location theta.scale₁ theta.scale₂ =
    (_root_.GD.N0107.d009030 m n 0 1 1).withDensity
      (fun omega ↦ ENNReal.ofReal
        (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega))
  rw [_root_.GD.N0232.N0720.d009061,
    _root_.GD.N0232.N0720.d009061]
  change
    (_root_.GD.N0232.N0719.d009174
        m theta.location theta.scale₁).prod
      (_root_.GD.N0232.N0719.d009174
        n theta.location theta.scale₂) =
    ((_root_.GD.N0232.N0719.d009174 m 0 1).prod
      (_root_.GD.N0232.N0719.d009174 n 0 1)).withDensity
        (fun omega ↦ ENNReal.ofReal
          (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega))
  rw [_root_.GD.N0232.N0719.N0932.d009217
      m theta.location theta.scale₁ theta.scale₁_pos.ne',
    _root_.GD.N0232.N0719.N0932.d009217
      n theta.location theta.scale₂ theta.scale₂_pos.ne',
    _root_.GD.N0232.N0719.N0932.d009212, _root_.GD.N0232.N0719.N0932.d009212,
    prod_withDensity]
  congr 1
  funext omega
  rw [← ENNReal.ofReal_mul
    (_root_.GD.N0232.N0719.N0932.d009215
      m theta.location theta.scale₁ omega.1)]
  rfl
  · exact (_root_.GD.N0232.N0719.N0932.d009214
      m theta.location theta.scale₁).ennreal_ofReal
  · exact (_root_.GD.N0232.N0719.N0932.d009214
      n theta.location theta.scale₂).ennreal_ofReal

@[fun_prop]
theorem d015007
    (m n : ℕ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    Continuous (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦
      _root_.GD.N0232.N0720.N1499.d015001 m n theta omega) := by
  let firstParameter : _root_.GD.N0232.N0720.N1080.d014168 → ℝ × Set.Ioi (0 : ℝ) :=
    fun theta ↦ (theta.location, ⟨theta.scale₁, theta.scale₁_pos⟩)
  let secondParameter : _root_.GD.N0232.N0720.N1080.d014168 → ℝ × Set.Ioi (0 : ℝ) :=
    fun theta ↦ (theta.location, ⟨theta.scale₂, theta.scale₂_pos⟩)
  have hfirstParameter : Continuous firstParameter := by
    exact _root_.GD.N0232.N0720.N1499.d014998.prodMk
      (_root_.GD.N0232.N0720.N1499.d014999.subtype_mk
        (fun theta ↦ theta.scale₁_pos))
  have hsecondParameter : Continuous secondParameter := by
    exact _root_.GD.N0232.N0720.N1499.d014998.prodMk
      (_root_.GD.N0232.N0720.N1499.d015000.subtype_mk
        (fun theta ↦ theta.scale₂_pos))
  have hfirst : Continuous (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦
      _root_.GD.N0232.N0719.N0932.d009213
        m theta.location theta.scale₁ omega.1) := by
    change Continuous
      ((fun theta : ℝ × Set.Ioi (0 : ℝ) ↦
          _root_.GD.N0232.N0719.N0932.d009213 m theta.1 theta.2 omega.1) ∘
        firstParameter)
    exact
      (_root_.GD.N0232.N0719.N0932.d009218 m omega.1).comp
        hfirstParameter
  have hsecond : Continuous (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦
      _root_.GD.N0232.N0719.N0932.d009213
        n theta.location theta.scale₂ omega.2) := by
    change Continuous
      ((fun theta : ℝ × Set.Ioi (0 : ℝ) ↦
          _root_.GD.N0232.N0719.N0932.d009213 n theta.1 theta.2 omega.2) ∘
        secondParameter)
    exact
      (_root_.GD.N0232.N0719.N0932.d009218 n omega.2).comp
        hsecondParameter
  exact hfirst.mul hsecond

set_option maxHeartbeats 800000 in


theorem d015008
    (m n : ℕ) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    LowerSemicontinuous (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta d) := by
  exact _root_.GD.N0230.N0591.d000131
    (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n)
    (_root_.GD.N0232.N0720.N1499.d015001 m n) _root_.GD.N0232.N0720.N1080.d014168.location d
    (_root_.GD.N0232.N0720.N1499.d015006 m n)
    (_root_.GD.N0232.N0720.N1499.d015002 m n)
    (_root_.GD.N0232.N0720.N1499.d015003 m n)
    (_root_.GD.N0232.N0720.N1499.d015007 m n)
    _root_.GD.N0232.N0720.N1499.d014998

end

end N1499
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1499.d015006
#print axioms _root_.GD.N0232.N0720.N1499.d015007
#print axioms _root_.GD.N0232.N0720.N1499.d015008
