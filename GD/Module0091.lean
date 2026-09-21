import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import GD.Module0089
















open Set

namespace GD
namespace N0230
namespace N0633

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]



noncomputable def d001198 : WeakSpace ℝ H ≃ₜ WeakDual ℝ H where
  toFun x := StrongDual.toWeakDual
    (InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x))
  invFun f := toWeakSpace ℝ H
    ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual f))
  left_inv x := by
    change toWeakSpace ℝ H
        ((InnerProductSpace.toDual ℝ H).symm
          (WeakDual.toStrongDual
            (StrongDual.toWeakDual
              (InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x))))) = x
    rw [show WeakDual.toStrongDual
          (StrongDual.toWeakDual
            (InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x))) =
          InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x) from
        StrongDual.toWeakDual.symm_apply_apply _]
    rw [(InnerProductSpace.toDual ℝ H).symm_apply_apply,
      (toWeakSpace ℝ H).apply_symm_apply]
  right_inv f := by
    change StrongDual.toWeakDual
        (InnerProductSpace.toDual ℝ H
          ((InnerProductSpace.toDual ℝ H).symm
            (WeakDual.toStrongDual f))) = f
    rw [(InnerProductSpace.toDual ℝ H).apply_symm_apply]
    exact StrongDual.toWeakDual.apply_symm_apply f
  continuous_toFun := by
    apply WeakDual.continuous_of_continuous_eval
    intro y
    have h := WeakBilin.eval_continuous
      (topDualPairing ℝ H).flip (InnerProductSpace.toDual ℝ H y)
    have heq :
        (fun x : WeakSpace ℝ H =>
          (StrongDual.toWeakDual
            (InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x))) y) =
          fun x : WeakSpace ℝ H =>
            ((topDualPairing ℝ H).flip x)
              (InnerProductSpace.toDual ℝ H y) := by
      funext x
      change inner ℝ ((toWeakSpace ℝ H).symm x) y =
        inner ℝ y ((toWeakSpace ℝ H).symm x)
      exact real_inner_comm _ _
    rw [heq]
    exact h
  continuous_invFun := by
    apply WeakBilin.continuous_of_continuous_eval
    intro f
    let y : H := (InnerProductSpace.toDual ℝ H).symm f
    have h : Continuous (fun a : WeakDual ℝ H => a y) :=
      WeakDual.eval_continuous y
    have heq :
        (fun a : WeakDual ℝ H =>
          ((topDualPairing ℝ H).flip
            (toWeakSpace ℝ H
              ((InnerProductSpace.toDual ℝ H).symm
                (WeakDual.toStrongDual a)))) f) =
          fun a => a y := by
      funext a
      calc
        ((topDualPairing ℝ H).flip
            (toWeakSpace ℝ H
              ((InnerProductSpace.toDual ℝ H).symm
                (WeakDual.toStrongDual a)))) f =
            f ((InnerProductSpace.toDual ℝ H).symm
              (WeakDual.toStrongDual a)) := rfl
        _ = inner ℝ y ((InnerProductSpace.toDual ℝ H).symm
              (WeakDual.toStrongDual a)) := by
                rw [show f = InnerProductSpace.toDual ℝ H y by
                  simp [y]]
                exact InnerProductSpace.toDual_apply_apply
        _ = inner ℝ ((InnerProductSpace.toDual ℝ H).symm
              (WeakDual.toStrongDual a)) y := real_inner_comm _ _
        _ = WeakDual.toStrongDual a y :=
          InnerProductSpace.toDual_symm_apply
        _ = a y := rfl
    rw [heq]
    exact h




theorem d001199 (r : ℝ) :
    IsCompact (toWeakSpace ℝ H '' Metric.closedBall (0 : H) r) := by
  have hdual := WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) r
  have himage := hdual.image (_root_.GD.N0230.N0633.d001198 (H := H)).symm.continuous
  convert himage using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y), ?_, ?_⟩
    · change WeakDual.toStrongDual
          (StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y)) ∈
            Metric.closedBall (0 : StrongDual ℝ H) r
      rw [show WeakDual.toStrongDual
          (StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y)) =
            InnerProductSpace.toDual ℝ H y from
          StrongDual.toWeakDual.symm_apply_apply _]
      simpa using hy
    · apply (toWeakSpace ℝ H).injective
      change (InnerProductSpace.toDual ℝ H).symm
          (WeakDual.toStrongDual
            (StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y))) = y
      rw [show WeakDual.toStrongDual
          (StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y)) =
            InnerProductSpace.toDual ℝ H y from
          StrongDual.toWeakDual.symm_apply_apply _]
      exact (InnerProductSpace.toDual ℝ H).symm_apply_apply y
  · rintro ⟨f, hf, rfl⟩
    refine ⟨(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual f), ?_, ?_⟩
    · simpa using hf
    · rfl



theorem d001200
    {K : Set H} (r : ℝ)
    (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKball : K ⊆ Metric.closedBall (0 : H) r) :
    IsCompact (toWeakSpace ℝ H '' K) := by
  apply (_root_.GD.N0230.N0633.d001199 (H := H) r).of_isClosed_subset
    (_root_.GD.N0230.N0708.d001175
      hKconv hKclosed)
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hKball hx, rfl⟩


theorem d001201
    {K : Set H} (r : ℝ)
    (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKnorm : ∀ x ∈ K, ‖x‖ ≤ r) :
    IsCompact (toWeakSpace ℝ H '' K) := by
  apply _root_.GD.N0230.N0633.d001200
    r hKconv hKclosed
  intro x hx
  simpa [Metric.mem_closedBall] using hKnorm x hx

end
end N0633
end N0230
end GD
