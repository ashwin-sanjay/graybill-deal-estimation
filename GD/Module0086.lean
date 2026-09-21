import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Topology.Algebra.ContinuousAffineMap


























namespace GD
namespace N0230
namespace N0703

open Function Set

variable {D T A : Type*}


def d001139 (act : T → D → D) (C : Set D) : Set D :=
  {x | x ∈ C ∧ ∀ t, act t x = x}

@[simp]
theorem d001140
    (act : T → D → D) (C : Set D) (x : D) :
    x ∈ _root_.GD.N0230.N0703.d001139 act C ↔
      x ∈ C ∧ ∀ t, act t x = x := Iff.rfl

theorem d001141
    (act : T → D → D) (C : Set D) :
    _root_.GD.N0230.N0703.d001139 act C ⊆ C := by
  intro x hx
  exact hx.1


theorem d001142
    (act : T → D → D) (C : Set D) :
    _root_.GD.N0230.N0703.d001139 act C =
      C ∩ ⋂ t, fixedPoints (act t) := by
  ext x
  simp [_root_.GD.N0230.N0703.d001139, fixedPoints, IsFixedPt]


theorem d001143
    [TopologicalSpace D] [T2Space D]
    (act : T → D → D) (C : Set D)
    (hC : IsClosed C) (hcontinuous : ∀ t, Continuous (act t)) :
    IsClosed (_root_.GD.N0230.N0703.d001139 act C) := by
  rw [_root_.GD.N0230.N0703.d001142]
  exact hC.inter (isClosed_iInter fun t ↦
    isClosed_fixedPoints (hcontinuous t))



theorem d001144
    [TopologicalSpace D] [T2Space D]
    (act : T → D → D) (C : Set D)
    (hC : IsCompact C) (hcontinuous : ∀ t, Continuous (act t)) :
    IsCompact (_root_.GD.N0230.N0703.d001139 act C) := by
  rw [_root_.GD.N0230.N0703.d001142]
  exact hC.inter_right (isClosed_iInter fun t ↦
    isClosed_fixedPoints (hcontinuous t))


theorem d001145
    [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
    (f : D →ᴬ[ℝ] D) :
    Convex ℝ (fixedPoints f) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  rw [mem_fixedPoints_iff] at hx hy ⊢
  have hab' : 1 - b = a := by linarith
  calc
    f (a • x + b • y) =
        f (AffineMap.lineMap x y b) := by
          rw [AffineMap.lineMap_apply_module, hab']
    _ = AffineMap.lineMap (f x) (f y) b := by
          exact ContinuousAffineMap.apply_lineMap f x y b
    _ = AffineMap.lineMap x y b := by rw [hx, hy]
    _ = a • x + b • y := by
          rw [AffineMap.lineMap_apply_module, hab']



theorem d001146
    [AddCommGroup D] [Module ℝ D] [TopologicalSpace D]
    (act : T → (D →ᴬ[ℝ] D)) (C : Set D)
    (hC : Convex ℝ C) :
    Convex ℝ (_root_.GD.N0230.N0703.d001139 (fun t ↦ act t) C) := by
  rw [_root_.GD.N0230.N0703.d001142]
  exact hC.inter (convex_iInter fun t ↦
    _root_.GD.N0230.N0703.d001145 (act t))





def d001147
    (outer : A → D → D) (inner : T → D → D) : Prop :=
  ∀ a t, ∃ t', inner t ∘ outer a = outer a ∘ inner t'



def d001148 (act : T → D → D) : Prop :=
  ∀ s t, Function.Commute (act s) (act t)









def d001149
    [TopologicalSpace D] [AddCommGroup D] [Module ℝ D]
    (act : T → (D →ᴬ[ℝ] D)) (C : Set D) : Prop :=
  IsCompact C →
    Convex ℝ C →
    C.Nonempty →
    (∀ t, MapsTo (act t) C C) →
    _root_.GD.N0230.N0703.d001148 (fun t ↦ act t) →
    (_root_.GD.N0230.N0703.d001139 (fun t ↦ act t) C).Nonempty



theorem d001150
    (outer : A → D → D) (inner : T → D → D) (C : Set D)
    (hnormal : _root_.GD.N0230.N0703.d001147 outer inner)
    (houterC : ∀ a, MapsTo (outer a) C C) :
    ∀ a, MapsTo (outer a)
      (_root_.GD.N0230.N0703.d001139 inner C) (_root_.GD.N0230.N0703.d001139 inner C) := by
  intro a x hx
  refine ⟨houterC a hx.1, ?_⟩
  intro t
  obtain ⟨t', hconj⟩ := hnormal a t
  have happ := congrFun hconj x
  change inner t (outer a x) = outer a x
  calc
    inner t (outer a x) = outer a (inner t' x) := happ
    _ = outer a x := by rw [hx.2 t']



theorem d001151
    (outer : A → D → D) (inner : T → D → D) (C : Set D)
    {x : D}
    (hx : x ∈ _root_.GD.N0230.N0703.d001139 outer
      (_root_.GD.N0230.N0703.d001139 inner C)) :
    x ∈ C ∧ (∀ t, inner t x = x) ∧
      ∀ a, outer a x = x := by
  exact ⟨hx.1.1, hx.1.2, hx.2⟩








theorem d001152
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    (inner : T → (D →ᴬ[ℝ] D))
    (outer : A → (D →ᴬ[ℝ] D))
    (C : Set D)
    (hcompact : IsCompact C)
    (hconvex : Convex ℝ C)
    (hnormal : _root_.GD.N0230.N0703.d001147 (fun a ↦ outer a) (fun t ↦ inner t))
    (houterC : ∀ a, MapsTo (outer a) C C)
    (hfirst : (_root_.GD.N0230.N0703.d001139 (fun t ↦ inner t) C).Nonempty)
    (houterCommutes : _root_.GD.N0230.N0703.d001148 (fun a ↦ outer a))
    (hsecond : _root_.GD.N0230.N0703.d001149 outer
      (_root_.GD.N0230.N0703.d001139 (fun t ↦ inner t) C)) :
    ∃ x, x ∈ C ∧ (∀ t, inner t x = x) ∧
      ∀ a, outer a x = x := by



  have _hfirstCompact : IsCompact
      (_root_.GD.N0230.N0703.d001139 (fun t ↦ inner t) C) :=
    _root_.GD.N0230.N0703.d001144 (fun t ↦ inner t) C hcompact
      (fun t ↦ (inner t).continuous)
  have _hfirstConvex : Convex ℝ
      (_root_.GD.N0230.N0703.d001139 (fun t ↦ inner t) C) :=
    _root_.GD.N0230.N0703.d001146 inner C hconvex
  have _houterFirst : ∀ a, MapsTo (outer a)
      (_root_.GD.N0230.N0703.d001139 (fun t ↦ inner t) C)
      (_root_.GD.N0230.N0703.d001139 (fun t ↦ inner t) C) :=
    _root_.GD.N0230.N0703.d001150
      (fun a ↦ outer a) (fun t ↦ inner t) C hnormal houterC
  obtain ⟨x, hx⟩ := hsecond _hfirstCompact _hfirstConvex hfirst
    _houterFirst houterCommutes
  exact ⟨x, _root_.GD.N0230.N0703.d001151
    (fun a ↦ outer a) (fun t ↦ inner t) C hx⟩









theorem d001153
    [TopologicalSpace D] [T2Space D]
    [AddCommGroup D] [Module ℝ D]
    (inner : T → (D →ᴬ[ℝ] D))
    (outer : A → (D →ᴬ[ℝ] D))
    (C : Set D)
    (hcompact : IsCompact C)
    (hconvex : Convex ℝ C)
    (hne : C.Nonempty)
    (hinnerC : ∀ t, MapsTo (inner t) C C)
    (hinnerCommutes : _root_.GD.N0230.N0703.d001148 (fun t ↦ inner t))
    (hnormal : _root_.GD.N0230.N0703.d001147 (fun a ↦ outer a) (fun t ↦ inner t))
    (houterC : ∀ a, MapsTo (outer a) C C)
    (houterCommutes : _root_.GD.N0230.N0703.d001148 (fun a ↦ outer a))
    (hinnerFixed : _root_.GD.N0230.N0703.d001149 inner C)
    (houterFixed : _root_.GD.N0230.N0703.d001149 outer
      (_root_.GD.N0230.N0703.d001139 (fun t ↦ inner t) C)) :
    ∃ x, x ∈ C ∧ (∀ t, inner t x = x) ∧
      ∀ a, outer a x = x := by
  have hfirst :
      (_root_.GD.N0230.N0703.d001139 (fun t ↦ inner t) C).Nonempty :=
    hinnerFixed hcompact hconvex hne hinnerC hinnerCommutes
  exact _root_.GD.N0230.N0703.d001152 inner outer C hcompact hconvex
    hnormal houterC hfirst houterCommutes houterFixed

end N0703
end N0230
end GD

#print axioms _root_.GD.N0230.N0703.d001144
#print axioms _root_.GD.N0230.N0703.d001146
#print axioms _root_.GD.N0230.N0703.d001150
#print axioms _root_.GD.N0230.N0703.d001152
#print axioms _root_.GD.N0230.N0703.d001153
