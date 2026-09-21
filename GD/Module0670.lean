import GD.Module0637
import GD.Module0253
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration












open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0232.N0719.N1004

noncomputable section

open _root_.GD.N0232.N0719.N0886


def d009794 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (i : Fin k) : Prop :=
  i ∈ Set.range triangle

local instance d009795 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    DecidablePred (_root_.GD.N0232.N0719.N1004.d009794 triangle) :=
  fun i => Classical.propDecidable (_root_.GD.N0232.N0719.N1004.d009794 triangle i)


noncomputable def d009796 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    Fin 3 ≃ Subtype (_root_.GD.N0232.N0719.N1004.d009794 triangle) :=
  Equiv.ofInjective triangle triangle.injective








noncomputable def d009797 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    (Fin k → ℝ) → (Fin 3 → ℝ) :=
  fun y j => y (triangle j)

@[simp]
theorem d009798 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k)
    (y : Fin k → ℝ) (j : Fin 3) :
    _root_.GD.N0232.N0719.N1004.d009797 triangle y j = y (triangle j) := by
  rfl





theorem d009799
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (μ : Fin k → Measure ℝ)
    [∀ i, SigmaFinite (μ i)]
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving
      (_root_.GD.N0232.N0719.N1004.d009797 triangle)
      (Measure.pi μ)
      (Measure.pi fun j : Fin 3 => μ (triangle j)) := by
  classical
  let p : Fin k → Prop := _root_.GD.N0232.N0719.N1004.d009794 triangle
  let e : Fin 3 ≃ Subtype p := _root_.GD.N0232.N0719.N1004.d009796 triangle
  have hsplit :=
    measurePreserving_piEquivPiSubtypeProd μ p
  have hfst :
      MeasurePreserving
        Prod.fst
        ((Measure.pi fun i : Subtype p => μ i).prod
          (Measure.pi fun i : Subtype (fun i => ¬p i) => μ i))
        (Measure.pi fun i : Subtype p => μ i) :=
    measurePreserving_fst
  have hreindex :=
    (measurePreserving_piCongrLeft
      (fun i : Subtype p => μ i) e).symm
  have hcomp := hreindex.comp (hfst.comp hsplit)
  have hfun :
      ((MeasurableEquiv.piCongrLeft
          (fun _ : Subtype p => ℝ) e).symm ∘
        Prod.fst ∘
        MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : Fin k => ℝ) p) =
        _root_.GD.N0232.N0719.N1004.d009797 triangle := by
    funext y j
    change
      (Equiv.piCongrLeft (fun _ : Subtype p => ℝ) e).symm
          (fun i : Subtype p => y i) j =
        y (triangle j)
    rw [Equiv.piCongrLeft_symm_apply]
    rfl
  rw [hfun] at hcomp
  have he :
      (fun j : Fin 3 => μ (e j)) =
        fun j : Fin 3 => μ (triangle j) := by
    funext j
    rfl
  rw [he] at hcomp
  exact hcomp



noncomputable def d009800 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    (Fin k → ℝ) →
      (Subtype (fun i => ¬_root_.GD.N0232.N0719.N1004.d009794 triangle i) → ℝ) :=
  fun y i => y i

@[simp]
theorem d009801 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k)
    (y : Fin k → ℝ)
    (i : Subtype (fun i => ¬_root_.GD.N0232.N0719.N1004.d009794 triangle i)) :
    _root_.GD.N0232.N0719.N1004.d009800 triangle y i = y i := by
  rfl



theorem d009802
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (μ : Fin k → Measure ℝ)
    [∀ i, SigmaFinite (μ i)]
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving
      (_root_.GD.N0232.N0719.N1004.d009800 triangle)
      (Measure.pi μ)
      (Measure.pi fun
        i : Subtype (fun i => ¬_root_.GD.N0232.N0719.N1004.d009794 triangle i) => μ i) := by
  classical
  let p : Fin k → Prop := _root_.GD.N0232.N0719.N1004.d009794 triangle
  have hsplit :=
    measurePreserving_piEquivPiSubtypeProd μ p
  have hsnd :
      MeasurePreserving
        Prod.snd
        ((Measure.pi fun i : Subtype p => μ i).prod
          (Measure.pi fun i : Subtype (fun i => ¬p i) => μ i))
        (Measure.pi fun i : Subtype (fun i => ¬p i) => μ i) :=
    measurePreserving_snd
  have hcomp := hsnd.comp hsplit
  have hfun :
      (Prod.snd ∘
        MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : Fin k => ℝ) p) =
        _root_.GD.N0232.N0719.N1004.d009800 triangle := by
    funext y i
    rfl
  rw [hfun] at hcomp
  exact hcomp






theorem d009803
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (μ : Fin k → Measure ℝ)
    [∀ i, SigmaFinite (μ i)]
    [∀ i, IsProbabilityMeasure (μ i)] :
    IndepFun
      (_root_.GD.N0232.N0719.N1004.d009797 triangle)
      (_root_.GD.N0232.N0719.N1004.d009800 triangle)
      (Measure.pi μ) := by
  classical
  let p : Fin k → Prop := _root_.GD.N0232.N0719.N1004.d009794 triangle
  let e : Fin 3 ≃ Subtype p := _root_.GD.N0232.N0719.N1004.d009796 triangle
  have hsplit :=
    measurePreserving_piEquivPiSubtypeProd μ p
  have hreindex :=
    (measurePreserving_piCongrLeft
      (fun i : Subtype p => μ i) e).symm
  have hjoint :
      MeasurePreserving
        (fun y =>
          (_root_.GD.N0232.N0719.N1004.d009797 triangle y,
            _root_.GD.N0232.N0719.N1004.d009800 triangle y))
        (Measure.pi μ)
        ((Measure.pi fun j : Fin 3 => μ (triangle j)).prod
          (Measure.pi fun
            i : Subtype (fun i => ¬_root_.GD.N0232.N0719.N1004.d009794 triangle i) => μ i)) := by
    have hprod :=
      hreindex.prod
        (MeasurePreserving.id
          (Measure.pi fun i : Subtype (fun i => ¬p i) => μ i))
    have hcomp := hprod.comp hsplit
    have hfun :
        (Prod.map
          (MeasurableEquiv.piCongrLeft
            (fun _ : Subtype p => ℝ) e).symm id ∘
          MeasurableEquiv.piEquivPiSubtypeProd
            (fun _ : Fin k => ℝ) p) =
          fun y =>
            (_root_.GD.N0232.N0719.N1004.d009797 triangle y,
              _root_.GD.N0232.N0719.N1004.d009800 triangle y) := by
      funext y
      apply Prod.ext
      · funext j
        change
          (Equiv.piCongrLeft (fun _ : Subtype p => ℝ) e).symm
              (fun i : Subtype p => y i) j =
            y (triangle j)
        rw [Equiv.piCongrLeft_symm_apply]
        rfl
      · funext i
        rfl
    rw [hfun] at hcomp
    have he :
        (fun j : Fin 3 => μ (e j)) =
          fun j : Fin 3 => μ (triangle j) := by
      funext j
      rfl
    rw [he] at hcomp
    exact hcomp
  apply
    (indepFun_iff_map_prod_eq_prod_map_map
      (_root_.GD.N0232.N0719.N1004.d009799 triangle μ).measurable.aemeasurable
      (_root_.GD.N0232.N0719.N1004.d009802 triangle μ).measurable.aemeasurable).2
  rw [hjoint.map_eq,
    (_root_.GD.N0232.N0719.N1004.d009799 triangle μ).map_eq,
    (_root_.GD.N0232.N0719.N1004.d009802 triangle μ).map_eq]



def d009804 :
    (Fin 3 → ℝ) → ℝ × (ℝ × ℝ) :=
  fun y => (y 0, (y 1, y 2))

@[fun_prop]
theorem d009805 :
    Measurable _root_.GD.N0232.N0719.N1004.d009804 := by
  unfold _root_.GD.N0232.N0719.N1004.d009804
  fun_prop



theorem d009806
    (μ : Fin 3 → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving
      _root_.GD.N0232.N0719.N1004.d009804
      (Measure.pi μ)
      ((μ 0).prod ((μ 1).prod (μ 2))) := by
  have hhead :=
    measurePreserving_piFinSuccAbove μ (0 : Fin 3)
  have htail :=
    measurePreserving_piFinTwo
      (fun j : Fin 2 => μ ((0 : Fin 3).succAbove j))
  have hprod :=
    (MeasurePreserving.id (μ 0)).prod htail
  have hcomp := hprod.comp hhead
  have hfun :
      (Prod.map id
          (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) ∘
        MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin 3 => ℝ) (0 : Fin 3)) =
        _root_.GD.N0232.N0719.N1004.d009804 := by
    funext y
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> rfl
  rw [hfun] at hcomp
  simpa using hcomp


def d009807 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    (Fin k → ℝ) → ℝ × (ℝ × ℝ) :=
  fun y => _root_.GD.N0232.N0719.N1004.d009804 (_root_.GD.N0232.N0719.N1004.d009797 triangle y)

@[simp]
theorem d009808 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k)
    (y : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N1004.d009807 triangle y =
      (y (triangle 0), (y (triangle 1), y (triangle 2))) := by
  simp [_root_.GD.N0232.N0719.N1004.d009807, _root_.GD.N0232.N0719.N1004.d009804]





theorem d009809
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (μ : Fin k → Measure ℝ)
    [∀ i, SigmaFinite (μ i)]
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving
      (_root_.GD.N0232.N0719.N1004.d009807 triangle)
      (Measure.pi μ)
      ((μ (triangle 0)).prod
        ((μ (triangle 1)).prod (μ (triangle 2)))) := by
  exact
    (_root_.GD.N0232.N0719.N1004.d009806
      (fun j : Fin 3 => μ (triangle j))).comp
      (_root_.GD.N0232.N0719.N1004.d009799 triangle μ)





theorem d009810
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (v : Fin k → ℝ≥0) :
    MeasurePreserving
      (_root_.GD.N0232.N0719.N1004.d009807 triangle)
      (Measure.pi fun i => gaussianReal 0 (v i))
      (_root_.GD.N0232.N0719.N0886.d003649
        (v (triangle 0)) (v (triangle 1)) (v (triangle 2))) := by
  simpa [_root_.GD.N0232.N0719.N0886.d003649] using
    _root_.GD.N0232.N0719.N1004.d009809 triangle
      (fun i => gaussianReal 0 (v i))





theorem d009811
    {k : ℕ}
    (triangle : Fin 3 ↪ Fin k)
    (v : Fin k → ℝ≥0)
    (c : Fin k → ℝ) :
    (∫ y : Fin k → ℝ,
        ∑ i with ¬_root_.GD.N0232.N0719.N1004.d009794 triangle i, c i * y i
      ∂Measure.pi (fun i => gaussianReal 0 (v i))) = 0 := by
  classical
  rw [integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro i hi
    rw [integral_const_mul, integral_eval]
    simp
  · intro i hi
    have hId :
        Integrable (fun x : ℝ => x) (gaussianReal 0 (v i)) := by
      simpa only [pow_one] using
        _root_.GD.N0232.N0719.N0886.d003647 (v i) 1
    exact
      (integrable_comp_eval
        (X := fun _ : Fin k => ℝ)
        (μ := fun j : Fin k => gaussianReal 0 (v j))
        (i := i) (f := fun x : ℝ => x) hId).const_mul (c i)


def d009812 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k)
    (c : Fin k → ℝ)
    (u : Subtype (fun i => ¬_root_.GD.N0232.N0719.N1004.d009794 triangle i) → ℝ) : ℝ := by
  classical
  exact ∑ i : Subtype (fun i => ¬_root_.GD.N0232.N0719.N1004.d009794 triangle i), c i * u i

@[fun_prop]
theorem d009813
    {k : ℕ}
    (triangle : Fin 3 ↪ Fin k)
    (c : Fin k → ℝ) :
    Measurable (_root_.GD.N0232.N0719.N1004.d009812 triangle c) := by
  classical
  unfold _root_.GD.N0232.N0719.N1004.d009812
  fun_prop



theorem d009814
    {k : ℕ}
    (triangle : Fin 3 ↪ Fin k)
    (v : Fin k → ℝ≥0)
    (c : Fin k → ℝ) :
    (∫ u,
        _root_.GD.N0232.N0719.N1004.d009812 triangle c u
      ∂Measure.pi (fun
        i : Subtype (fun i => ¬_root_.GD.N0232.N0719.N1004.d009794 triangle i) =>
          gaussianReal 0 (v i))) = 0 := by
  classical
  unfold _root_.GD.N0232.N0719.N1004.d009812
  rw [integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro i hi
    rw [integral_const_mul, integral_eval]
    simp
  · intro i hi
    have hId :
        Integrable (fun x : ℝ => x) (gaussianReal 0 (v i)) := by
      simpa only [pow_one] using
        _root_.GD.N0232.N0719.N0886.d003647 (v i) 1
    exact
      (integrable_comp_eval
        (X := fun _ : Subtype
          (fun j => ¬_root_.GD.N0232.N0719.N1004.d009794 triangle j) => ℝ)
        (μ := fun j : Subtype
          (fun j => ¬_root_.GD.N0232.N0719.N1004.d009794 triangle j) =>
            gaussianReal 0 (v j))
        (i := i) (f := fun x : ℝ => x) hId).const_mul (c i)






theorem d009815
    {k : ℕ}
    (triangle : Fin 3 ↪ Fin k)
    (v : Fin k → ℝ≥0)
    (c : Fin k → ℝ)
    (F : (Fin 3 → ℝ) → ℝ)
    (hF : Measurable F) :
    (∫ y : Fin k → ℝ,
        F (_root_.GD.N0232.N0719.N1004.d009797 triangle y) *
          _root_.GD.N0232.N0719.N1004.d009812 triangle c
            (_root_.GD.N0232.N0719.N1004.d009800 triangle y)
      ∂Measure.pi (fun i => gaussianReal 0 (v i))) = 0 := by
  classical
  let μ := Measure.pi (fun i => gaussianReal 0 (v i))
  have hind :=
    (_root_.GD.N0232.N0719.N1004.d009803 triangle
      (fun i => gaussianReal 0 (v i))).comp
      hF (_root_.GD.N0232.N0719.N1004.d009813 triangle c)
  have hfactor :=
    hind.integral_mul_eq_mul_integral
      ((hF.comp
        (_root_.GD.N0232.N0719.N1004.d009799 triangle
          (fun i => gaussianReal 0 (v i))).measurable).aestronglyMeasurable)
      (((_root_.GD.N0232.N0719.N1004.d009813 triangle c).comp
        (_root_.GD.N0232.N0719.N1004.d009802 triangle
          (fun i => gaussianReal 0 (v i))).measurable).aestronglyMeasurable)
  change
    (∫ y : Fin k → ℝ,
      ((F ∘ _root_.GD.N0232.N0719.N1004.d009797 triangle) *
        (_root_.GD.N0232.N0719.N1004.d009812 triangle c ∘
          _root_.GD.N0232.N0719.N1004.d009800 triangle)) y
      ∂Measure.pi (fun i => gaussianReal 0 (v i))) = 0
  rw [hfactor]
  have hcomp :
      (∫ y : Fin k → ℝ,
          (_root_.GD.N0232.N0719.N1004.d009812 triangle c ∘
            _root_.GD.N0232.N0719.N1004.d009800 triangle) y
        ∂Measure.pi (fun i => gaussianReal 0 (v i))) =
        ∫ u,
          _root_.GD.N0232.N0719.N1004.d009812 triangle c u
        ∂Measure.pi (fun
          i : Subtype (fun i => ¬_root_.GD.N0232.N0719.N1004.d009794 triangle i) =>
            gaussianReal 0 (v i)) := by
    let hmp :=
      _root_.GD.N0232.N0719.N1004.d009802 triangle
        (fun i => gaussianReal 0 (v i))
    calc
      _ = ∫ u,
          _root_.GD.N0232.N0719.N1004.d009812 triangle c u
        ∂Measure.map (_root_.GD.N0232.N0719.N1004.d009800 triangle)
          (Measure.pi (fun i => gaussianReal 0 (v i))) := by
        exact
          (integral_map hmp.measurable.aemeasurable
            (_root_.GD.N0232.N0719.N1004.d009813 triangle c).aestronglyMeasurable).symm
      _ = _ := by rw [hmp.map_eq]
  rw [hcomp, _root_.GD.N0232.N0719.N1004.d009814]
  ring

end

end GD.N0232.N0719.N1004
