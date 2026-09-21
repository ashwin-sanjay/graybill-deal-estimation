import GD.Module0913
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GD.N0076.N0312

noncomputable section

variable {X Y Z Θ : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z]

def d022661 (μ : Measure X) (c : ℝ) (d : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((d x - c) ^ 2) ∂μ

theorem d022662 (μ : Measure X) (T : X → Y) (hT : Measurable T)
    (c : ℝ) (d : Y → ℝ) (hd : Measurable d) :
    _root_.GD.N0076.N0312.d022661 (μ.map T) c d = _root_.GD.N0076.N0312.d022661 μ c (d ∘ T) := by
  exact lintegral_map (by fun_prop) hT

theorem d022663 (μ : Measure X) (c : ℝ)
    (s : Set X) (hs : MeasurableSet s) :
    _root_.GD.N0076.N0312.d022661 μ c (fun x => c + s.indicator (fun _ => (1 : ℝ)) x) = μ s := by
  have h : (fun x => ENNReal.ofReal
      (((c + s.indicator (fun _ => (1 : ℝ)) x) - c) ^ 2)) =
      s.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [_root_.GD.N0076.N0312.d022661, h]
  exact lintegral_indicator_const hs 1 |>.trans (one_mul _)



theorem d022664 (μ : Measure X) (ν : Measure Y)
    (T : X → Y) (hT : Measurable T) (c : ℝ) :
    μ.map T = ν ↔ ∀ d : Y → ℝ, Measurable d →
      _root_.GD.N0076.N0312.d022661 μ c (d ∘ T) = _root_.GD.N0076.N0312.d022661 ν c d := by
  constructor
  · intro h d hd
    rw [← _root_.GD.N0076.N0312.d022662 μ T hT c d hd, h]
  · intro h
    apply Measure.ext
    intro s hs
    let d : Y → ℝ := fun y => c + s.indicator (fun _ => (1 : ℝ)) y
    have hd : Measurable d := measurable_const.add (measurable_const.indicator hs)
    have hh := h d hd
    rw [← _root_.GD.N0076.N0312.d022662 μ T hT c d hd] at hh
    simpa only [d, _root_.GD.N0076.N0312.d022663 _ c s hs] using hh

theorem d022665 (μ ν : Measure Y) (c : ℝ) :
    μ = ν ↔ ∀ d : Y → ℝ, Measurable d → _root_.GD.N0076.N0312.d022661 μ c d = _root_.GD.N0076.N0312.d022661 ν c d := by
  simpa using _root_.GD.N0076.N0312.d022664 μ ν id measurable_id c


theorem d022666 (μ : Measure X) (ν : Measure Y)
    (κ : Kernel X Y) (c : ℝ) :
    κ ∘ₘ μ = ν ↔ ∀ d : Y → ℝ, Measurable d →
      (∫⁻ x, _root_.GD.N0076.N0312.d022661 (κ x) c d ∂μ) = _root_.GD.N0076.N0312.d022661 ν c d := by
  have h (d : Y → ℝ) (hd : Measurable d) :
      _root_.GD.N0076.N0312.d022661 (κ ∘ₘ μ) c d = ∫⁻ x, _root_.GD.N0076.N0312.d022661 (κ x) c d ∂μ :=
    Measure.lintegral_bind κ.aemeasurable (by fun_prop)
  constructor
  · intro hκ d hd
    rw [← h d hd, hκ]
  · intro hκ
    apply (_root_.GD.N0076.N0312.d022665 _ _ c).2
    intro d hd
    rw [h d hd, hκ d hd]

omit [MeasurableSpace X] in

theorem d022667 (T : X → Y) (d : X → ℝ) :
    Measurable[(inferInstance : MeasurableSpace Y).comap T] d ↔
      ∃ e : Y → ℝ, Measurable e ∧ d = e ∘ T := by
  constructor
  · exact Measurable.exists_eq_measurable_comp
  · rintro ⟨e, he, rfl⟩
    exact he.comp (measurable_iff_comap_le.mpr le_rfl)

omit [MeasurableSpace X] [MeasurableSpace Y] in

theorem d022668 (T : X → Y) (d : X → ℝ) (x x' : X)
    (hT : T x = T x') (hd : d x ≠ d x') :
    ¬ ∃ e : Y → ℝ, d = e ∘ T := by
  rintro ⟨e, rfl⟩
  exact hd (congrArg e hT)

omit [MeasurableSpace X] [MeasurableSpace Y] in


theorem d022669 (T : X → Y) (bX : X → ℝ) (bY : Y → ℝ) :
    bY ∘ T = bX ↔ ∀ x, bY (T x) = bX x :=
  funext_iff

theorem d022670 (μ : Measure X) (ν : Measure Y) (ξ : Measure Z)
    (T : X → Y) (U : Y → Z) (hT : Measurable T) (hU : Measurable U)
    (hμ : μ.map T = ν) (hν : ν.map U = ξ) :
    μ.map (U ∘ T) = ξ := by
  rw [← Measure.map_map hU hT, hμ, hν]

section Pi

variable {I J : Type*} [Fintype I] [Fintype J]
  {A : I → Type*} [∀ i, MeasurableSpace (A i)]


theorem d022671 (μ : ∀ i, Measure (A i))
    [∀ i, IsProbabilityMeasure (μ i)] (e : J → I) (he : Function.Injective e) :
    MeasurePreserving (fun x : ∀ i, A i => fun j => x (e j))
      (Measure.pi μ) (Measure.pi (fun j => μ (e j))) := by
  have hI : iIndepFun (fun i (x : ∀ i, A i) => x i) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hJ := hI.precomp he
  refine ⟨by fun_prop, ?_⟩
  have h := hJ.map_fun_eq_pi_map
    (fun j => (measurable_pi_apply (e j)).aemeasurable)
  simpa only [(measurePreserving_eval μ _).map_eq] using h

end Pi

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859



def d022672 {k l : ℕ} {n : Fin k → ℕ} {m : Fin l → ℕ}
    (g : Fin l → Fin k) (j : ∀ i, Fin (m i) → Fin (n (g i))) :
    _root_.GD.N0232.N0719.d009173 k n → _root_.GD.N0232.N0719.d009173 l m :=
  fun x i a => x (g i) (j i a)

def d022673 {k l : ℕ} (g : Fin l → Fin k) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0859.d010809 l :=
  ⟨θ.location, θ.scale ∘ g, fun i => θ.scale_pos (g i)⟩

@[fun_prop] theorem d022674 {k l : ℕ}
    {n : Fin k → ℕ} {m : Fin l → ℕ}
    (g : Fin l → Fin k) (j : ∀ i, Fin (m i) → Fin (n (g i))) :
    Measurable (_root_.GD.N0076.N0312.d022672 g j) := by
  unfold _root_.GD.N0076.N0312.d022672
  fun_prop

theorem d022675 {k l : ℕ} (g : Fin l → Fin k) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (_root_.GD.N0076.N0312.d022673 g θ).location = θ.location := rfl


theorem d022676 {k l : ℕ} {n : Fin k → ℕ} {m : Fin l → ℕ}
    (g : Fin l → Fin k) (hg : Function.Injective g)
    (j : ∀ i, Fin (m i) → Fin (n (g i))) (hj : ∀ i, Function.Injective (j i))
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (_root_.GD.N0232.N0719.N0859.d010812 k n θ).map (_root_.GD.N0076.N0312.d022672 g j) = _root_.GD.N0232.N0719.N0859.d010812 l m (_root_.GD.N0076.N0312.d022673 g θ) := by
  rw [_root_.GD.N0076.N0310.d014204, _root_.GD.N0076.N0310.d014204]
  unfold _root_.GD.N0076.N0310.d014203
  let μ : ∀ i : Fin k, Measure (Fin (n i) → ℝ) := fun i =>
    Measure.pi (fun _ => gaussianReal θ.location (_root_.GD.N0232.N0719.N0932.d009193 (θ.scale i)))
  have hgM := _root_.GD.N0076.N0312.d022671 μ g hg
  have hjM := measurePreserving_pi
    (fun i : Fin l => μ (g i))
    (fun i : Fin l => Measure.pi (fun _ : Fin (m i) =>
      gaussianReal θ.location (_root_.GD.N0232.N0719.N0932.d009193 (θ.scale (g i)))))
    (fun i => _root_.GD.N0076.N0312.d022671
      (fun _ : Fin (n (g i)) => gaussianReal θ.location
        (_root_.GD.N0232.N0719.N0932.d009193 (θ.scale (g i)))) (j i) (hj i))
  exact (hjM.comp hgM).map_eq

theorem d022677 {k l : ℕ}
    {n : Fin k → ℕ} {m : Fin l → ℕ}
    (g : Fin l → Fin k) (hg : Function.Injective g)
    (j : ∀ i, Fin (m i) → Fin (n (g i))) (hj : ∀ i, Function.Injective (j i))
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.d009173 l m → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0719.N0859.d010840 k n θ (d ∘ _root_.GD.N0076.N0312.d022672 g j) =
      _root_.GD.N0232.N0719.N0859.d010840 l m (_root_.GD.N0076.N0312.d022673 g θ) d := by
  change _root_.GD.N0076.N0312.d022661 (_root_.GD.N0232.N0719.N0859.d010812 k n θ) θ.location (d ∘ _root_.GD.N0076.N0312.d022672 g j) =
    _root_.GD.N0076.N0312.d022661 (_root_.GD.N0232.N0719.N0859.d010812 l m (_root_.GD.N0076.N0312.d022673 g θ)) θ.location d
  rw [← _root_.GD.N0076.N0312.d022662 _ _ (_root_.GD.N0076.N0312.d022674 g j) _ _ hd,
    _root_.GD.N0076.N0312.d022676 g hg j hj]




theorem d022678 {k l : ℕ} (g : Fin l → Fin k)
    (hg : Function.Injective g) : Function.Surjective (_root_.GD.N0076.N0312.d022673 g) := by
  classical
  intro θ
  let s : Fin k → ℝ := Function.extend g θ.scale (fun _ => 1)
  have hs : ∀ i, 0 < s i := by
    intro i
    by_cases hi : ∃ a, g a = i
    · obtain ⟨a, rfl⟩ := hi
      simpa only [s, hg.extend_apply] using θ.scale_pos a
    · simp only [s, Function.extend_apply' _ _ i hi, zero_lt_one]
  refine ⟨⟨θ.location, s, hs⟩, ?_⟩
  have heq : s ∘ g = θ.scale := Function.extend_comp hg θ.scale (fun _ => 1)
  cases θ
  dsimp [_root_.GD.N0076.N0312.d022673] at *
  congr 1




theorem d022679 {k l : ℕ} {n : Fin k → ℕ} {m : Fin l → ℕ}
    (g : Fin l → Fin k) (hg : Function.Injective g)
    (j : ∀ i, Fin (m i) → Fin (n (g i))) (hj : ∀ i, Function.Injective (j i))
    (d e : _root_.GD.N0232.N0719.d009173 l m → ℝ)
    (hd : Measurable d) (he : Measurable e) :
    (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k n θ (d ∘ _root_.GD.N0076.N0312.d022672 g j) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k n θ (e ∘ _root_.GD.N0076.N0312.d022672 g j)) ↔
    (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 l m θ d ≤ _root_.GD.N0232.N0719.N0859.d010840 l m θ e) := by
  simp_rw [_root_.GD.N0076.N0312.d022677 g hg j hj _ d hd,
    _root_.GD.N0076.N0312.d022677 g hg j hj _ e he]
  constructor
  · intro h θ
    obtain ⟨η, rfl⟩ := _root_.GD.N0076.N0312.d022678 g hg θ
    exact h η
  · intro h θ
    exact h (_root_.GD.N0076.N0312.d022673 g θ)

theorem d022680 {k l : ℕ} {n : Fin k → ℕ} {m : Fin l → ℕ}
    (g : Fin l → Fin k) (hg : Function.Injective g)
    (j : ∀ i, Fin (m i) → Fin (n (g i))) (hj : ∀ i, Function.Injective (j i))
    (d e : _root_.GD.N0232.N0719.d009173 l m → ℝ)
    (hd : Measurable d) (he : Measurable e) :
    (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k n θ (d ∘ _root_.GD.N0076.N0312.d022672 g j) <
      _root_.GD.N0232.N0719.N0859.d010840 k n θ (e ∘ _root_.GD.N0076.N0312.d022672 g j)) ↔
    (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 l m θ d < _root_.GD.N0232.N0719.N0859.d010840 l m θ e) := by
  simp_rw [_root_.GD.N0076.N0312.d022677 g hg j hj _ d hd,
    _root_.GD.N0076.N0312.d022677 g hg j hj _ e he]
  constructor
  · intro h θ
    obtain ⟨η, rfl⟩ := _root_.GD.N0076.N0312.d022678 g hg θ
    exact h η
  · intro h θ
    exact h (_root_.GD.N0076.N0312.d022673 g θ)

theorem d022681 {k l : ℕ} {n : Fin k → ℕ} {m : Fin l → ℕ}
    (g : Fin l → Fin k) (hg : Function.Injective g)
    (j : ∀ i, Fin (m i) → Fin (n (g i))) (hj : ∀ i, Function.Injective (j i))
    (d e : _root_.GD.N0232.N0719.d009173 l m → ℝ)
    (hd : Measurable d) (he : Measurable e) :
    (∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k n θ (d ∘ _root_.GD.N0076.N0312.d022672 g j) <
      _root_.GD.N0232.N0719.N0859.d010840 k n θ (e ∘ _root_.GD.N0076.N0312.d022672 g j)) ↔
    (∃ θ, _root_.GD.N0232.N0719.N0859.d010840 l m θ d < _root_.GD.N0232.N0719.N0859.d010840 l m θ e) := by
  simp_rw [_root_.GD.N0076.N0312.d022677 g hg j hj _ d hd,
    _root_.GD.N0076.N0312.d022677 g hg j hj _ e he]
  constructor
  · rintro ⟨θ, hθ⟩
    exact ⟨_root_.GD.N0076.N0312.d022673 g θ, hθ⟩
  · rintro ⟨θ, hθ⟩
    obtain ⟨η, rfl⟩ := _root_.GD.N0076.N0312.d022678 g hg θ
    exact ⟨η, hθ⟩




theorem d022682 {k l : ℕ}
    {n : Fin k → ℕ} {m : Fin l → ℕ}
    (g : Fin l → Fin k) (j : ∀ i, Fin (m i) → Fin (n (g i)))
    (q : Σ i : Fin k, Fin (n i))
    (hq : ∀ i a, (⟨g i, j i a⟩ : Σ i : Fin k, Fin (n i)) ≠ q) :
    ¬ ∃ d : _root_.GD.N0232.N0719.d009173 l m → ℝ,
      (fun x : _root_.GD.N0232.N0719.d009173 k n => x q.1 q.2) =
        d ∘ _root_.GD.N0076.N0312.d022672 g j := by
  classical
  let x : _root_.GD.N0232.N0719.d009173 k n := fun _ _ => 0
  let x' : _root_.GD.N0232.N0719.d009173 k n :=
    fun i a => if (⟨i, a⟩ : Σ i : Fin k, Fin (n i)) = q then 1 else 0
  apply _root_.GD.N0076.N0312.d022668 (_root_.GD.N0076.N0312.d022672 g j) _ x x'
  · funext i a
    simp only [_root_.GD.N0076.N0312.d022672, x, x', if_neg (hq i a)]
  · simp only [x, x', Sigma.eta, ↓reduceIte, ne_eq, zero_ne_one, not_false_eq_true]

end
end GD.N0076.N0312

#print axioms _root_.GD.N0076.N0312.d022664
#print axioms _root_.GD.N0076.N0312.d022667
#print axioms _root_.GD.N0076.N0312.d022668
#print axioms _root_.GD.N0076.N0312.d022669
#print axioms _root_.GD.N0076.N0312.d022670
#print axioms _root_.GD.N0076.N0312.d022671
#print axioms _root_.GD.N0076.N0312.d022676
#print axioms _root_.GD.N0076.N0312.d022677

#print axioms _root_.GD.N0076.N0312.d022665
#print axioms _root_.GD.N0076.N0312.d022666
#print axioms _root_.GD.N0076.N0312.d022678
#print axioms _root_.GD.N0076.N0312.d022679
#print axioms _root_.GD.N0076.N0312.d022680
#print axioms _root_.GD.N0076.N0312.d022681
#print axioms _root_.GD.N0076.N0312.d022682
