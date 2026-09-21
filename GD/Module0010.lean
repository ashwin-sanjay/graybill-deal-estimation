import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Real
import GD.Module0009














open Filter MeasureTheory Set

namespace GD
namespace N0230
namespace N0562

variable {Ω X E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]











theorem d000067
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (f : ℕ → Ω → E) (g : Ω → E)
    (happrox : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
      ∃ a : ℕ → Ω → E, ∃ b : Ω → E,
        TendstoInMeasure mu a atTop b ∧
        (∀ᶠ n in atTop,
          mu.real {x | ε ≤ dist (f n x) (a n x)} < δ) ∧
        mu.real {x | ε ≤ dist (b x) (g x)} < δ) :
    TendstoInMeasure mu f atTop g := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hε3 : 0 < ε / 3 := by positivity
  have hδ3 : 0 < δ / 3 := by positivity
  obtain ⟨a, b, hab, hfa, hbg⟩ := happrox (ε / 3) hε3 (δ / 3) hδ3
  have hab' :=
    (tendstoInMeasure_iff_measureReal_dist.mp hab) (ε / 3) hε3
  rw [Metric.tendsto_atTop] at hab'
  obtain ⟨N₁, hN₁⟩ := hab' (δ / 3) hδ3
  obtain ⟨N₂, hN₂⟩ := (eventually_atTop.1 hfa)
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hcenterDist := hN₁ n hn₁
  have hcenterNonneg :
      0 ≤ mu.real {x | ε / 3 ≤ dist (a n x) (b x)} :=
    measureReal_nonneg
  have hcenter :
      mu.real {x | ε / 3 ≤ dist (a n x) (b x)} < δ / 3 := by
    simpa [Real.dist_eq, abs_of_nonneg hcenterNonneg] using hcenterDist
  have hleft := hN₂ n hn₂
  let A : Set Ω := {x | ε / 3 ≤ dist (f n x) (a n x)}
  let B : Set Ω := {x | ε / 3 ≤ dist (a n x) (b x)}
  let C : Set Ω := {x | ε / 3 ≤ dist (b x) (g x)}
  have hsubset : {x | ε ≤ dist (f n x) (g x)} ⊆ A ∪ (B ∪ C) := by
    intro x hx
    by_contra hnot
    have hxA : x ∉ A := fun hxA ↦ hnot (Or.inl hxA)
    have hxB : x ∉ B := fun hxB ↦ hnot (Or.inr (Or.inl hxB))
    have hxC : x ∉ C := fun hxC ↦ hnot (Or.inr (Or.inr hxC))
    have hA_lt : dist (f n x) (a n x) < ε / 3 := by
      simpa [A] using hxA
    have hB_lt : dist (a n x) (b x) < ε / 3 := by
      simpa [B] using hxB
    have hC_lt : dist (b x) (g x) < ε / 3 := by
      simpa [C] using hxC
    have htriangle :
        dist (f n x) (g x) ≤
          dist (f n x) (a n x) +
            (dist (a n x) (b x) + dist (b x) (g x)) := by
      calc
        dist (f n x) (g x) ≤
            dist (f n x) (a n x) + dist (a n x) (g x) :=
          dist_triangle _ _ _
        _ ≤ dist (f n x) (a n x) +
            (dist (a n x) (b x) + dist (b x) (g x)) := by
          gcongr
          exact dist_triangle _ _ _
    have : dist (f n x) (g x) < ε := by
      calc
        dist (f n x) (g x) ≤
            dist (f n x) (a n x) +
              (dist (a n x) (b x) + dist (b x) (g x)) := htriangle
        _ < ε := by linarith
    exact (not_lt_of_ge hx) this
  have hmeasure :
      mu.real {x | ε ≤ dist (f n x) (g x)} ≤
        mu.real A + (mu.real B + mu.real C) := by
    exact (measureReal_mono hsubset).trans
      ((measureReal_union_le A (B ∪ C)).trans
        (by
          gcongr
          exact measureReal_union_le B C))
  have hA : mu.real A < δ / 3 := by simpa [A] using hleft
  have hB : mu.real B < δ / 3 := by simpa [B] using hcenter
  have hC : mu.real C < δ / 3 := by simpa [C] using hbg
  have hsmall :
      mu.real {x | ε ≤ dist (f n x) (g x)} < δ := by
    calc
      mu.real {x | ε ≤ dist (f n x) (g x)} ≤
          mu.real A + (mu.real B + mu.real C) := hmeasure
      _ < δ := by linarith
  have hnonneg : 0 ≤ mu.real {x | ε ≤ dist (f n x) (g x)} :=
    measureReal_nonneg
  simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hsmall













theorem d000068
    [TopologicalSpace X]
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (transform : ℕ → Ω → X) (limitTransform : Ω → X)
    (d : X → E)
    (hcontinuousPullback : ∀ h : X → E, Continuous h →
      TendstoInMeasure mu
        (fun n x ↦ h (transform n x)) atTop
        (fun x ↦ h (limitTransform x)))
    (huniformApproximation : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
      ∃ h : X → E, Continuous h ∧
        (∀ᶠ n in atTop,
          mu.real {x |
            ε ≤ dist (d (transform n x)) (h (transform n x))} < δ) ∧
        mu.real {x |
          ε ≤ dist (h (limitTransform x)) (d (limitTransform x))} < δ) :
    TendstoInMeasure mu
      (fun n x ↦ d (transform n x)) atTop
      (fun x ↦ d (limitTransform x)) := by
  apply _root_.GD.N0230.N0562.d000067 mu
  intro ε hε δ hδ
  obtain ⟨h, hh, hmoving, hlimit⟩ :=
    huniformApproximation ε hε δ hδ
  exact ⟨
    (fun n x ↦ h (transform n x)),
    (fun x ↦ h (limitTransform x)),
    hcontinuousPullback h hh,
    hmoving,
    hlimit⟩










theorem d000069
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace E] [BorelSpace E] [OpensMeasurableSpace E]
    [OpensMeasurableSpace (E × E)]
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (transform : ℕ → Ω → X) (limitTransform : Ω → X)
    (d : X → E) (hd : Measurable d)
    (hcontinuousPullback : ∀ h : X → E, Continuous h →
      TendstoInMeasure mu
        (fun n x ↦ h (transform n x)) atTop
        (fun x ↦ h (limitTransform x)))
    (hsetwiseUpper : ∀ s : Set X, MeasurableSet s →
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ n in atTop,
          mu.real (transform n ⁻¹' s) <
            mu.real (limitTransform ⁻¹' s) + δ)
    (hlimitApproximation : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
      ∃ h : X → E, Continuous h ∧
        mu.real {x |
          ε ≤ dist (d (limitTransform x)) (h (limitTransform x))} < δ) :
    TendstoInMeasure mu
      (fun n x ↦ d (transform n x)) atTop
      (fun x ↦ d (limitTransform x)) := by
  apply
    _root_.GD.N0230.N0562.d000068
      mu transform limitTransform d hcontinuousPullback
  intro ε hε δ hδ
  have hδtwo : 0 < δ / 2 := by positivity
  obtain ⟨h, hh, hlimit⟩ :=
    hlimitApproximation ε hε (δ / 2) hδtwo
  let s : Set X := {y | ε ≤ dist (d y) (h y)}
  have hs : MeasurableSet s := by
    exact measurableSet_le measurable_const
      (continuous_dist.measurable.comp (hd.prodMk hh.measurable))
  have hmoving := hsetwiseUpper s hs (δ / 2) hδtwo
  refine ⟨h, hh, ?_, ?_⟩
  · filter_upwards [hmoving] with n hn
    have hpreimage :
        transform n ⁻¹' s =
          {x | ε ≤ dist (d (transform n x)) (h (transform n x))} := by
      ext x
      rfl
    rw [hpreimage] at hn
    have hlimitPreimage :
        limitTransform ⁻¹' s =
          {x | ε ≤ dist (d (limitTransform x)) (h (limitTransform x))} := by
      ext x
      rfl
    rw [hlimitPreimage] at hn
    linarith
  · have hlimit' :
        mu.real {x |
          ε ≤ dist (h (limitTransform x)) (d (limitTransform x))} < δ / 2 := by
      simpa [dist_comm] using hlimit
    exact hlimit'.trans (half_lt_self hδ)









theorem d000070
    {V : Type*}
    [TopologicalSpace X] [NormalSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [OpensMeasurableSpace (V × V)]
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (nu : Measure X) [IsFiniteMeasure nu] [nu.WeaklyRegular]
    (transform : ℕ → Ω → X) (limitTransform : Ω → X)
    (d : X → V) (hdMeasurable : Measurable d)
    {p : ENNReal} (hpTop : p ≠ ⊤) (hpZero : p ≠ 0)
    (hdLp : MemLp d p nu)
    (hcontinuousPullback : ∀ h : X → V, Continuous h →
      TendstoInMeasure mu
        (fun n x ↦ h (transform n x)) atTop
        (fun x ↦ h (limitTransform x)))
    (hlimitLaw : ∀ s : Set X, MeasurableSet s →
      nu.real s = mu.real (limitTransform ⁻¹' s))
    (hsetwiseUpper : ∀ s : Set X, MeasurableSet s →
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ n in atTop,
          mu.real (transform n ⁻¹' s) < nu.real s + δ) :
    TendstoInMeasure mu
      (fun n x ↦ d (transform n x)) atTop
      (fun x ↦ d (limitTransform x)) := by
  apply _root_.GD.N0230.N0562.d000069
    mu transform limitTransform d hdMeasurable hcontinuousPullback
  · intro s hs δ hδ
    filter_upwards [hsetwiseUpper s hs δ hδ] with n hn
    simpa [← hlimitLaw s hs] using hn
  · intro ε hε δ hδ
    obtain ⟨h, hh, hsmall⟩ :=
      _root_.GD.N0230.N0588.d000066
          nu hpTop hpZero d hdLp ε δ hε hδ
    refine ⟨h, hh, ?_⟩
    let s : Set X := {y | ε ≤ dist (d y) (h y)}
    have hs : MeasurableSet s := by
      exact measurableSet_le measurable_const
        (continuous_dist.measurable.comp (hdMeasurable.prodMk hh.measurable))
    have hpreimage :
        limitTransform ⁻¹' s =
          {x | ε ≤ dist (d (limitTransform x)) (h (limitTransform x))} := by
      ext x
      rfl
    rw [← hpreimage, ← hlimitLaw s hs]
    exact hsmall

end N0562
end N0230
end GD

#print axioms _root_.GD.N0230.N0562.d000067
#print axioms _root_.GD.N0230.N0562.d000068
#print axioms _root_.GD.N0230.N0562.d000069
#print axioms _root_.GD.N0230.N0562.d000070
