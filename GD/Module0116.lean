import GD.Module0115
import GD.Module0053

































open MeasureTheory Filter
open scoped RealInnerProductSpace BigOperators

namespace GD
namespace N0230
namespace N0627

noncomputable section

open _root_.GD.N0230.N0669
open _root_.GD.N0230.N0574
open _root_.GD.N0230.N0568
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0623
open _root_.GD.N0230.N0689

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*} [MeasurableSpace Θ]
variable (ψ : Θ → H) (m h₀ : H)



theorem d001441
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ} {F : ℝ}
    (hrep : Tendsto (fun n ↦ -2 * (a n *
      ∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ))
      atTop (nhds F)) :
    Tendsto (fun n ↦ a n *
      ∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ)
      atTop (nhds (-(F / 2))) := by
  have h := hrep.const_mul (-(1 / 2) : ℝ)
  have heq : (fun n ↦ (-(1 / 2) : ℝ) * (-2 * (a n *
      ∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ))) =
      fun n ↦ a n * ∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ := by
    funext n
    ring
  have h2 : (-(1 / 2) : ℝ) * F = -(F / 2) := by ring
  rw [heq, h2] at h
  exact h




theorem d001442
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ} {F : ℝ}
    (hF : F < 0)
    (hrep : Tendsto (fun n ↦ -2 * (a n *
      ∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ))
      atTop (nhds F)) :
    0 < -(F / 2) ∧
      ∀ᶠ n in atTop, -(F / 4) ≤ a n *
        ∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ := by
  have hmass := _root_.GD.N0230.N0627.d001441 ψ m h₀ hrep
  refine ⟨by linarith, ?_⟩
  have hev := hmass.eventually_const_lt
    (by linarith : -(F / 4) < -(F / 2))
  filter_upwards [hev] with n hn
  exact hn.le





theorem d001443 [CompleteSpace H]
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ}
    {c F : ℝ} {w : H}
    (hu0 : h₀ ≠ 0) (hc : 0 < c)
    (hfloor : ∀ θ, c ≤ ⟪h₀, ψ θ - m⟫)
    (hint : ∀ n, IntegrableOn (fun θ ↦ ψ θ - m) (K n) μ)
    (hF : F < 0)
    (hrep : Tendsto (fun n ↦ -2 * (a n *
      ∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ))
      atTop (nhds F))
    (hvec : Tendsto (fun n ↦ a n • ∫ θ in K n, (ψ θ - m) ∂μ)
      atTop (nhds w)) :
    ⟪h₀, w⟫ = -(F / 2) ∧
      ∀ η : ℝ, 0 < η → η < 4 * (-(F / 2)) * c / ‖h₀‖ ^ 2 →
        Convex ℝ (_root_.GD.N0230.N0574.d001411 ψ m w η) ∧
          (_root_.GD.N0230.N0574.d001411 ψ m w η).Nonempty ∧
          ∃ p ∈ _root_.GD.N0230.N0574.d001411 ψ m w η,
            ∀ θ, 0 < ‖m - ψ θ‖ ^ 2 - ‖p - ψ θ‖ ^ 2 := by
  have hpairseq : (fun n ↦
      ⟪h₀, a n • ∫ θ in K n, (ψ θ - m) ∂μ⟫) =
      fun n ↦ a n * ∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ := by
    funext n
    rw [real_inner_smul_right,
      ← _root_.GD.N0230.N0568.d001436 ψ m h₀ (hint n)]
  have hpair : Tendsto (fun n ↦
      ⟪h₀, a n • ∫ θ in K n, (ψ θ - m) ∂μ⟫)
      atTop (nhds ⟪h₀, w⟫) :=
    Tendsto.inner tendsto_const_nhds hvec
  rw [hpairseq] at hpair
  have hmass := _root_.GD.N0230.N0627.d001441 ψ m h₀ hrep
  have hw : ⟪h₀, w⟫ = -(F / 2) := tendsto_nhds_unique hpair hmass
  have hγ : (0 : ℝ) < -(F / 2) := by linarith
  exact ⟨hw, fun η hη hb ↦ _root_.GD.N0230.N0574.d001414 ψ m w hu0
    hfloor hc hw.ge hγ hη hb⟩









theorem d001444 [CompleteSpace H]
    {Theta X V E : Type*}
    [MeasurableSpace Theta] [MeasurableSpace X]
    [Fintype V] [Fintype E] [DecidableEq V]
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center boundaryFlux : X → ℝ)
    (src dst : E → V) (flux : E → ℝ)
    (affineEndFlux : ℝ)
    (hlikelihood : ∀ theta x, 0 ≤ likelihood theta x)
    (hdeficit : Integrable
      (_root_.GD.N0230.N0589.d000096 likelihood target action center).uncurry
      (prior.prod data))
    (htax : Integrable
      (_root_.GD.N0230.N0589.d000089 prior likelihood action center) data)
    (hboundary : Integrable boundaryFlux data)
    (hmarginal : ∀ᵐ x ∂data,
      0 < _root_.GD.N0230.N0589.d000088 prior likelihood x)
    (hbalance : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000099 prior likelihood target action center x =
        _root_.GD.N0230.N0589.d000089 prior likelihood action center x +
          boundaryFlux x)
    (hnonpos : ∀ theta,
      _root_.GD.N0230.N0589.d000098 data likelihood target action center
        theta ≤ 0)
    (hboundarySplit :
      ∫ x, boundaryFlux x ∂data =
        ((∑ v, _root_.GD.N0230.N0623.d000202 dst flux v) -
          (∑ v, _root_.GD.N0230.N0623.d000203 src flux v)) + affineEndFlux)
    (hdistinct : ¬ action =ᵐ[data] center)
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ}
    {c : ℝ} {w : H}
    (hu0 : h₀ ≠ 0) (hc : 0 < c)
    (hfloor : ∀ θ, c ≤ ⟪h₀, ψ θ - m⟫)
    (hint : ∀ n, IntegrableOn (fun θ ↦ ψ θ - m) (K n) μ)
    (hrep : Tendsto (fun n ↦ -2 * (a n *
      ∫ θ in K n, _root_.GD.N0230.N0568.d001434 ψ m h₀ θ ∂μ))
      atTop (nhds affineEndFlux))
    (hvec : Tendsto (fun n ↦ a n • ∫ θ in K n, (ψ θ - m) ∂μ)
      atTop (nhds w)) :
    ⟪h₀, w⟫ = -(affineEndFlux / 2) ∧
      ∀ η : ℝ, 0 < η →
        η < 4 * (-(affineEndFlux / 2)) * c / ‖h₀‖ ^ 2 →
        Convex ℝ (_root_.GD.N0230.N0574.d001411 ψ m w η) ∧
          (_root_.GD.N0230.N0574.d001411 ψ m w η).Nonempty ∧
          ∃ p ∈ _root_.GD.N0230.N0574.d001411 ψ m w η,
            ∀ θ, 0 < ‖m - ψ θ‖ ^ 2 - ‖p - ψ θ‖ ^ 2 := by
  have hF := _root_.GD.N0230.N0689.d000665
    prior data likelihood target action center boundaryFlux
    src dst flux affineEndFlux hlikelihood hdeficit htax hboundary
    hmarginal hbalance hnonpos hboundarySplit hdistinct
  exact _root_.GD.N0230.N0627.d001443 ψ m h₀ hu0 hc hfloor
    hint hF hrep hvec

end

end N0627
end N0230
end GD

#print axioms _root_.GD.N0230.N0627.d001441
#print axioms _root_.GD.N0230.N0627.d001442
#print axioms _root_.GD.N0230.N0627.d001443
#print axioms _root_.GD.N0230.N0627.d001444
