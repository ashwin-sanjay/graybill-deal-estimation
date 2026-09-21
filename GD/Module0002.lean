import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

















open Set Filter
open scoped Topology ContDiff

namespace GD.N0227.N0544

noncomputable section

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


inductive d000002 (I : Type*) where
  | generator : I → d000002 I
  | bracket : d000002 I → d000002 I → d000002 I


def d000002.d000003 (V : I → E → E) : _root_.GD.N0227.N0544.d000002 I → E → E
  | .generator i => V i
  | .bracket u v => VectorField.lieBracket ℝ (u.d000003 V) (v.d000003 V)



def d000004 (V : I → E → E) (x : E) : Submodule ℝ E :=
  Submodule.span ℝ (range (fun w : _root_.GD.N0227.N0544.d000002 I => w.d000003 V x))

theorem d000005 {s : Set E} (hs : IsOpen s)
    {V W : E → E} (hV : ContDiffOn ℝ ∞ V s) (hW : ContDiffOn ℝ ∞ W s) :
    ContDiffOn ℝ ∞ (VectorField.lieBracket ℝ V W) s := by
  intro x hx
  exact ((hV.contDiffAt (hs.mem_nhds hx)).lieBracket_vectorField
    (hW.contDiffAt (hs.mem_nhds hx)) (m := ∞) (by simp)).contDiffWithinAt

theorem d000002.d000006 {s : Set E} (hs : IsOpen s)
    (V : I → E → E) (hV : ∀ i, ContDiffOn ℝ ∞ (V i) s)
    (w : _root_.GD.N0227.N0544.d000002 I) : ContDiffOn ℝ ∞ (w.d000003 V) s := by
  induction w with
  | generator i => exact hV i
  | bracket u v hu hv => exact _root_.GD.N0227.N0544.d000005 hs hu hv



theorem d000007 {s : Set E} (hs : IsOpen s)
    {H : E → ℝ} {V W : E → E}
    (hH : ContDiffOn ℝ 2 H s)
    (hV : ContDiffOn ℝ ∞ V s) (hW : ContDiffOn ℝ ∞ W s)
    (hVH : ∀ x ∈ s, fderiv ℝ H x (V x) = 0)
    (hWH : ∀ x ∈ s, fderiv ℝ H x (W x) = 0) :
    ∀ x ∈ s, fderiv ℝ H x (VectorField.lieBracket ℝ V W x) = 0 := by
  intro x hx
  have hVx := (hV.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have hWx := (hW.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  rw [VectorField.fderiv_apply_lieBracket
    (hH.contDiffAt (hs.mem_nhds hx)) (by simp) hWx hVx]
  have hv : (fun y => fderiv ℝ H y (V y)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact hVH y hy
  have hw : (fun y => fderiv ℝ H y (W y)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact hWH y hy
  rw [hv.fderiv_eq, hw.fderiv_eq]
  simp



theorem d000002.d000008 {s : Set E} (hs : IsOpen s)
    (V : I → E → E) (hV : ∀ i, ContDiffOn ℝ ∞ (V i) s)
    {H : E → ℝ} (hH : ContDiffOn ℝ 2 H s)
    (hzero : ∀ i, ∀ x ∈ s, fderiv ℝ H x (V i x) = 0)
    (w : _root_.GD.N0227.N0544.d000002 I) : ∀ x ∈ s, fderiv ℝ H x (w.d000003 V x) = 0 := by
  induction w with
  | generator i => exact hzero i
  | bracket u v hu hv =>
      exact _root_.GD.N0227.N0544.d000007 hs hH
        (u.d000006 hs V hV) (v.d000006 hs V hV) hu hv


theorem d000009 {s : Set E} (hs : IsOpen s)
    (V : I → E → E) (hV : ∀ i, ContDiffOn ℝ ∞ (V i) s)
    {H : E → ℝ} (hH : ContDiffOn ℝ 2 H s)
    (hzero : ∀ i, ∀ y ∈ s, fderiv ℝ H y (V i y) = 0)
    {x : E} (hx : x ∈ s) :
    _root_.GD.N0227.N0544.d000004 V x ≤ LinearMap.ker (fderiv ℝ H x).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl⟩
  exact w.d000008 hs V hV hH hzero x hx


theorem d000010 {s : Set E} (hs : IsOpen s)
    (V : I → E → E) (hV : ∀ i, ContDiffOn ℝ ∞ (V i) s)
    {H : E → ℝ} (hH : ContDiffOn ℝ 2 H s)
    (hzero : ∀ i, ∀ y ∈ s, fderiv ℝ H y (V i y) = 0)
    {x v : E} (hx : x ∈ s) (hv : v ∈ _root_.GD.N0227.N0544.d000004 V x) :
    fderiv ℝ H x v = 0 :=
  _root_.GD.N0227.N0544.d000009 hs V hV hH hzero hx hv


theorem d000011 {s : Set E} (hs : IsOpen s)
    (V : I → E → E) (hV : ∀ i, ContDiffOn ℝ ∞ (V i) s)
    {H : E → ℝ} (hH : ContDiffOn ℝ 2 H s)
    (hzero : ∀ i, ∀ y ∈ s, fderiv ℝ H y (V i y) = 0)
    {x v : E} (hx : x ∈ s) (hv : v ∈ _root_.GD.N0227.N0544.d000004 V x)
    {κ : ℝ} (hκ : κ ≠ 0) (hHx : H x ≠ 0)
    (hcharacter : fderiv ℝ H x v = κ * H x) : False := by
  have hz := _root_.GD.N0227.N0544.d000010 hs V hV hH hzero hx hv
  exact (mul_ne_zero hκ hHx) (hcharacter.symm.trans hz)


theorem d000012 {M₀ M₁ : E → ℝ} {x v : E}
    (hM₀ : DifferentiableAt ℝ M₀ x) (hM₁ : DifferentiableAt ℝ M₁ x)
    (hne : M₀ x ≠ 0) {lam₀ lam₁ : ℝ}
    (h₀ : fderiv ℝ M₀ x v = lam₀ * M₀ x)
    (h₁ : fderiv ℝ M₁ x v = lam₁ * M₁ x) :
    fderiv ℝ (fun y => M₁ y / M₀ y) x v =
      (lam₁ - lam₀) * (M₁ x / M₀ x) := by
  have hratio : DifferentiableAt ℝ (fun y => M₁ y / M₀ y) x := by
    simpa only [div_eq_mul_inv, Pi.mul_apply, Function.comp_def] using
      hM₁.fun_mul ((hasDerivAt_inv hne).differentiableAt.comp x hM₀)
  have hprod : M₁ =ᶠ[𝓝 x] fun y => (M₁ y / M₀ y) * M₀ y := by
    filter_upwards [hM₀.continuousAt.eventually_ne hne] with y hy
    exact (div_mul_cancel₀ (M₁ y) hy).symm
  have hp := (hratio.hasFDerivAt.mul hM₀.hasFDerivAt).congr_of_eventuallyEq hprod
  have hpv := congrArg (fun L : E →L[ℝ] ℝ => L v) hp.fderiv
  simp only [add_apply, smul_apply,
    smul_eq_mul, h₀, h₁] at hpv
  apply mul_right_cancel₀ hne
  have hc := div_mul_cancel₀ (M₁ x) hne
  nlinarith [hpv, congrArg (fun t => lam₀ * t) hc, congrArg (fun t => lam₁ * t) hc]


theorem d000013 {M₀ M₁ : E → ℝ} {x v : E}
    (hM₀ : DifferentiableAt ℝ M₀ x) (hM₁ : DifferentiableAt ℝ M₁ x)
    (hne : M₀ x ≠ 0) {a : ℝ}
    (h₀ : fderiv ℝ M₀ x v = a * M₀ x)
    (h₁ : fderiv ℝ M₁ x v = a * M₁ x) :
    fderiv ℝ (fun y => M₁ y / M₀ y) x v = 0 := by
  simpa using _root_.GD.N0227.N0544.d000012 hM₀ hM₁ hne h₀ h₁





theorem d000014 {s : Set E} (hs : IsOpen s)
    (V : I → E → E) (hV : ∀ i, ContDiffOn ℝ ∞ (V i) s)
    (M₀ M₁ : E → ℝ)
    (hM₀ : ContDiffOn ℝ 2 M₀ s) (hM₁ : ContDiffOn ℝ 2 M₁ s)
    (hne : ∀ y ∈ s, M₀ y ≠ 0)
    (a : I → E → ℝ)
    (htransport₀ : ∀ i, ∀ y ∈ s, fderiv ℝ M₀ y (V i y) = a i y * M₀ y)
    (htransport₁ : ∀ i, ∀ y ∈ s, fderiv ℝ M₁ y (V i y) = a i y * M₁ y)
    {x v : E} (hx : x ∈ s) (hv : v ∈ _root_.GD.N0227.N0544.d000004 V x)
    (hM₁x : M₁ x ≠ 0) {lam₀ lam₁ : ℝ} (hlam : lam₀ ≠ lam₁)
    (hcharacter₀ : fderiv ℝ M₀ x v = lam₀ * M₀ x)
    (hcharacter₁ : fderiv ℝ M₁ x v = lam₁ * M₁ x) : False := by
  have hratio : ContDiffOn ℝ 2 (fun y => M₁ y / M₀ y) s := hM₁.fun_div hM₀ hne
  have hd₀ (y : E) (hy : y ∈ s) : DifferentiableAt ℝ M₀ y :=
    (hM₀.contDiffAt (hs.mem_nhds hy)).differentiableAt (by norm_num)
  have hd₁ (y : E) (hy : y ∈ s) : DifferentiableAt ℝ M₁ y :=
    (hM₁.contDiffAt (hs.mem_nhds hy)).differentiableAt (by norm_num)
  apply _root_.GD.N0227.N0544.d000011 hs V hV hratio
    (fun i y hy => _root_.GD.N0227.N0544.d000013 (hd₀ y hy) (hd₁ y hy) (hne y hy)
      (htransport₀ i y hy) (htransport₁ i y hy)) hx hv
      (sub_ne_zero.mpr hlam.symm) (div_ne_zero hM₁x (hne x hx))
  exact _root_.GD.N0227.N0544.d000012 (hd₀ x hx) (hd₁ x hx) (hne x hx)
    hcharacter₀ hcharacter₁



theorem d000015 {M : E → ℝ} {x v : E}
    (hM : DifferentiableAt ℝ M x) (γ : ℝ → E)
    (hγ : HasDerivAt γ v 0) (hγ₀ : γ 0 = x) (lam : ℝ)
    (hhom : ∀ᶠ t : ℝ in 𝓝 0, M (γ t) = Real.exp (lam * t) * M x) :
    fderiv ℝ M x v = lam * M x := by
  have hMx : HasFDerivAt M (fderiv ℝ M x) (γ 0) := by
    simpa [hγ₀] using hM.hasFDerivAt
  have hl := hMx.comp_hasDerivAt 0 hγ
  have hr := (((hasDerivAt_id (0 : ℝ)).const_mul lam).exp).mul_const (M x)
  have hsame := hl.congr_of_eventuallyEq (show
      (fun t => Real.exp (lam * t) * M x) =ᶠ[𝓝 0] (M ∘ γ) from Filter.EventuallyEq.symm hhom)
  simpa using hsame.unique hr


theorem d000016 {s : Set E} (hs : IsOpen s)
    (V : I → E → E) (hV : ∀ i, ContDiffOn ℝ ∞ (V i) s)
    (M₀ M₁ : E → ℝ)
    (hM₀ : ContDiffOn ℝ 2 M₀ s) (hM₁ : ContDiffOn ℝ 2 M₁ s)
    (hne : ∀ y ∈ s, M₀ y ≠ 0)
    (a : I → E → ℝ)
    (htransport₀ : ∀ i, ∀ y ∈ s, fderiv ℝ M₀ y (V i y) = a i y * M₀ y)
    (htransport₁ : ∀ i, ∀ y ∈ s, fderiv ℝ M₁ y (V i y) = a i y * M₁ y)
    {x v : E} (hx : x ∈ s) (hv : v ∈ _root_.GD.N0227.N0544.d000004 V x) (hM₁x : M₁ x ≠ 0)
    (γ : ℝ → E) (hγ : HasDerivAt γ v 0) (hγ₀ : γ 0 = x)
    {lam₀ lam₁ : ℝ} (hlam : lam₀ ≠ lam₁)
    (hhom₀ : ∀ᶠ t : ℝ in 𝓝 0, M₀ (γ t) = Real.exp (lam₀ * t) * M₀ x)
    (hhom₁ : ∀ᶠ t : ℝ in 𝓝 0, M₁ (γ t) = Real.exp (lam₁ * t) * M₁ x) : False := by
  apply _root_.GD.N0227.N0544.d000014 hs V hV M₀ M₁ hM₀ hM₁ hne a
    htransport₀ htransport₁ hx hv hM₁x hlam
  · exact _root_.GD.N0227.N0544.d000015
      ((hM₀.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)) γ hγ hγ₀ lam₀ hhom₀
  · exact _root_.GD.N0227.N0544.d000015
      ((hM₁.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)) γ hγ hγ₀ lam₁ hhom₁



def d000002.d000017 (V : I → E → E) (S : I → E → ℝ) : _root_.GD.N0227.N0544.d000002 I → E → ℝ
  | .generator i => S i
  | .bracket u v => fun x =>
      fderiv ℝ (v.d000017 V S) x (u.d000003 V x) -
        fderiv ℝ (u.d000017 V S) x (v.d000003 V x)



theorem d000002.d000018 {s : Set E} (hs : IsOpen s)
    (V : I → E → E) (hV : ∀ i, ContDiffOn ℝ ∞ (V i) s)
    {R : E → ℝ} (hR : ContDiffOn ℝ 2 R s)
    (S : I → E → ℝ)
    (hsource : ∀ i, ∀ x ∈ s, fderiv ℝ R x (V i x) = S i x)
    (w : _root_.GD.N0227.N0544.d000002 I) : ∀ x ∈ s,
      fderiv ℝ R x (w.d000003 V x) = w.d000017 V S x := by
  induction w with
  | generator i => exact hsource i
  | bracket u v hu hv =>
      intro x hx
      have hux := ((u.d000006 hs V hV).contDiffAt
        (hs.mem_nhds hx)).differentiableAt (by simp)
      have hvx := ((v.d000006 hs V hV).contDiffAt
        (hs.mem_nhds hx)).differentiableAt (by simp)
      change fderiv ℝ R x (VectorField.lieBracket ℝ (u.d000003 V) (v.d000003 V) x) = _
      rw [VectorField.fderiv_apply_lieBracket
        (hR.contDiffAt (hs.mem_nhds hx)) (by simp) hvx hux]
      have hue : (fun y => fderiv ℝ R y (u.d000003 V y)) =ᶠ[𝓝 x]
          u.d000017 V S := by
        filter_upwards [hs.mem_nhds hx] with y hy
        exact hu y hy
      have hve : (fun y => fderiv ℝ R y (v.d000003 V y)) =ᶠ[𝓝 x]
          v.d000017 V S := by
        filter_upwards [hs.mem_nhds hx] with y hy
        exact hv y hy
      rw [hue.fderiv_eq, hve.fderiv_eq]
      rfl



theorem d000019 {H ρ : E → ℝ} {x v : E}
    (hH : DifferentiableAt ℝ H x) (hρ : DifferentiableAt ℝ ρ x)
    (hne : H x ≠ 0) {a source : ℝ}
    (h₀ : fderiv ℝ H x v = a * H x)
    (h₁ : fderiv ℝ ρ x v = a * ρ x + source) :
    fderiv ℝ (fun y => ρ y / H y) x v = source / H x := by
  have hratio : DifferentiableAt ℝ (fun y => ρ y / H y) x := by
    simpa only [div_eq_mul_inv, Pi.mul_apply, Function.comp_def] using
      hρ.fun_mul ((hasDerivAt_inv hne).differentiableAt.comp x hH)
  have hprod : ρ =ᶠ[𝓝 x] fun y => (ρ y / H y) * H y := by
    filter_upwards [hH.continuousAt.eventually_ne hne] with y hy
    exact (div_mul_cancel₀ (ρ y) hy).symm
  have hp := (hratio.hasFDerivAt.mul hH.hasFDerivAt).congr_of_eventuallyEq hprod
  have hpv := congrArg (fun L : E →L[ℝ] ℝ => L v) hp.fderiv
  simp only [add_apply, smul_apply,
    smul_eq_mul, h₀, h₁] at hpv
  apply (eq_div_iff hne).2
  have hc := div_mul_cancel₀ (ρ x) hne
  nlinarith [hpv, congrArg (fun t => a * t) hc]




theorem d000020 {s : Set E} (hs : IsOpen s)
    (V : I → E → E) (hV : ∀ i, ContDiffOn ℝ ∞ (V i) s)
    {R : E → ℝ} (hR : ContDiffOn ℝ 2 R s)
    (S : I → E → ℝ)
    (hsource : ∀ i, ∀ y ∈ s, fderiv ℝ R y (V i y) = S i y)
    {J : Type*} [Fintype J] (words : J → _root_.GD.N0227.N0544.d000002 I) (c : J → ℝ)
    {x v : E} (hx : x ∈ s)
    (hv : v = ∑ j, c j • (words j).d000003 V x)
    {κ H ρ : ℝ} (hκ : κ ≠ 0)
    (hcharacter : fderiv ℝ R x v = κ * R x) (hρ : ρ = H * R x) :
    ρ = (H / κ) * ∑ j, c j * (words j).d000017 V S x := by
  have hsum : ∑ j, c j * (words j).d000017 V S x = κ * R x := by
    rw [← hcharacter, hv, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul]
    simp only [smul_eq_mul, (words j).d000018 hs V hV hR S hsource x hx]
  rw [hsum, hρ]
  field_simp



theorem d000021 {J M : E → ℝ} {x v : E}
    (hJ : DifferentiableAt ℝ J x) (hM : DifferentiableAt ℝ M x)
    {κ lam : ℝ} (hj : fderiv ℝ J x v = κ * J x)
    (hm : fderiv ℝ M x v = lam * M x) :
    fderiv ℝ (fun y => J y * M y) x v = (lam + κ) * (J x * M x) := by
  rw [(hJ.hasFDerivAt.fun_mul hM.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply,
    smul_eq_mul, hj, hm]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in

theorem d000022 {J M₀ M₁ : E → ℝ} {x : E} (hJ : J x ≠ 0) :
    (J x * M₁ x) / (J x * M₀ x) = M₁ x / M₀ x :=
  mul_div_mul_left _ _ hJ


theorem d000023 (lam₀ lam₁ κ : ℝ) :
    (lam₁ + κ) - (lam₀ + κ) = lam₁ - lam₀ := by ring

end

end GD.N0227.N0544

#print axioms _root_.GD.N0227.N0544.d000002.d000008
#print axioms _root_.GD.N0227.N0544.d000009
#print axioms _root_.GD.N0227.N0544.d000011
#print axioms _root_.GD.N0227.N0544.d000014
#print axioms _root_.GD.N0227.N0544.d000015
#print axioms _root_.GD.N0227.N0544.d000016
#print axioms _root_.GD.N0227.N0544.d000022
#print axioms _root_.GD.N0227.N0544.d000002.d000018
#print axioms _root_.GD.N0227.N0544.d000019
#print axioms _root_.GD.N0227.N0544.d000020
#print axioms _root_.GD.N0227.N0544.d000021
