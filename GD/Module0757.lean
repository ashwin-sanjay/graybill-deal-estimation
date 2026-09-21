import GD.Module0756
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option warningAsError true










open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

namespace GD.N0232.N0719.N0995

open _root_.GD.N0232.N0719.N0873 _root_.GD.N0232.N0719.N0989
open _root_.GD.N0232.N0719.N0994
open _root_.GD.N0232.N0719.N0983 (d009709)
open _root_.GD.N0232.N0720.N1382 (d004663 d004664 d004665)

noncomputable section
variable {k : ℕ}

def d011385 (phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ) (i : Fin k) (p : _root_.GD.N0232.N0719.N0983.d009709 k) : ℝ :=
  phi p * _root_.GD.N0232.N0719.N0994.d011372 p i

theorem d011386 {phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ}
    (hphi : Continuous phi) (i : Fin k) : Continuous (_root_.GD.N0232.N0719.N0995.d011385 phi i) := by
  unfold _root_.GD.N0232.N0719.N0995.d011385 _root_.GD.N0232.N0719.N0994.d011372
  exact hphi.mul (continuous_subtype_val.comp
    (_root_.GD.N0232.N0719.N0983.d009711 i))

def d011387 (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) (i : Fin k) : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) →L[ℝ] ℝ :=
  (-x.1 i) • _root_.GD.N0232.N0719.N0873.d011298 i - _root_.GD.N0232.N0719.N0873.d011299 i

def d011388 (n m : ℕ) (phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ)
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) (p : _root_.GD.N0232.N0719.N0994.d011371 k) : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) →L[ℝ] ℝ :=
  ∑ i, (_root_.GD.N0232.N0719.N0994.d011381 (n + 2) m (_root_.GD.N0232.N0719.N0995.d011385 phi i) x p • _root_.GD.N0232.N0719.N0995.d011387 x i +
    _root_.GD.N0232.N0719.N0994.d011381 (n + 1) (m + 1) (_root_.GD.N0232.N0719.N0995.d011385 phi i) x p • _root_.GD.N0232.N0719.N0873.d011298 i)

def d011389 (n m : ℕ) (phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ)
    (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) : ℝ :=
  ∫ p, _root_.GD.N0232.N0719.N0994.d011381 n m phi x p ∂nu

def d011390 (n m : ℕ) (phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ)
    (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) →L[ℝ] ℝ :=
  ∑ i, (_root_.GD.N0232.N0719.N0995.d011389 (n + 2) m (_root_.GD.N0232.N0719.N0995.d011385 phi i) nu x • _root_.GD.N0232.N0719.N0995.d011387 x i +
    _root_.GD.N0232.N0719.N0995.d011389 (n + 1) (m + 1) (_root_.GD.N0232.N0719.N0995.d011385 phi i) nu x • _root_.GD.N0232.N0719.N0873.d011298 i)

theorem d011391 (n m : ℕ) (phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ)
    {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) (p : _root_.GD.N0232.N0719.N0994.d011371 k) :
    HasFDerivAt (fun y => _root_.GD.N0232.N0719.N0994.d011381 n m phi y p) (_root_.GD.N0232.N0719.N0995.d011388 n m phi x p) x := by
  apply ((_root_.GD.N0232.N0719.N0989.d011348 n p.1 (_root_.GD.N0232.N0719.N0994.d011372 p.2)
    (_root_.GD.N0232.N0719.N0989.d011345 _ (_root_.GD.N0232.N0719.N0994.d011373 p.2) (_root_.GD.N0232.N0719.N0994.d011374 p.2) hx)).const_mul
      (p.1 ^ m * phi p.2)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [_root_.GD.N0232.N0719.N0995.d011388, _root_.GD.N0232.N0719.N0989.d011347,
    _root_.GD.N0232.N0719.N0989.d011341, _root_.GD.N0232.N0719.N0989.d011342, _root_.GD.N0232.N0719.N0994.d011381, _root_.GD.N0232.N0719.N0995.d011385, _root_.GD.N0232.N0719.N0995.d011387,
    sum_apply, add_apply, sub_apply, smul_apply, smul_eq_mul, mul_add]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pow_succ]
  ring

theorem d011392 (n m : ℕ) {phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ}
    (hphi : Continuous phi) {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) :
    Continuous (_root_.GD.N0232.N0719.N0995.d011388 n m phi x) := by
  apply continuous_finsetSum
  intro i _
  exact ((_root_.GD.N0232.N0719.N0994.d011382 _ _ (_root_.GD.N0232.N0719.N0995.d011386 hphi i) hx).smul
    continuous_const).add
    ((_root_.GD.N0232.N0719.N0994.d011382 _ _ (_root_.GD.N0232.N0719.N0995.d011386 hphi i) hx).smul continuous_const)

theorem d011393 (n m : ℕ) {phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ}
    (hphi : Continuous phi) (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (hnu : _root_.GD.N0232.N0719.N0994.d011375 nu)
    {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) :
    (∫ p, _root_.GD.N0232.N0719.N0995.d011388 n m phi x p ∂nu) = _root_.GD.N0232.N0719.N0995.d011390 n m phi nu x := by
  have hleft i := (_root_.GD.N0232.N0719.N0994.d011384 (n + 2) m
    (_root_.GD.N0232.N0719.N0995.d011386 hphi i) nu hnu hx).smul_const (_root_.GD.N0232.N0719.N0995.d011387 x i)
  have hright i := (_root_.GD.N0232.N0719.N0994.d011384 (n + 1) (m + 1)
    (_root_.GD.N0232.N0719.N0995.d011386 hphi i) nu hnu hx).smul_const (_root_.GD.N0232.N0719.N0873.d011298 i)
  unfold _root_.GD.N0232.N0719.N0995.d011388 _root_.GD.N0232.N0719.N0995.d011390
  rw [integral_finsetSum Finset.univ
    (f := fun i p => _root_.GD.N0232.N0719.N0994.d011381 (n + 2) m (_root_.GD.N0232.N0719.N0995.d011385 phi i) x p • _root_.GD.N0232.N0719.N0995.d011387 x i +
      _root_.GD.N0232.N0719.N0994.d011381 (n + 1) (m + 1) (_root_.GD.N0232.N0719.N0995.d011385 phi i) x p • _root_.GD.N0232.N0719.N0873.d011298 i)
    (fun i _ => (hleft i).add (hright i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_add (hleft i) (hright i), integral_smul_const, integral_smul_const]
  rfl

theorem d011394 (n m : ℕ) {phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ}
    (hphi : Continuous phi) {delta R beta : ℝ}
    (hd : 0 < delta) (hR : 0 < R) (hbeta : _root_.GD.N0232.N0720.N1382.d004663 delta R < beta) :
    ∃ C : ℝ, ∀ x ∈ _root_.GD.N0232.N0719.N0994.d011376 delta R, ∀ p : _root_.GD.N0232.N0719.N0994.d011371 k,
      ‖_root_.GD.N0232.N0719.N0995.d011388 n m phi x p‖ ≤ C * Real.exp (beta * p.1 ^ 2) := by
  have h0 (i : Fin k) := _root_.GD.N0232.N0719.N0994.d011383 (n + 2) m
    (_root_.GD.N0232.N0719.N0995.d011386 hphi i) hd hR hbeta
  have h1 (i : Fin k) := _root_.GD.N0232.N0719.N0994.d011383 (n + 1) (m + 1)
    (_root_.GD.N0232.N0719.N0995.d011386 hphi i) hd hR hbeta
  choose C0 hC0 hb0 using h0
  choose C1 hC1 hb1 using h1
  refine ⟨∑ i, (C0 i * (R * ‖_root_.GD.N0232.N0719.N0873.d011298 i‖ + ‖_root_.GD.N0232.N0719.N0873.d011299 i‖) +
    C1 i * ‖_root_.GD.N0232.N0719.N0873.d011298 i‖), ?_⟩
  intro x hx p
  unfold _root_.GD.N0232.N0719.N0995.d011388
  apply (norm_sum_le _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hdir : ‖_root_.GD.N0232.N0719.N0995.d011387 x i‖ ≤ R * ‖_root_.GD.N0232.N0719.N0873.d011298 i‖ + ‖_root_.GD.N0232.N0719.N0873.d011299 i‖ := by
    unfold _root_.GD.N0232.N0719.N0995.d011387
    apply (norm_sub_le _ _).trans
    rw [norm_smul, norm_neg, Real.norm_eq_abs]
    exact add_le_add (mul_le_mul_of_nonneg_right (hx.1 i).le (norm_nonneg _)) le_rfl
  have hC0i := hC0 i
  have hleft := mul_le_mul (hb0 i x hx p) hdir (norm_nonneg _) (by positivity)
  have hright := mul_le_mul_of_nonneg_right (hb1 i x hx p) (norm_nonneg (_root_.GD.N0232.N0719.N0873.d011298 i))
  apply (norm_add_le _ _).trans
  simp only [norm_smul]
  nlinarith

theorem d011395 (n m : ℕ) {phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ}
    (hphi : Continuous phi) (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (hnu : _root_.GD.N0232.N0719.N0994.d011375 nu)
    {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) :
    HasFDerivAt (_root_.GD.N0232.N0719.N0995.d011389 n m phi nu) (_root_.GD.N0232.N0719.N0995.d011390 n m phi nu x) x := by
  obtain ⟨delta, R, hd, hR, hbox⟩ := _root_.GD.N0232.N0719.N0994.d011380 hx
  let beta := (_root_.GD.N0232.N0720.N1382.d004663 delta R + 1 / 2) / 2
  have hb0 : 0 < beta := by dsimp [beta]; linarith [_root_.GD.N0232.N0720.N1382.d004664 hd hR]
  have hb1 : beta < 1 / 2 := by dsimp [beta]; linarith [_root_.GD.N0232.N0720.N1382.d004665 hd (R := R)]
  have hbb : _root_.GD.N0232.N0720.N1382.d004663 delta R < beta := by dsimp [beta]; linarith [_root_.GD.N0232.N0720.N1382.d004665 hd (R := R)]
  obtain ⟨C, hbound⟩ := _root_.GD.N0232.N0719.N0995.d011394 n m hphi hd hR hbb
  have hsub : _root_.GD.N0232.N0719.N0994.d011376 delta R ⊆ (_root_.GD.N0232.N0719.N0989.d011338 : Set (_root_.GD.N0232.N0719.N0873.d011295 (Fin k))) :=
    fun y hy i => hd.trans (hy.2 i)
  have hmeas : ∀ᶠ y : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) in 𝓝 x,
      AEStronglyMeasurable (_root_.GD.N0232.N0719.N0994.d011381 n m phi y) nu := by
    filter_upwards [_root_.GD.N0232.N0719.N0994.d011377.mem_nhds hx] with y hy
    exact (_root_.GD.N0232.N0719.N0994.d011382 n m hphi hy).aestronglyMeasurable
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (H := _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) (E := ℝ) (α := _root_.GD.N0232.N0719.N0994.d011371 k) (x₀ := x)
    (F := _root_.GD.N0232.N0719.N0994.d011381 n m phi) (F' := _root_.GD.N0232.N0719.N0995.d011388 n m phi) (μ := nu)
    (s := _root_.GD.N0232.N0719.N0994.d011376 delta R) (bound := fun p : _root_.GD.N0232.N0719.N0994.d011371 k => C * Real.exp (beta * p.1 ^ 2))
    hbox hmeas (_root_.GD.N0232.N0719.N0994.d011384 n m hphi nu hnu hx)
    (_root_.GD.N0232.N0719.N0995.d011392 n m hphi hx).aestronglyMeasurable
    (ae_of_all _ fun p y hy => hbound y hy p)
    ((hnu beta hb0 hb1).const_mul C)
    (ae_of_all _ fun p y hy => _root_.GD.N0232.N0719.N0995.d011391 n m phi (hsub hy) p)
  rw [_root_.GD.N0232.N0719.N0995.d011393 n m hphi nu hnu hx] at hderiv
  exact hderiv

theorem d011396 (n m : ℕ) {phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ}
    (hphi : Continuous phi) (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (hnu : _root_.GD.N0232.N0719.N0994.d011375 nu) :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0719.N0995.d011389 n m phi nu) _root_.GD.N0232.N0719.N0989.d011338 := by
  have hall : ∀ j : ℕ, ∀ n m : ℕ, ∀ phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ, Continuous phi →
      ContDiffOn ℝ j (_root_.GD.N0232.N0719.N0995.d011389 n m phi nu) _root_.GD.N0232.N0719.N0989.d011338 := by
    intro j
    induction j with
    | zero =>
      intro n m phi hphi
      change ContDiffOn ℝ 0 (_root_.GD.N0232.N0719.N0995.d011389 n m phi nu) _root_.GD.N0232.N0719.N0989.d011338
      rw [contDiffOn_zero]
      intro x hx
      exact (_root_.GD.N0232.N0719.N0995.d011395 n m hphi nu hnu hx).continuousAt.continuousWithinAt
    | succ j ih =>
      intro n m phi hphi
      rw [Nat.cast_add, Nat.cast_one]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn _root_.GD.N0232.N0719.N0994.d011377.uniqueDiffOn).2
      refine ⟨by simp, _root_.GD.N0232.N0719.N0995.d011390 n m phi nu, ?_, ?_⟩
      · unfold _root_.GD.N0232.N0719.N0995.d011390
        apply ContDiffOn.sum
        intro i _
        have hdir : ContDiffOn ℝ j (fun x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) => _root_.GD.N0232.N0719.N0995.d011387 x i) _root_.GD.N0232.N0719.N0989.d011338 := by
          unfold _root_.GD.N0232.N0719.N0995.d011387
          fun_prop
        exact ((ih _ _ _ (_root_.GD.N0232.N0719.N0995.d011386 hphi i)).smul hdir).add
          ((ih _ _ _ (_root_.GD.N0232.N0719.N0995.d011386 hphi i)).smul contDiffOn_const)
      · intro x hx
        exact (_root_.GD.N0232.N0719.N0995.d011395 n m hphi nu hnu hx).hasFDerivWithinAt
  exact contDiffOn_infty.mpr fun j => hall j n m phi hphi

end
end GD.N0232.N0719.N0995

#print axioms _root_.GD.N0232.N0719.N0995.d011395
#print axioms _root_.GD.N0232.N0719.N0995.d011396
