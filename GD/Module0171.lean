import GD.Module0169

set_option warningAsError true
set_option autoImplicit false










open MeasureTheory
open scoped LineDeriv SchwartzMap

namespace GD.N0232.N0720.N1233

noncomputable section

open _root_.GD.N0232.N0720.N1230

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]



def d002008 (χ : 𝓢(D, ℝ)) : ℕ → 𝓢(D, ℝ) → 𝓢(D, ℝ)
  | 0, f => f
  | n + 1, f => _root_.GD.N0232.N0720.N1230.d001994 χ (d002008 χ n f)

@[simp] theorem d002009 (χ f : 𝓢(D, ℝ)) (n : ℕ) (x : D) :
    _root_.GD.N0232.N0720.N1233.d002008 χ n f x = χ x ^ n * f x := by
  induction n with
  | zero => simp [_root_.GD.N0232.N0720.N1233.d002008]
  | succ n ih => simp only [_root_.GD.N0232.N0720.N1233.d002008, _root_.GD.N0232.N0720.N1230.d001995, ih, pow_succ]; ring

theorem d002010 (χ f : 𝓢(D, ℝ)) (n : ℕ) :
    (_root_.GD.N0232.N0720.N1233.d002008 χ n f : D → ℝ) = fun x ↦ χ x ^ n * f x := by
  funext x
  exact _root_.GD.N0232.N0720.N1233.d002009 χ f n x


theorem d002011 (χ f : 𝓢(D, ℝ)) (n : ℕ) (v : D) :
    ∂_{v} (_root_.GD.N0232.N0720.N1233.d002008 χ (n + 1) f) =
      _root_.GD.N0232.N0720.N1233.d002008 χ n (((n + 1 : ℕ) : ℝ) • _root_.GD.N0232.N0720.N1230.d001994 (∂_{v} χ) f +
        _root_.GD.N0232.N0720.N1230.d001994 χ (∂_{v} f)) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, _root_.GD.N0232.N0720.N1233.d002010]
  have hd := (((χ.differentiableAt (x := x)).hasFDerivAt.pow (n + 1)).mul
    (f.differentiableAt (x := x)).hasFDerivAt)
  change (fderiv ℝ ((fun y ↦ χ y ^ (n + 1)) * (f : D → ℝ)) x) v = _
  rw [hd.fderiv]
  simp only [add_apply, smul_apply,
    smul_eq_mul, _root_.GD.N0232.N0720.N1233.d002009, nsmul_eq_mul,
    _root_.GD.N0232.N0720.N1230.d001995, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  ring

theorem d002012
    (χ f : 𝓢(D, ℝ)) (dirs : List D) (n : ℕ) :
    ∃ r : 𝓢(D, ℝ), _root_.GD.N0232.N0720.N1230.d001993 dirs (_root_.GD.N0232.N0720.N1233.d002008 χ (n + dirs.length) f) = _root_.GD.N0232.N0720.N1233.d002008 χ n r := by
  induction dirs generalizing f with
  | nil => exact ⟨f, rfl⟩
  | cons v vs ih =>
      simp only [List.length_cons, ← Nat.add_assoc, _root_.GD.N0232.N0720.N1230.d001993,
        _root_.GD.N0232.N0720.N1233.d002011]
      exact ih _

def d002013 (χ : 𝓢(D, ℝ)) : 𝓢(D, ℝ) := _root_.GD.N0232.N0720.N1233.d002008 χ 7 χ

@[simp] theorem d002014 (χ : 𝓢(D, ℝ)) (x : D) : _root_.GD.N0232.N0720.N1233.d002013 χ x = χ x ^ 8 := by
  simp only [_root_.GD.N0232.N0720.N1233.d002013, _root_.GD.N0232.N0720.N1233.d002009]
  ring

theorem d002015
    (χ f : 𝓢(D, ℝ)) (dirs : List D) (hlen : dirs.length ≤ 4) :
    ∃ r : 𝓢(D, ℝ),
      _root_.GD.N0232.N0720.N1230.d001993 dirs (_root_.GD.N0232.N0720.N1230.d001994 (_root_.GD.N0232.N0720.N1233.d002013 χ) f) = _root_.GD.N0232.N0720.N1233.d002008 χ 4 r := by
  have heq : _root_.GD.N0232.N0720.N1230.d001994 (_root_.GD.N0232.N0720.N1233.d002013 χ) f = _root_.GD.N0232.N0720.N1233.d002008 χ 8 f := by
    ext x
    simp
  have hn : 8 - dirs.length + dirs.length = 8 := by omega
  obtain ⟨r, hr⟩ := _root_.GD.N0232.N0720.N1233.d002012 χ f dirs (8 - dirs.length)
  rw [hn] at hr
  refine ⟨_root_.GD.N0232.N0720.N1233.d002008 χ (4 - dirs.length) r, ?_⟩
  rw [heq, hr]
  ext x
  simp only [_root_.GD.N0232.N0720.N1233.d002009, ← mul_assoc, ← pow_add]
  congr 2
  omega

theorem d002016
    {J : Type*} [Fintype J]
    (χ : 𝓢(D, ℝ)) (directions : J → List D) (coefficient : J → 𝓢(D, ℝ))
    (hlen : ∀ j, (directions j).length ≤ 4) :
    ∃ R : 𝓢(D, ℝ),
      _root_.GD.N0232.N0720.N1230.d001998 directions coefficient (_root_.GD.N0232.N0720.N1233.d002013 χ) = _root_.GD.N0232.N0720.N1233.d002008 χ 4 R := by
  classical
  choose r hr using fun j ↦ _root_.GD.N0232.N0720.N1233.d002015 χ (coefficient j)
    (directions j) (hlen j)
  refine ⟨∑ j, ((-1 : ℝ) ^ (directions j).length) • r j, ?_⟩
  ext x
  simp only [_root_.GD.N0232.N0720.N1230.d002000, hr, _root_.GD.N0232.N0720.N1233.d002009,
    sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring



theorem d002017
    {J : Type*} [Fintype J]
    (χ : 𝓢(D, ℝ)) (directions : J → List D) (coefficient : J → 𝓢(D, ℝ))
    (hlen : ∀ j, (directions j).length ≤ 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ x,
      (_root_.GD.N0232.N0720.N1230.d001998 directions coefficient (_root_.GD.N0232.N0720.N1233.d002013 χ) x) ^ 2 ≤
        K * _root_.GD.N0232.N0720.N1233.d002013 χ x := by
  obtain ⟨R, hR⟩ := _root_.GD.N0232.N0720.N1233.d002016 χ directions coefficient hlen
  let M : ℝ := SchwartzMap.seminorm ℝ 0 0 R
  have hm (x : D) : |R x| ≤ M := SchwartzMap.norm_le_seminorm ℝ R x
  have hM : 0 ≤ M := (abs_nonneg (R 0)).trans (hm 0)
  refine ⟨M ^ 2 + 1, by positivity, ?_⟩
  intro x
  have hb := abs_le.mp (hm x)
  have hs : R x ^ 2 ≤ M ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (show 0 ≤ M + R x by linarith [hb.1])]
  calc
    _ = χ x ^ 8 * R x ^ 2 := by rw [hR, _root_.GD.N0232.N0720.N1233.d002009]; ring
    _ ≤ χ x ^ 8 * M ^ 2 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (M ^ 2 + 1) * _root_.GD.N0232.N0720.N1233.d002013 χ x := by
      rw [_root_.GD.N0232.N0720.N1233.d002014]
      nlinarith [show 0 ≤ χ x ^ 8 by positivity]

end
end GD.N0232.N0720.N1233

#print axioms _root_.GD.N0232.N0720.N1233.d002017
