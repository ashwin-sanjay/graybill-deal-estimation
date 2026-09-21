import GD.Module0259
import GD.Module0643











open MeasureTheory Set Filter ProbabilityTheory
open scoped NNReal Topology BigOperators

namespace GD.N0232.N0719.N0985

noncomputable section

theorem d009753 {v : ℝ} (hv : 0 < v) (a h m : ℝ) :
    (∫ c : ℝ, (c + a * h) ^ 2 * Real.exp (-((c + a * m) ^ 2) / (2 * v))) =
      Real.sqrt (2 * Real.pi * v) * (v + a ^ 2 * (h - m) ^ 2) := by
  let M := a * (h - m)
  let S := Real.sqrt (2 * Real.pi * v)
  let F : ℝ → ℝ := fun x => x ^ 2 * Real.exp (-((x - M) ^ 2) / (2 * v))
  have hS : S ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < 2 * Real.pi * v)).ne'
  have hvn : v.toNNReal ≠ 0 := (Real.toNNReal_pos.mpr hv).ne'
  have hmoment := _root_.GD.N0232.N0719.N0879.d003727 M v.toNNReal
  rw [integral_gaussianReal_eq_integral_smul (E := ℝ) hvn] at hmoment
  simp only [smul_eq_mul, gaussianPDFReal, Real.coe_toNNReal v hv.le] at hmoment
  have hfactor : (fun x : ℝ => (Real.sqrt (2 * Real.pi * v))⁻¹ *
      Real.exp (-((x - M) ^ 2) / (2 * v)) * x ^ 2) = fun x => S⁻¹ * F x := by
    funext x
    dsimp [F, S]
    ring
  rw [hfactor, integral_const_mul] at hmoment
  have hI : (∫ x, F x) = S * (M ^ 2 + v) := by
    have hmul := congrArg (fun z : ℝ => S * z) hmoment
    simpa only [← mul_assoc, mul_inv_cancel₀ hS, one_mul] using hmul
  calc
    _ = ∫ c : ℝ, F (c + a * h) := by
      apply integral_congr_ae
      exact ae_of_all _ fun c => by
        dsimp [F, M]
        congr 2
        ring
    _ = ∫ x : ℝ, F x := integral_add_right_eq_self F (a * h)
    _ = _ := by rw [hI]; dsimp [S, M]; ring


theorem d009754 {C b : ℝ} (hC : 0 < C) (hb : -1 < b) :
    (∫ a : ℝ in Ioi 0, a ^ b * Real.exp (-C * a ^ 2)) =
      (1 / 2 : ℝ) * (1 / C) ^ ((b + 1) / 2) * Real.Gamma ((b + 1) / 2) := by
  let g : ℝ → ℝ := fun x => x ^ ((b + 1) / 2 - 1) * Real.exp (-(C * x))
  have hchange := integral_comp_rpow_Ioi_of_pos (g := g) (by norm_num : (0 : ℝ) < 2)
  have heq : (∫ x : ℝ in Ioi 0, ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) • g (x ^ (2 : ℝ))) =
      2 * ∫ x : ℝ in Ioi 0, x ^ b * Real.exp (-C * x ^ 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp [g]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
      ← Real.rpow_mul hx.le]
    have hexp : (2 : ℝ) * ((b + 1) / 2 - 1) = b - 1 := by ring
    rw [hexp, Real.rpow_two]
    have hpow : x * x ^ (b - 1) = x ^ b := by
      conv_lhs => lhs; rw [← Real.rpow_one x]
      rw [← Real.rpow_add hx]
      congr 1
      ring
    rw [show 2 * x * (x ^ (b - 1) * Real.exp (-(C * x ^ 2))) =
      2 * (x * x ^ (b - 1)) * Real.exp (-C * x ^ 2) by
        simp only [neg_mul]
        ring, hpow]
    ring
  rw [heq] at hchange
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (show 0 < (b + 1) / 2 by linarith) hC
  change (∫ x in Ioi 0, g x) = _ at hgamma
  rw [hgamma] at hchange
  linarith

def d009755 (N Q : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 / Q) ^ ((N + 1) / 2) * Real.Gamma ((N + 1) / 2)

def d009756 (N v Q h m : ℝ) : ℝ :=
  ∫ a : ℝ in Ioi 0, a ^ (N - 2) * Real.exp (-Q * a ^ 2) *
    ∫ c : ℝ, (c + a * h) ^ 2 * Real.exp (-((c + a * m) ^ 2) / (2 * v))



theorem d009757 {N v Q : ℝ} (hN : 1 < N) (hv : 0 < v) (hQ : 0 < Q)
    (h m : ℝ) :
    _root_.GD.N0232.N0719.N0985.d009756 N v Q h m = Real.sqrt (2 * Real.pi * v) *
      (v * _root_.GD.N0232.N0719.N0985.d009755 (N - 2) Q + (h - m) ^ 2 * _root_.GD.N0232.N0719.N0985.d009755 N Q) := by
  have hlow := integrableOn_rpow_mul_exp_neg_mul_sq hQ (show -1 < N - 2 by linarith)
  have hhigh := integrableOn_rpow_mul_exp_neg_mul_sq hQ (show -1 < N by linarith)
  unfold _root_.GD.N0232.N0719.N0985.d009756
  simp_rw [_root_.GD.N0232.N0719.N0985.d009753 hv]
  have heq : (∫ a : ℝ in Ioi 0, a ^ (N - 2) * Real.exp (-Q * a ^ 2) *
      (Real.sqrt (2 * Real.pi * v) * (v + a ^ 2 * (h - m) ^ 2))) =
      Real.sqrt (2 * Real.pi * v) * ∫ a : ℝ in Ioi 0,
        v * (a ^ (N - 2) * Real.exp (-Q * a ^ 2)) +
          (h - m) ^ 2 * (a ^ N * Real.exp (-Q * a ^ 2)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro a ha
    have hpow : a ^ (N - 2) * a ^ 2 = a ^ N := by
      rw [← Real.rpow_two, ← Real.rpow_add ha]
      congr 1
      ring
    calc
      _ = Real.sqrt (2 * Real.pi * v) *
          (v * (a ^ (N - 2) * Real.exp (-Q * a ^ 2)) +
            (h - m) ^ 2 * ((a ^ (N - 2) * a ^ 2) * Real.exp (-Q * a ^ 2))) := by ring
      _ = _ := by rw [hpow]
  rw [heq, integral_add (hlow.const_mul v) (hhigh.const_mul ((h - m) ^ 2)),
    integral_const_mul, integral_const_mul,
    _root_.GD.N0232.N0719.N0985.d009754 hQ (show -1 < N - 2 by linarith),
    _root_.GD.N0232.N0719.N0985.d009754 hQ (show -1 < N by linarith)]
  rfl

theorem d009758 {N Q : ℝ} (hN : -1 < N) (hQ : 0 < Q) :
    0 < _root_.GD.N0232.N0719.N0985.d009755 N Q := by
  unfold _root_.GD.N0232.N0719.N0985.d009755
  exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by positivity) _))
    (Real.Gamma_pos_of_pos (by linarith))


theorem d009759 {N v Q : ℝ} (hN : 1 < N) (hv : 0 < v) (hQ : 0 < Q)
    (h m : ℝ) :
    _root_.GD.N0232.N0719.N0985.d009756 N v Q h m - _root_.GD.N0232.N0719.N0985.d009756 N v Q m m =
      Real.sqrt (2 * Real.pi * v) * _root_.GD.N0232.N0719.N0985.d009755 N Q * (h - m) ^ 2 := by
  rw [_root_.GD.N0232.N0719.N0985.d009757 hN hv hQ, _root_.GD.N0232.N0719.N0985.d009757 hN hv hQ]
  ring

variable {J : Type*} [Fintype J]

def d009760 (N : ℝ) (v Q w : J → ℝ) (j : J) : ℝ :=
  w j * Real.sqrt (2 * Real.pi * v j) * _root_.GD.N0232.N0719.N0985.d009755 N (Q j)

def d009761 (N : ℝ) (v Q w m : J → ℝ) (h : ℝ) : ℝ :=
  ∑ j, w j * _root_.GD.N0232.N0719.N0985.d009756 N (v j) (Q j) h (m j)

open _root_.GD.N0230.N0615



theorem d009762 {N : ℝ} (hN : 1 < N) (v Q w m : J → ℝ)
    (hv : ∀ j, 0 < v j) (hQ : ∀ j, 0 < Q j)
    (hW : _root_.GD.N0230.N0615.d000151 (_root_.GD.N0232.N0719.N0985.d009760 N v Q w) ≠ 0) (h : ℝ) :
    _root_.GD.N0232.N0719.N0985.d009761 N v Q w m h -
        _root_.GD.N0232.N0719.N0985.d009761 N v Q w m (_root_.GD.N0230.N0615.d000152 (_root_.GD.N0232.N0719.N0985.d009760 N v Q w) m) =
      _root_.GD.N0230.N0615.d000151 (_root_.GD.N0232.N0719.N0985.d009760 N v Q w) *
        (h - _root_.GD.N0230.N0615.d000152 (_root_.GD.N0232.N0719.N0985.d009760 N v Q w) m) ^ 2 := by
  let c := _root_.GD.N0230.N0615.d000152 (_root_.GD.N0232.N0719.N0985.d009760 N v Q w) m
  have hdiff : _root_.GD.N0232.N0719.N0985.d009761 N v Q w m h - _root_.GD.N0232.N0719.N0985.d009761 N v Q w m c =
      (∑ j, _root_.GD.N0232.N0719.N0985.d009760 N v Q w j * (m j - h) ^ 2) -
        ∑ j, _root_.GD.N0232.N0719.N0985.d009760 N v Q w j * (m j - c) ^ 2 := by
    unfold _root_.GD.N0232.N0719.N0985.d009761
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [_root_.GD.N0232.N0719.N0985.d009757 hN (hv j) (hQ j), _root_.GD.N0232.N0719.N0985.d009757 hN (hv j) (hQ j)]
    unfold _root_.GD.N0232.N0719.N0985.d009760
    ring
  change _root_.GD.N0232.N0719.N0985.d009761 N v Q w m h - _root_.GD.N0232.N0719.N0985.d009761 N v Q w m c = _
  rw [hdiff, _root_.GD.N0230.N0615.d000158 (_root_.GD.N0232.N0719.N0985.d009760 N v Q w) m h hW]
  dsimp [c]
  ring

theorem d009763 {N : ℝ} (hN : 1 < N) (v Q w m : J → ℝ)
    (hv : ∀ j, 0 < v j) (hQ : ∀ j, 0 < Q j)
    (hw : ∀ j, 0 ≤ w j) (hwpos : ∃ j, 0 < w j) (h : ℝ) :
    _root_.GD.N0232.N0719.N0985.d009761 N v Q w m (_root_.GD.N0230.N0615.d000152 (_root_.GD.N0232.N0719.N0985.d009760 N v Q w) m) ≤
      _root_.GD.N0232.N0719.N0985.d009761 N v Q w m h := by
  have hW : 0 < _root_.GD.N0230.N0615.d000151 (_root_.GD.N0232.N0719.N0985.d009760 N v Q w) := by
    unfold _root_.GD.N0230.N0615.d000151 _root_.GD.N0232.N0719.N0985.d009760
    apply Finset.sum_pos'
    · exact fun j _ => mul_nonneg
        (mul_nonneg (hw j) (Real.sqrt_nonneg _))
        (_root_.GD.N0232.N0719.N0985.d009758 (by linarith : -1 < N) (hQ j)).le
    · obtain ⟨j, hj⟩ := hwpos
      exact ⟨j, Finset.mem_univ j, mul_pos
        (mul_pos hj (Real.sqrt_pos.mpr
          (mul_pos (mul_pos (by norm_num) Real.pi_pos) (hv j))))
        (_root_.GD.N0232.N0719.N0985.d009758 (by linarith : -1 < N) (hQ j))⟩
  apply sub_nonneg.mp
  rw [_root_.GD.N0232.N0719.N0985.d009762 hN v Q w m hv hQ hW.ne']
  positivity

end

end GD.N0232.N0719.N0985

#print axioms _root_.GD.N0232.N0719.N0985.d009753
#print axioms _root_.GD.N0232.N0719.N0985.d009754
#print axioms _root_.GD.N0232.N0719.N0985.d009757
#print axioms _root_.GD.N0232.N0719.N0985.d009759
#print axioms _root_.GD.N0232.N0719.N0985.d009762
#print axioms _root_.GD.N0232.N0719.N0985.d009763
