import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring







namespace GD.N0106.N0428.N0765.N1624

set_option autoImplicit false
set_option warningAsError true

open Set Polynomial

open scoped ContDiff

noncomputable section


theorem d005779 (n : ℕ)
    {a b : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (v : Fin (n + 1) → ℝ) (hv : StrictMono v)
    (hvb : ∀ i, v i ∈ Icc a b) (hfz : ∀ i, f (v i) = 0) :
    ∃ x ∈ Icc a b, iteratedDeriv n f x = 0 := by
  induction n generalizing f with
  | zero =>
      exact ⟨v 0, hvb 0, by simpa only [iteratedDeriv_zero] using hfz 0⟩
  | succ n ih =>
      have hy : ∀ i : Fin (n + 1),
          ∃ y ∈ Ioo (v i.castSucc) (v i.succ), deriv f y = 0 := by
        intro i
        apply exists_deriv_eq_zero
          (hv (show i.castSucc < i.succ by
            change i.val < i.val + 1
            exact Nat.lt_succ_self _))
          hf.continuous.continuousOn
        rw [hfz, hfz]
      choose y hyb hyz using hy
      have hym : StrictMono y := by
        intro i j hij
        have hij' : i.succ ≤ j.castSucc := by
          change i.val + 1 ≤ j.val
          change i.val < j.val at hij
          exact Nat.succ_le_of_lt hij
        exact ((hyb i).2.trans_le (hv.monotone hij')).trans (hyb j).1
      have hyab : ∀ i, y i ∈ Icc a b := by
        intro i
        exact ⟨(hvb i.castSucc).1.trans (hyb i).1.le,
          (hyb i).2.le.trans (hvb i.succ).2⟩
      obtain ⟨x, hx, hzero⟩ := ih (contDiff_infty_iff_deriv.mp hf).2 y hym hyab hyz
      exact ⟨x, hx, by simpa only [iteratedDeriv_succ'] using hzero⟩


theorem d005780 (n : ℕ)
    {a b : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (s : Finset ℝ) (hs : s.card = n + 1)
    (hsb : ∀ x ∈ s, x ∈ Icc a b) (hfz : ∀ x ∈ s, f x = 0) :
    ∃ x ∈ Icc a b, iteratedDeriv n f x = 0 := by
  exact _root_.GD.N0106.N0428.N0765.N1624.d005779 n hf (s.orderEmbOfFin hs)
    (s.orderEmbOfFin hs).strictMono
    (fun i => hsb _ (s.orderEmbOfFin_mem hs i))
    (fun i => hfz _ (s.orderEmbOfFin_mem hs i))

theorem d005781 (p : ℝ[X]) :
    ContDiff ℝ ∞ (fun x : ℝ => p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
      simpa only [Polynomial.eval_monomial] using
        (contDiff_const.mul (contDiff_id.pow n) :
          ContDiff ℝ ∞ (fun x : ℝ => a * x ^ n))


theorem d005782 (n : ℕ) (p : ℝ[X]) :
    iteratedDeriv n (fun x : ℝ => p.eval x) =
      fun x : ℝ => (Polynomial.derivative^[n] p).eval x := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ', Function.iterate_succ_apply]
      have hd : deriv (fun x : ℝ => p.eval x) = fun x => p.derivative.eval x :=
        funext fun x => (p.hasDerivAt x).deriv
      rw [hd, ih]

theorem d005783 (s : Finset ℝ) (hs : s.card = 14) (x : ℝ) :
    iteratedDeriv 14 (fun t : ℝ => (∏ z ∈ s, (X - C z) : ℝ[X]).eval t) x =
      ((14 : ℕ).factorial : ℝ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1624.d005782,
    Polynomial.iterate_derivative_prod_X_sub_C (by simp only [hs, le_refl] : 14 ≤ s.card)]
  simp [hs]



theorem d005784 {a b x : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (s : Finset ℝ) (hs : s.card = 14)
    (hsb : ∀ t ∈ s, t ∈ Icc a b) (hx : x ∈ Icc a b) :
    ∃ ξ ∈ Icc a b,
      f x - (Lagrange.interpolate s id f).eval x =
        (iteratedDeriv 14 f ξ / ((14 : ℕ).factorial : ℝ)) * ∏ t ∈ s, (x - t) := by
  classical
  let p : ℝ[X] := Lagrange.interpolate s id f
  let q : ℝ[X] := ∏ t ∈ s, (X - C t)
  have hpnode : ∀ t ∈ s, p.eval t = f t := by
    intro t ht
    exact Lagrange.eval_interpolate_at_node f Function.injective_id.injOn ht
  have hqeval : ∀ t : ℝ, q.eval t = ∏ z ∈ s, (t - z) := by
    intro t
    simp only [q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  have hqnode : ∀ t ∈ s, q.eval t = 0 := by
    intro t ht
    rw [hqeval]
    exact Finset.prod_eq_zero ht (sub_self t)
  by_cases hxs : x ∈ s
  · refine ⟨x, hx, ?_⟩
    change f x - p.eval x = _
    rw [hpnode x hxs, sub_self, ← hqeval x, hqnode x hxs, mul_zero]
  have hqx : q.eval x ≠ 0 := by
    rw [hqeval]
    apply Finset.prod_ne_zero_iff.mpr
    intro z hz
    apply sub_ne_zero.mpr
    intro h
    apply hxs
    simpa only [h] using hz
  let k : ℝ := (f x - p.eval x) / q.eval x
  let g : ℝ → ℝ := fun t => f t - p.eval t - k * q.eval t
  have hp : ContDiff ℝ ∞ (fun t : ℝ => p.eval t) := _root_.GD.N0106.N0428.N0765.N1624.d005781 p
  have hq : ContDiff ℝ ∞ (fun t : ℝ => q.eval t) := _root_.GD.N0106.N0428.N0765.N1624.d005781 q
  have hg : ContDiff ℝ ∞ g := (hf.sub hp).sub (contDiff_const.mul hq)
  have hgzero : ∀ t ∈ insert x s, g t = 0 := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · dsimp [g, k]
      rw [div_mul_cancel₀ _ hqx, sub_self]
    · dsimp [g]
      rw [hpnode t ht, hqnode t ht]
      ring
  have hgpoints : ∀ t ∈ insert x s, t ∈ Icc a b := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hx
    · exact hsb t ht
  obtain ⟨ξ, hξ, hgξ⟩ := _root_.GD.N0106.N0428.N0765.N1624.d005780 14 hg (insert x s)
    (by simp [hxs, hs]) hgpoints hgzero
  have hf14 : ContDiff ℝ (14 : ℕ) f := hf.of_le (ENat.natCast_le_of_coe_top_le_withTop (N := ∞) le_rfl 14)
  have hp14 : ContDiff ℝ (14 : ℕ) (fun t : ℝ => p.eval t) := hp.of_le (ENat.natCast_le_of_coe_top_le_withTop (N := ∞) le_rfl 14)
  have hq14 : ContDiff ℝ (14 : ℕ) (fun t : ℝ => q.eval t) := hq.of_le (ENat.natCast_le_of_coe_top_le_withTop (N := ∞) le_rfl 14)
  have hpzero : iteratedDeriv 14 (fun t : ℝ => p.eval t) ξ = 0 := by
    rw [_root_.GD.N0106.N0428.N0765.N1624.d005782]
    have hd : p.degree < (14 : ℕ) := by
      simpa only [p, hs] using
        Lagrange.degree_interpolate_lt (s := s) (v := id) f Function.injective_id.injOn
    simp only [Polynomial.iterate_derivative_eq_zero_of_degree_lt hd, Polynomial.eval_zero]
  have hqfourteen : iteratedDeriv 14 (fun t : ℝ => q.eval t) ξ =
      ((14 : ℕ).factorial : ℝ) := _root_.GD.N0106.N0428.N0765.N1624.d005783 s hs ξ
  have hgcalc : iteratedDeriv 14 g ξ =
      iteratedDeriv 14 f ξ - k * ((14 : ℕ).factorial : ℝ) := by
    change iteratedDeriv 14 (fun t => f t - p.eval t - k * q.eval t) ξ = _
    rw [iteratedDeriv_fun_sub (hf14.sub hp14).contDiffAt
        (contDiff_const.mul hq14).contDiffAt,
      iteratedDeriv_fun_sub hf14.contDiffAt hp14.contDiffAt,
      iteratedDeriv_const_mul_field, hpzero, hqfourteen, sub_zero]
  have hk : k = iteratedDeriv 14 f ξ / ((14 : ℕ).factorial : ℝ) := by
    apply (eq_div_iff (by positivity : ((14 : ℕ).factorial : ℝ) ≠ 0)).mpr
    exact (sub_eq_zero.mp (hgcalc.symm.trans hgξ)).symm
  refine ⟨ξ, hξ, ?_⟩
  change f x - p.eval x = _
  calc
    f x - p.eval x = k * q.eval x := by
      dsimp [k]
      rw [div_mul_cancel₀ _ hqx]
    _ = (iteratedDeriv 14 f ξ / ((14 : ℕ).factorial : ℝ)) * ∏ t ∈ s, (x - t) := by
      rw [hk, hqeval]

end
end GD.N0106.N0428.N0765.N1624

#print axioms _root_.GD.N0106.N0428.N0765.N1624.d005779
#print axioms _root_.GD.N0106.N0428.N0765.N1624.d005780
#print axioms _root_.GD.N0106.N0428.N0765.N1624.d005782
#print axioms _root_.GD.N0106.N0428.N0765.N1624.d005783
#print axioms _root_.GD.N0106.N0428.N0765.N1624.d005784
