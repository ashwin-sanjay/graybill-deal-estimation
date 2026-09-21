import GD.Module0049

set_option autoImplicit false
set_option warningAsError true

















open Filter Set Topology
open scoped BigOperators

namespace GD.N0100.N0345

open _root_.GD.N0230.N0622
open _root_.GD.N0230.N0560

noncomputable section

variable {H Θ I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem d008413 (x y : H) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ‖a • x + b • y‖ ^ 2 =
      a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - a * b * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
    real_inner_smul_left, inner_smul_right, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb, mul_pow, mul_pow]
  obtain rfl := eq_sub_of_add_eq hab
  ring



theorem d008414 [Fintype I]
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ)
    (packet : I → Θ) (weight : I → ℝ)
    (hD : Convex ℝ D) (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (hweight : ∀ i, 0 ≤ weight i)
    (scale offset : ℝ)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (x y : H) (hx : x ∈ D) (hy : y ∈ D)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    _root_.GD.N0230.N0560.d000624 risk theta0 packet weight (a • x + b • y) ≤
      a * _root_.GD.N0230.N0560.d000624 risk theta0 packet weight x +
      b * _root_.GD.N0230.N0560.d000624 risk theta0 packet weight y -
      scale * a * b * ‖x - y‖ ^ 2 := by
  have hm := hD hx hy ha hb hab
  have hsum : (∑ i, weight i * risk (packet i) (a • x + b • y)) ≤
      a * (∑ i, weight i * risk (packet i) x) +
      b * (∑ i, weight i * risk (packet i) y) := by
    calc
      _ ≤ ∑ i, weight i * (a * risk (packet i) x + b * risk (packet i) y) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          ((hconvex (packet i)).2 hx hy ha hb hab) (hweight i)
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  unfold _root_.GD.N0230.N0560.d000624
  rw [hreference _ hm, hreference x hx, hreference y hy,
    _root_.GD.N0100.N0345.d008413 x y a b ha hb hab]
  have hoffset : a * offset + b * offset = offset := by
    rw [← add_mul, hab, one_mul]
  nlinarith



theorem d008415 [Fintype I]
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ)
    (packet : I → Θ) (weight : I → ℝ)
    (hD : Convex ℝ D) (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (scale offset : ℝ)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (seed p : H) (hseed : seed ∈ D) (hp : p ∈ D)
    (hbayes : _root_.GD.N0230.N0622.d000607 D risk theta0 packet weight p) :
    scale * ‖seed - p‖ ^ 2 ≤ _root_.GD.N0230.N0560.d000625 risk theta0 packet weight seed p := by
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have htpos (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have htone (n : ℕ) : t n ≤ 1 := by
    dsimp [t]
    exact (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hbound (n : ℕ) :
      (1 - t n) * (scale * ‖seed - p‖ ^ 2) ≤
        _root_.GD.N0230.N0560.d000625 risk theta0 packet weight seed p := by
    have hc := _root_.GD.N0100.N0345.d008414 D risk theta0 packet weight hD hconvex
      hbayes.1 scale offset hreference seed p hseed hp
      (t n) (1 - t n) (htpos n).le (sub_nonneg.mpr (htone n)) (by ring)
    have hm := hbayes.2 ((t n) • seed + (1 - t n) • p)
      (hD hseed hp (htpos n).le (sub_nonneg.mpr (htone n)) (by ring))
    change _root_.GD.N0230.N0560.d000624 risk theta0 packet weight p ≤
      _root_.GD.N0230.N0560.d000624 risk theta0 packet weight ((t n) • seed + (1 - t n) • p) at hm
    apply (mul_le_mul_iff_right₀ (htpos n)).mp
    unfold _root_.GD.N0230.N0560.d000625
    nlinarith
  have hzero : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n => (1 - t n) * (scale * ‖seed - p‖ ^ 2))
      atTop (𝓝 (scale * ‖seed - p‖ ^ 2)) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (𝓝 1)).sub hzero).mul_const (scale * ‖seed - p‖ ^ 2)
  exact le_of_tendsto hlim (Eventually.of_forall hbound)



theorem d008416 [Fintype I]
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ)
    (packet : I → Θ) (weight : I → ℝ)
    (hD : Convex ℝ D) (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (hweight : ∀ i, 0 ≤ weight i)
    (scale offset : ℝ)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (seed p d : H) (hseed : seed ∈ D) (hd : d ∈ D)
    (hdom : ∀ theta, risk theta d ≤ risk theta seed)
    (eta : ℝ)
    (happrox : ∀ x ∈ D, _root_.GD.N0230.N0560.d000624 risk theta0 packet weight p ≤
      _root_.GD.N0230.N0560.d000624 risk theta0 packet weight x + eta) :
    scale * ‖d - seed‖ ^ 2 ≤
      4 * (_root_.GD.N0230.N0560.d000625 risk theta0 packet weight seed p + eta) := by
  have hsum : (∑ i, weight i * risk (packet i) d) ≤
      ∑ i, weight i * risk (packet i) seed :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hdom _) (hweight i)
  have hobj : _root_.GD.N0230.N0560.d000624 risk theta0 packet weight d ≤
      _root_.GD.N0230.N0560.d000624 risk theta0 packet weight seed := add_le_add (hdom theta0) hsum
  have hc := _root_.GD.N0100.N0345.d008414 D risk theta0 packet weight hD hconvex
    hweight scale offset hreference d seed hd hseed
    (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hm := happrox ((1 / 2 : ℝ) • d + (1 / 2 : ℝ) • seed)
    (hD hd hseed (by norm_num) (by norm_num) (by norm_num))
  unfold _root_.GD.N0230.N0560.d000625
  nlinarith


theorem d008417 [Fintype I]
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ)
    (packet : I → Θ) (weight : I → ℝ)
    (hD : Convex ℝ D) (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (scale offset : ℝ)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (seed p d : H) (hseed : seed ∈ D) (hd : d ∈ D)
    (hdom : ∀ theta, risk theta d ≤ risk theta seed)
    (hbayes : _root_.GD.N0230.N0622.d000607 D risk theta0 packet weight p) :
    scale * ‖d - seed‖ ^ 2 ≤
      4 * _root_.GD.N0230.N0560.d000625 risk theta0 packet weight seed p := by
  simpa using _root_.GD.N0100.N0345.d008416
    D risk theta0 packet weight hD hconvex hbayes.1 scale offset hreference
    seed p d hseed hd hdom 0 (by simpa only [_root_.GD.N0230.N0560.d000624, add_zero] using hbayes.2)



theorem d008418
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ)
    (hD : Convex ℝ D) (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (scale offset : ℝ) (hscale : 0 < scale)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (seed : H) (hseed : seed ∈ D)
    (size : ℕ → ℕ) (packet : ∀ n, Fin (size n) → Θ)
    (weight : ∀ n, Fin (size n) → ℝ) (p : ℕ → H)
    (hp : ∀ n, p n ∈ D)
    (hbayes : ∀ n, _root_.GD.N0230.N0622.d000607 D risk theta0 (packet n) (weight n) (p n))
    (hzero : Tendsto (fun n => _root_.GD.N0230.N0560.d000625 risk theta0 (packet n) (weight n) seed (p n))
      atTop (𝓝 0)) :
    Tendsto p atTop (𝓝 seed) := by
  have hsq : Tendsto (fun n => ‖p n - seed‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) _
      (show Tendsto (fun n => _root_.GD.N0230.N0560.d000625 risk theta0 (packet n) (weight n) seed (p n) / scale)
        atTop (𝓝 0) by simpa using hzero.div_const scale)
    intro n
    apply (le_div_iff₀ hscale).2
    simpa [norm_sub_rev, mul_comm] using _root_.GD.N0100.N0345.d008415
      D risk theta0 (packet n) (weight n) hD hconvex scale offset hreference
      seed (p n) hseed (hp n) (hbayes n)
  have hnorm : Tendsto (fun n => ‖p n - seed‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero]
      using (Real.continuous_sqrt.tendsto 0).comp hsq
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm



theorem d008419
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ)
    (hD : Convex ℝ D) (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (scale offset : ℝ) (hscale : 0 < scale)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (seed d : H) (hseed : seed ∈ D) (hd : d ∈ D)
    (hdom : ∀ theta, risk theta d ≤ risk theta seed)
    (size : ℕ → ℕ) (packet : ∀ n, Fin (size n) → Θ)
    (weight : ∀ n, Fin (size n) → ℝ) (p : ℕ → H) (eta : ℕ → ℝ)
    (hweight : ∀ n i, 0 ≤ weight n i)
    (happrox : ∀ n x, x ∈ D → _root_.GD.N0230.N0560.d000624 risk theta0 (packet n) (weight n) (p n) ≤
      _root_.GD.N0230.N0560.d000624 risk theta0 (packet n) (weight n) x + eta n)
    (hzero : Tendsto (fun n => _root_.GD.N0230.N0560.d000625 risk theta0 (packet n) (weight n) seed (p n) + eta n)
      atTop (𝓝 0)) :
    d = seed := by
  have hbound (n : ℕ) : scale * ‖d - seed‖ ^ 2 ≤
      4 * (_root_.GD.N0230.N0560.d000625 risk theta0 (packet n) (weight n) seed (p n) + eta n) :=
    _root_.GD.N0100.N0345.d008416
      D risk theta0 (packet n) (weight n) hD hconvex (hweight n)
      scale offset hreference seed (p n) d hseed hd hdom (eta n) (happrox n)
  have hz : scale * ‖d - seed‖ ^ 2 ≤ 0 := by
    simpa using ge_of_tendsto (hzero.const_mul 4) (Eventually.of_forall hbound)
  by_contra hne
  have hp : 0 < scale * ‖d - seed‖ ^ 2 :=
    mul_pos hscale (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
  exact (not_le_of_gt hp) hz



theorem d008420
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ)
    (hD : Convex ℝ D) (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (scale offset : ℝ) (hscale : 0 < scale)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (seed : H) (hseed : seed ∈ D)
    (size : ℕ → ℕ) (packet : ∀ n, Fin (size n) → Θ)
    (weight : ∀ n, Fin (size n) → ℝ) (p : ℕ → H) (eta : ℕ → ℝ)
    (hweight : ∀ n i, 0 ≤ weight n i)
    (happrox : ∀ n x, x ∈ D → _root_.GD.N0230.N0560.d000624 risk theta0 (packet n) (weight n) (p n) ≤
      _root_.GD.N0230.N0560.d000624 risk theta0 (packet n) (weight n) x + eta n)
    (hzero : Tendsto (fun n => _root_.GD.N0230.N0560.d000625 risk theta0 (packet n) (weight n) seed (p n) + eta n)
      atTop (𝓝 0)) :
    _root_.GD.N0230.N0556.d000031
      (fun theta (d : D) => risk theta d) ⟨seed, hseed⟩ := by
  rintro ⟨d, hdom, theta, hbetter⟩
  have heq : (d : H) = seed :=
    _root_.GD.N0100.N0345.d008419 D risk theta0 hD hconvex
      scale offset hscale hreference seed d hseed d.property hdom
      size packet weight p eta hweight happrox hzero
  change risk theta (d : H) < risk theta seed at hbetter
  rw [heq] at hbetter
  exact (lt_irrefl _) hbetter






theorem d008421 :
    (∀ _ : Unit, ConvexOn ℝ (univ : Set ℝ) (fun x : ℝ => x ^ 2)) ∧
    _root_.GD.N0230.N0622.d000607 (univ : Set ℝ) (fun (_ : Unit) (x : ℝ) => x ^ 2)
      () (fun _ : Fin 0 => ()) (fun _ => 0) 0 ∧
    (∀ _ : Unit, (-1 : ℝ) ^ 2 ≤ (1 : ℝ) ^ 2) ∧
    _root_.GD.N0230.N0560.d000625 (fun (_ : Unit) (x : ℝ) => x ^ 2)
      () (fun _ : Fin 0 => ()) (fun _ => 0) 1 0 = 1 ∧
    ‖(-1 : ℝ) - 1‖ ^ 2 = 4 * _root_.GD.N0230.N0560.d000625 (fun (_ : Unit) (x : ℝ) => x ^ 2)
      () (fun _ : Fin 0 => ()) (fun _ => 0) 1 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _
    simpa only [Real.norm_eq_abs, sq_abs] using
      _root_.GD.N0230.N0622.d000610 (univ : Set ℝ) convex_univ
  · constructor
    · intro i
      exact Fin.elim0 i
    · intro x _
      simpa using sq_nonneg x
  · intro _
    norm_num
  · norm_num [_root_.GD.N0230.N0560.d000625, _root_.GD.N0230.N0560.d000624]
  · norm_num [_root_.GD.N0230.N0560.d000625, _root_.GD.N0230.N0560.d000624]

end
end GD.N0100.N0345

#print axioms _root_.GD.N0100.N0345.d008413
#print axioms _root_.GD.N0100.N0345.d008414
#print axioms _root_.GD.N0100.N0345.d008415
#print axioms _root_.GD.N0100.N0345.d008416
#print axioms _root_.GD.N0100.N0345.d008417
#print axioms _root_.GD.N0100.N0345.d008418
#print axioms _root_.GD.N0100.N0345.d008419
#print axioms _root_.GD.N0100.N0345.d008420
#print axioms _root_.GD.N0100.N0345.d008421
