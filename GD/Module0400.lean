import GD.Module0398













noncomputable section

open Set
open scoped Topology

namespace GD.N0112

open _root_.GD.N0110


theorem d006170
    (f : ℝ → ℝ) (n : ℕ) (x M : ℝ)
    (hx : x ≠ 0)
    (hf : ContDiffOn ℝ (n + 1) f (uIcc 0 x))
    (hbound :
      ∀ y ∈ uIoo 0 x, |iteratedDeriv (n + 1) f y| ≤ M) :
    |f x - taylorWithinEval f n (uIcc 0 x) 0 x|
      ≤ M * |x| ^ (n + 1) / Nat.factorial (n + 1) := by
  obtain ⟨y, hy, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv hx.symm hf
  rw [hrem, abs_div, abs_mul, abs_pow, sub_zero,
    Nat.abs_cast]
  gcongr
  exact hbound y hy



theorem d006171
    (f : ℝ → ℝ) (S : Set ℝ) (x : ℝ)
    (hS : UniqueDiffOn ℝ S)
    (h0S : 0 ∈ S)
    (hf : ContDiffAt ℝ 2 f 0) :
    taylorWithinEval f 2 S 0 x =
      _root_.GD.N0110.d006124 (f 0) (iteratedDeriv 1 f 0)
        (iteratedDeriv 2 f 0) x := by
  have hd0 :
      iteratedDerivWithin 0 f S 0 = iteratedDeriv 0 f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hS
      (hf.of_le (by norm_num : (0 : WithTop ℕ∞) ≤ 2)) h0S
  have hd1 :
      iteratedDerivWithin 1 f S 0 = iteratedDeriv 1 f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hS
      (hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) h0S
  have hd2 :
      iteratedDerivWithin 2 f S 0 = iteratedDeriv 2 f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hS hf h0S
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, hd0, hd1, hd2,
    iteratedDeriv_zero, _root_.GD.N0110.d006124]
  ring


theorem d006172
    (f : ℝ → ℝ) (S : Set ℝ) (x : ℝ)
    (hS : UniqueDiffOn ℝ S)
    (h0S : 0 ∈ S)
    (hf : ContDiffAt ℝ 3 f 0) :
    taylorWithinEval f 3 S 0 x =
      _root_.GD.N0110.d006125 (f 0) (iteratedDeriv 1 f 0)
        (iteratedDeriv 2 f 0) (iteratedDeriv 3 f 0) x := by
  rw [taylorWithinEval_succ, _root_.GD.N0112.d006171 f S x hS h0S
    (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))]
  rw [iteratedDerivWithin_eq_iteratedDeriv hS hf h0S]
  unfold _root_.GD.N0110.d006125
  norm_num
  ring


theorem d006173
    (f : ℝ → ℝ) (S : Set ℝ) (x : ℝ)
    (hS : UniqueDiffOn ℝ S)
    (h0S : 0 ∈ S)
    (hf : ContDiffAt ℝ 4 f 0) :
    taylorWithinEval f 4 S 0 x =
      _root_.GD.N0110.d006126 (f 0) (iteratedDeriv 1 f 0)
        (iteratedDeriv 2 f 0) (iteratedDeriv 3 f 0)
        (iteratedDeriv 4 f 0) x := by
  rw [taylorWithinEval_succ, _root_.GD.N0112.d006172 f S x hS h0S
    (hf.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))]
  rw [iteratedDerivWithin_eq_iteratedDeriv hS hf h0S]
  unfold _root_.GD.N0110.d006126
  norm_num
  ring




theorem d006174
    (f : ℝ → ℝ) (h M : ℝ)
    (hh : 0 < h)
    (hf : ContDiffOn ℝ 3 f (Icc (-h) h))
    (hbound :
      ∀ y ∈ Icc (-h) h, |iteratedDeriv 3 f y| ≤ M) :
    |_root_.GD.N0110.d006121 f h - iteratedDeriv 1 f 0|
      ≤ M * h ^ 2 / 6 := by
  have hzero : 0 ∈ Icc (-h) h := by constructor <;> linarith
  have hnhds : Icc (-h) h ∈ 𝓝 (0 : ℝ) :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hf0 : ContDiffAt ℝ 3 f 0 := hf.contDiffAt hnhds
  have hplusSet : uIcc 0 h = Icc 0 h := by simp [uIcc_of_le hh.le]
  have hminusSet : uIcc 0 (-h) = Icc (-h) 0 := by
    rw [uIcc_comm]
    simp [uIcc_of_le (by linarith : -h ≤ 0)]
  have hplusSub : uIcc 0 h ⊆ Icc (-h) h := by
    rw [hplusSet]
    intro y hy
    constructor <;> linarith [hy.1, hy.2]
  have hminusSub : uIcc 0 (-h) ⊆ Icc (-h) h := by
    rw [hminusSet]
    exact Icc_subset_Icc_right (by linarith)
  have hp0 :=
    _root_.GD.N0112.d006170 f 2 h M (ne_of_gt hh)
      (hf.mono hplusSub)
      (fun y hy => hbound y (hplusSub (Ioo_subset_Icc_self hy)))
  have hm0 :=
    _root_.GD.N0112.d006170 f 2 (-h) M (by linarith)
      (hf.mono hminusSub)
      (fun y hy => hbound y (hminusSub (Ioo_subset_Icc_self hy)))
  have hp :
      |f h - _root_.GD.N0110.d006124 (f 0) (iteratedDeriv 1 f 0)
        (iteratedDeriv 2 f 0) h| ≤ M * h ^ 3 / 6 := by
    rw [← _root_.GD.N0112.d006171 f (uIcc 0 h) h
      (by rw [hplusSet]; exact uniqueDiffOn_Icc hh)
      left_mem_uIcc (hf0.of_le (by norm_num))]
    simpa [abs_of_pos hh, Nat.factorial] using hp0
  have hm :
      |f (-h) - _root_.GD.N0110.d006124 (f 0) (iteratedDeriv 1 f 0)
        (iteratedDeriv 2 f 0) (-h)| ≤ M * h ^ 3 / 6 := by
    rw [← _root_.GD.N0112.d006171 f (uIcc 0 (-h)) (-h)
      (by rw [hminusSet]; exact uniqueDiffOn_Icc (by linarith))
      left_mem_uIcc (hf0.of_le (by norm_num))]
    simpa [abs_of_pos hh, Nat.factorial] using hm0
  exact _root_.GD.N0110.d006127 f h (f 0) (iteratedDeriv 1 f 0)
    (iteratedDeriv 2 f 0) M hh hp hm




theorem d006175
    (f : ℝ → ℝ) (h M : ℝ)
    (hh : 0 < h)
    (hf : ContDiffOn ℝ 4 f (Icc (-h) h))
    (hbound :
      ∀ y ∈ Icc (-h) h, |iteratedDeriv 4 f y| ≤ M) :
    |_root_.GD.N0110.d006122 f h - iteratedDeriv 2 f 0|
      ≤ M * h ^ 2 / 12 := by
  have hzero : 0 ∈ Icc (-h) h := by constructor <;> linarith
  have hnhds : Icc (-h) h ∈ 𝓝 (0 : ℝ) :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hf0 : ContDiffAt ℝ 4 f 0 := hf.contDiffAt hnhds
  have hplusSet : uIcc 0 h = Icc 0 h := by simp [uIcc_of_le hh.le]
  have hminusSet : uIcc 0 (-h) = Icc (-h) 0 := by
    rw [uIcc_comm]
    simp [uIcc_of_le (by linarith : -h ≤ 0)]
  have hplusSub : uIcc 0 h ⊆ Icc (-h) h := by
    rw [hplusSet]
    intro y hy
    constructor <;> linarith [hy.1, hy.2]
  have hminusSub : uIcc 0 (-h) ⊆ Icc (-h) h := by
    rw [hminusSet]
    exact Icc_subset_Icc_right (by linarith)
  have hp0 :=
    _root_.GD.N0112.d006170 f 3 h M (ne_of_gt hh)
      (hf.mono hplusSub)
      (fun y hy => hbound y (hplusSub (Ioo_subset_Icc_self hy)))
  have hm0 :=
    _root_.GD.N0112.d006170 f 3 (-h) M (by linarith)
      (hf.mono hminusSub)
      (fun y hy => hbound y (hminusSub (Ioo_subset_Icc_self hy)))
  have hp :
      |f h - _root_.GD.N0110.d006125 (f 0) (iteratedDeriv 1 f 0)
        (iteratedDeriv 2 f 0) (iteratedDeriv 3 f 0) h|
        ≤ M * h ^ 4 / 24 := by
    rw [← _root_.GD.N0112.d006172 f (uIcc 0 h) h
      (by rw [hplusSet]; exact uniqueDiffOn_Icc hh)
      left_mem_uIcc (hf0.of_le (by norm_num))]
    simpa [abs_of_pos hh, Nat.factorial] using hp0
  have hm :
      |f (-h) - _root_.GD.N0110.d006125 (f 0) (iteratedDeriv 1 f 0)
        (iteratedDeriv 2 f 0) (iteratedDeriv 3 f 0) (-h)|
        ≤ M * h ^ 4 / 24 := by
    rw [← _root_.GD.N0112.d006172 f (uIcc 0 (-h)) (-h)
      (by rw [hminusSet]; exact uniqueDiffOn_Icc (by linarith))
      left_mem_uIcc (hf0.of_le (by norm_num))]
    simpa [abs_of_pos hh, Nat.factorial] using hm0
  exact _root_.GD.N0110.d006128 f h (f 0) (iteratedDeriv 1 f 0)
    (iteratedDeriv 2 f 0) (iteratedDeriv 3 f 0) M hh rfl hp hm





theorem d006176
    (f : ℝ → ℝ) (h M : ℝ)
    (hh : 0 < h)
    (hf : ContDiffOn ℝ 5 f (Icc (-2 * h) (2 * h)))
    (hbound :
      ∀ y ∈ Icc (-2 * h) (2 * h),
        |iteratedDeriv 5 f y| ≤ M) :
    |_root_.GD.N0110.d006123 f h - iteratedDeriv 3 f 0|
      ≤ (17 / 60 : ℝ) * M * h ^ 2 := by
  have hnhds : Icc (-2 * h) (2 * h) ∈ 𝓝 (0 : ℝ) :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hf0 : ContDiffAt ℝ 5 f 0 := hf.contDiffAt hnhds
  have hsub :
      ∀ x ∈ ({h, -h, 2 * h, -2 * h} : Set ℝ),
        uIcc 0 x ⊆ Icc (-2 * h) (2 * h) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals
      intro y hy
      simp only [mem_uIcc] at hy
      constructor <;> rcases hy with hy | hy <;> linarith [hy.1, hy.2]
  have remainder (x : ℝ)
      (hx : x ∈ ({h, -h, 2 * h, -2 * h} : Set ℝ))
      (hx0 : x ≠ 0) :
      |f x - _root_.GD.N0110.d006126 (f 0) (iteratedDeriv 1 f 0)
        (iteratedDeriv 2 f 0) (iteratedDeriv 3 f 0)
        (iteratedDeriv 4 f 0) x|
        ≤ M * |x| ^ 5 / 120 := by
    have hs := hsub x hx
    have hr :=
      _root_.GD.N0112.d006170 f 4 x M hx0
        (hf.mono hs)
        (fun y hy => hbound y (hs (Ioo_subset_Icc_self hy)))
    rw [← _root_.GD.N0112.d006173 f (uIcc 0 x) x
      (uniqueDiffOn_Icc (min_lt_max.mpr hx0.symm))
      left_mem_uIcc (hf0.of_le (by norm_num))]
    exact hr
  have hp1 := remainder h (by simp) (ne_of_gt hh)
  have hm1 := remainder (-h) (by simp) (by linarith)
  have hp2 := remainder (2 * h) (by simp) (by positivity)
  have hm2 := remainder (-2 * h) (by simp) (by positivity)
  apply _root_.GD.N0110.d006129 f h (f 0) (iteratedDeriv 1 f 0)
    (iteratedDeriv 2 f 0) (iteratedDeriv 3 f 0)
    (iteratedDeriv 4 f 0) M hh
  · simpa [abs_of_pos hh, Nat.factorial] using hp1
  · simpa [abs_of_pos hh, Nat.factorial] using hm1
  · simpa [abs_of_pos hh, Nat.factorial] using hp2
  · simpa [abs_of_pos hh, Nat.factorial] using hm2

end GD.N0112
