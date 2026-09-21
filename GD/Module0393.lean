import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Filter Topology

namespace GD.N0035


def d006053 (j : ℕ) : ℚ := (1 / 2 : ℚ) ^ j

theorem d006054 (j : ℕ) : 0 < _root_.GD.N0035.d006053 j := by
  unfold _root_.GD.N0035.d006053
  positivity

theorem d006055 (j : ℕ) : 2 * _root_.GD.N0035.d006053 (j + 1) = _root_.GD.N0035.d006053 j := by
  simp [_root_.GD.N0035.d006053, pow_succ]
  ring


def d006056 (gap : ℕ → ℚ)
    (h : ∀ j : ℕ, ∃ n : ℕ, gap n < _root_.GD.N0035.d006053 (j + 1) ^ 2) (j : ℕ) : ℕ :=
  Nat.find (h j)

theorem d006057 (gap : ℕ → ℚ)
    (h : ∀ j : ℕ, ∃ n : ℕ, gap n < _root_.GD.N0035.d006053 (j + 1) ^ 2) (j : ℕ) :
    gap (_root_.GD.N0035.d006056 gap h j) < _root_.GD.N0035.d006053 (j + 1) ^ 2 :=
  Nat.find_spec (h j)



theorem d006058 (gap : ℕ → ℚ)
    (hgap : Tendsto (fun n => (gap n : ℝ)) atTop (𝓝 0)) :
    ∀ j : ℕ, ∃ n : ℕ, gap n < _root_.GD.N0035.d006053 (j + 1) ^ 2 := by
  intro j
  have hpos : (0 : ℝ) < ((_root_.GD.N0035.d006053 (j + 1) ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast sq_pos_of_pos (_root_.GD.N0035.d006054 (j + 1))
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hgap).2 _ hpos).exists
  exact ⟨n, by exact_mod_cast hn⟩

variable {H : Type*} [NormedAddCommGroup H]



theorem d006059
    (p : H) (finite : ℕ → H) (approx : ℕ → ℕ → H) (gap : ℕ → ℚ)
    (hsearch : ∀ j : ℕ, ∃ n : ℕ, gap n < _root_.GD.N0035.d006053 (j + 1) ^ 2)
    (htax : ∀ n, ‖p - finite n‖ ^ 2 ≤ (gap n : ℝ))
    (happrox : ∀ n j, ‖approx n j - finite n‖ ≤ (_root_.GD.N0035.d006053 j : ℝ)) (j : ℕ) :
    ‖approx (_root_.GD.N0035.d006056 gap hsearch j) (j + 1) - p‖ ≤ (_root_.GD.N0035.d006053 j : ℝ) := by
  let N := _root_.GD.N0035.d006056 gap hsearch j
  have hgap : (gap N : ℝ) < (_root_.GD.N0035.d006053 (j + 1) : ℝ) ^ 2 := by
    exact_mod_cast _root_.GD.N0035.d006057 gap hsearch j
  have htaxN := htax N
  have hδ : (0 : ℝ) < (_root_.GD.N0035.d006053 (j + 1) : ℝ) := by
    exact_mod_cast _root_.GD.N0035.d006054 (j + 1)
  have hdist : ‖finite N - p‖ ≤ (_root_.GD.N0035.d006053 (j + 1) : ℝ) := by
    rw [norm_sub_rev]
    nlinarith [norm_nonneg (p - finite N)]
  have htriangle := norm_sub_le_norm_sub_add_norm_sub (approx N (j + 1)) (finite N) p
  have hround := happrox N (j + 1)
  have htwo : 2 * (_root_.GD.N0035.d006053 (j + 1) : ℝ) = (_root_.GD.N0035.d006053 j : ℝ) := by
    exact_mod_cast _root_.GD.N0035.d006055 j
  change ‖approx N (j + 1) - p‖ ≤ (_root_.GD.N0035.d006053 j : ℝ)
  linarith



theorem d006060
    (p : H) (finite : ℕ → H) (upper lower : ℕ → ℚ)
    (htax : ∀ n, ‖p - finite n‖ ^ 2 + ‖finite n‖ ^ 2 ≤ ‖p‖ ^ 2)
    (hu : ∀ n, ‖p‖ ^ 2 ≤ (upper n : ℝ))
    (hl : ∀ n, (lower n : ℝ) ≤ ‖finite n‖ ^ 2) (n : ℕ) :
    ‖p - finite n‖ ^ 2 ≤ ((upper n - lower n : ℚ) : ℝ) := by
  push_cast
  linarith [htax n, hu n, hl n]



theorem d006061
    (p : H) (finite : ℕ → H) (approx : ℕ → ℕ → H) (upper lower : ℕ → ℚ)
    (htax : ∀ n, ‖p - finite n‖ ^ 2 + ‖finite n‖ ^ 2 ≤ ‖p‖ ^ 2)
    (hu : ∀ n, ‖p‖ ^ 2 ≤ (upper n : ℝ))
    (hl : ∀ n, (lower n : ℝ) ≤ ‖finite n‖ ^ 2)
    (hlim : Tendsto (fun n => ((upper n - lower n : ℚ) : ℝ)) atTop (𝓝 0))
    (happrox : ∀ n j, ‖approx n j - finite n‖ ≤ (_root_.GD.N0035.d006053 j : ℝ)) (j : ℕ) :
    ‖approx (_root_.GD.N0035.d006056 (fun n => upper n - lower n)
      (_root_.GD.N0035.d006058 _ hlim) j) (j + 1) - p‖ ≤ (_root_.GD.N0035.d006053 j : ℝ) :=
  _root_.GD.N0035.d006059 p finite approx _
    (_root_.GD.N0035.d006058 _ hlim)
    (_root_.GD.N0035.d006060 p finite upper lower htax hu hl) happrox j



theorem d006062 (p q : H) (a δ : ℚ)
    (hpq : ‖q - p‖ ≤ (δ : ℝ))
    (hnorm : ‖q‖ ≤ (a : ℝ) + (δ : ℝ)) :
    ‖p‖ ^ 2 ≤ (((a + 2 * δ) ^ 2 : ℚ) : ℝ) := by
  have htri := norm_le_insert' p q
  have hnormp : ‖p‖ ≤ (a : ℝ) + 2 * (δ : ℝ) := by
    rw [norm_sub_rev] at hpq
    linarith
  push_cast
  exact pow_le_pow_left₀ (norm_nonneg p) hnormp 2


theorem d006063 (p q : H) (a δ : ℚ)
    (hpq : ‖q - p‖ ≤ (δ : ℝ))
    (hlo : ‖q‖ ≤ (a : ℝ) + (δ : ℝ))
    (hhi : (a : ℝ) ≤ ‖q‖ + (δ : ℝ)) :
    0 ≤ (((a + 2 * δ) ^ 2 : ℚ) : ℝ) - ‖p‖ ^ 2 ∧
    (((a + 2 * δ) ^ 2 : ℚ) : ℝ) - ‖p‖ ^ 2 ≤
      8 * ‖p‖ * (δ : ℝ) + 16 * (δ : ℝ) ^ 2 := by
  refine ⟨sub_nonneg.mpr (_root_.GD.N0035.d006062 p q a δ hpq hlo), ?_⟩
  have hδ : (0 : ℝ) ≤ (δ : ℝ) := (norm_nonneg _).trans hpq
  have hq : ‖q‖ ≤ ‖p‖ + (δ : ℝ) :=
    (norm_le_insert' q p).trans (add_le_add le_rfl hpq)
  have hu : (a : ℝ) + 2 * (δ : ℝ) ≤ ‖p‖ + 4 * (δ : ℝ) := by linarith
  have hl : 0 ≤ (a : ℝ) + 2 * (δ : ℝ) := by linarith [norm_nonneg q]
  have hs := pow_le_pow_left₀ hl hu 2
  push_cast
  nlinarith

theorem d006064 :
    Tendsto (fun j => (_root_.GD.N0035.d006053 j : ℝ)) atTop (𝓝 0) := by
  simpa [_root_.GD.N0035.d006053] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1))




theorem d006065 (p : H) (q : ℕ → H) (a : ℕ → ℚ)
    (hpq : ∀ j, ‖q j - p‖ ≤ (_root_.GD.N0035.d006053 j : ℝ))
    (hlo : ∀ j, ‖q j‖ ≤ (a j : ℝ) + (_root_.GD.N0035.d006053 j : ℝ))
    (hhi : ∀ j, (a j : ℝ) ≤ ‖q j‖ + (_root_.GD.N0035.d006053 j : ℝ)) :
    Tendsto (fun j => (((a j + 2 * _root_.GD.N0035.d006053 j) ^ 2 : ℚ) : ℝ)) atTop (𝓝 (‖p‖ ^ 2)) := by
  have hb := fun j => _root_.GD.N0035.d006063 p (q j) (a j) (_root_.GD.N0035.d006053 j)
    (hpq j) (hlo j) (hhi j)
  have hzero : Tendsto (fun j => 8 * ‖p‖ * (_root_.GD.N0035.d006053 j : ℝ) +
      16 * (_root_.GD.N0035.d006053 j : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa using (_root_.GD.N0035.d006064.const_mul (8 * ‖p‖)).add
      ((_root_.GD.N0035.d006064.pow 2).const_mul 16)
  have hgap := squeeze_zero (fun j => (hb j).1) (fun j => (hb j).2) hzero
  have hsum := hgap.add_const (‖p‖ ^ 2)
  change Tendsto (fun j => (((a j + 2 * _root_.GD.N0035.d006053 j) ^ 2 : ℚ) : ℝ) -
    ‖p‖ ^ 2 + ‖p‖ ^ 2) atTop (𝓝 (0 + ‖p‖ ^ 2)) at hsum
  simpa only [sub_add_cancel, zero_add] using hsum

end GD.N0035

#print axioms _root_.GD.N0035.d006057
#print axioms _root_.GD.N0035.d006058
#print axioms _root_.GD.N0035.d006059
#print axioms _root_.GD.N0035.d006060
#print axioms _root_.GD.N0035.d006061
#print axioms _root_.GD.N0035.d006062

#print axioms _root_.GD.N0035.d006063
#print axioms _root_.GD.N0035.d006065
#print axioms _root_.GD.N0035.d006054
#print axioms _root_.GD.N0035.d006055
#print axioms _root_.GD.N0035.d006064

#eval (List.range 4).map (_root_.GD.N0035.d006056
  _root_.GD.N0035.d006053 (_root_.GD.N0035.d006058
    _root_.GD.N0035.d006053 _root_.GD.N0035.d006064))
