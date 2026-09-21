import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring







namespace GD.N0106.N0428.N0765.N1524

set_option autoImplicit false
set_option warningAsError true

open Set Polynomial Polynomial.Chebyshev

noncomputable section

def d005283 : Finset ℝ :=
  (Finset.range 14).image (fun k : ℕ => Real.cos ((2 * k + 1) * Real.pi / (2 * 14)))

theorem d005284 : _root_.GD.N0106.N0428.N0765.N1524.d005283.card = 14 := by
  classical
  rw [_root_.GD.N0106.N0428.N0765.N1524.d005283, Finset.card_image_of_injOn, Finset.card_range]
  exact (Finset.range 14).nodup_map_iff_injOn.mp (roots_T_real_nodup 14)

theorem d005285 {t : ℝ} (ht : t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005283) : t ∈ Icc (-1) 1 := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
  exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩


theorem d005286 (x : ℝ) :
    (8192 : ℝ) * ∏ t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005283, (x - t) = (T ℝ 14).eval x := by
  classical
  have hroots := roots_T_real 14
  simp only [Nat.cast_ofNat] at hroots
  have hcard : (T ℝ 14).roots.card = (T ℝ 14).natDegree := by
    rw [hroots]
    change _root_.GD.N0106.N0428.N0765.N1524.d005283.card = _
    rw [_root_.GD.N0106.N0428.N0765.N1524.d005284]
    norm_num
  have hp := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [hroots] at hp
  change C (T ℝ 14).leadingCoeff * (∏ t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005283, (X - C t)) = T ℝ 14 at hp
  have hlc : (T ℝ 14).leadingCoeff = (8192 : ℝ) := by norm_num [leadingCoeff_T]
  rw [hlc] at hp
  have heval := congrArg (fun p : ℝ[X] => p.eval x) hp
  simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X] using heval


theorem d005287 {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |∏ t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005283, (x - t)| ≤ (1 : ℝ) / 8192 := by
  have hb := abs_eval_T_real_le_one (14 : ℤ) (abs_le.mpr hx)
  have hi := congrArg abs (_root_.GD.N0106.N0428.N0765.N1524.d005286 x)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8192)] at hi
  linarith


def d005288 (c : ℝ) : Finset ℝ := _root_.GD.N0106.N0428.N0765.N1524.d005283.image (fun t => c + t / 14)

theorem d005289 (c : ℝ) : Function.Injective (fun t : ℝ => c + t / 14) := by
  intro x y h
  linarith

theorem d005290 (c : ℝ) : (_root_.GD.N0106.N0428.N0765.N1524.d005288 c).card = 14 := by
  classical
  rw [_root_.GD.N0106.N0428.N0765.N1524.d005288, Finset.card_image_of_injOn (_root_.GD.N0106.N0428.N0765.N1524.d005289 c).injOn,
    _root_.GD.N0106.N0428.N0765.N1524.d005284]


theorem d005291 {c x : ℝ} :
    x ∈ _root_.GD.N0106.N0428.N0765.N1524.d005288 c ↔ ∃ k : ℕ, k < 14 ∧
      x = c + Real.cos ((2 * k + 1) * Real.pi / (2 * 14)) / 14 := by
  classical
  simp only [_root_.GD.N0106.N0428.N0765.N1524.d005288, _root_.GD.N0106.N0428.N0765.N1524.d005283, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨t, ⟨k, hk, rfl⟩, h⟩
    exact ⟨k, hk, h.symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩

theorem d005292 (c : ℝ) {t : ℝ} (ht : t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005288 c) :
    t ∈ Icc (c - 1 / 14) (c + 1 / 14) := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
  have hb := _root_.GD.N0106.N0428.N0765.N1524.d005285 hz
  constructor <;> linarith [hb.1, hb.2]

theorem d005293 (c x : ℝ) :
    (∏ t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005288 c, (x - t)) =
      ((1 : ℝ) / 14) ^ 14 * ∏ t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005283, (14 * (x - c) - t) := by
  classical
  rw [_root_.GD.N0106.N0428.N0765.N1524.d005288, Finset.prod_image (_root_.GD.N0106.N0428.N0765.N1524.d005289 c).injOn]
  calc
    (∏ t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005283, (x - (c + t / 14))) =
        ∏ t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005283, ((1 : ℝ) / 14) * (14 * (x - c) - t) := by
      apply Finset.prod_congr rfl
      intro t _
      ring
    _ = ((1 : ℝ) / 14) ^ 14 * ∏ t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005283, (14 * (x - c) - t) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, _root_.GD.N0106.N0428.N0765.N1524.d005284]


theorem d005294 (c : ℝ) {x : ℝ}
    (hx : x ∈ Icc (c - 1 / 14) (c + 1 / 14)) :
    |∏ t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005288 c, (x - t)| ≤ ((1 : ℝ) / 14) ^ 14 / 8192 := by
  have hscaled : 14 * (x - c) ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  rw [_root_.GD.N0106.N0428.N0765.N1524.d005293, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ((1 : ℝ) / 14) ^ 14)]
  calc
    ((1 : ℝ) / 14) ^ 14 * |∏ t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005283, (14 * (x - c) - t)| ≤
        ((1 : ℝ) / 14) ^ 14 * ((1 : ℝ) / 8192) :=
      mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1524.d005287 hscaled) (by positivity)
    _ = ((1 : ℝ) / 14) ^ 14 / 8192 := by ring

end
end GD.N0106.N0428.N0765.N1524

#print axioms _root_.GD.N0106.N0428.N0765.N1524.d005284
#print axioms _root_.GD.N0106.N0428.N0765.N1524.d005286
#print axioms _root_.GD.N0106.N0428.N0765.N1524.d005287
#print axioms _root_.GD.N0106.N0428.N0765.N1524.d005290
#print axioms _root_.GD.N0106.N0428.N0765.N1524.d005291
#print axioms _root_.GD.N0106.N0428.N0765.N1524.d005294
