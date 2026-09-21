import GD.Module0251
import GD.Module0266





















open scoped BigOperators

namespace GD.N0232.N0719.N0854

noncomputable section


def d003821 (k : ℕ) : Fin k → ℝ :=
  fun _ => (1 : ℝ) / (k : ℝ)





def d003822 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) : Fin k → ℝ :=
  fun i =>
    (1 : ℝ) / (k : ℝ) +
      (if i = triangle 0 then (1 : ℝ) / (5 * (k : ℝ)) else 0) -
      (if i = triangle 1 then (1 : ℝ) / (5 * (k : ℝ)) else 0)

theorem d003823 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    triangle 0 ≠ triangle 1 := by
  intro h
  have hv := congrArg Fin.val (triangle.injective h)
  norm_num at hv

theorem d003824 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    triangle 0 ≠ triangle 2 := by
  intro h
  have hv := congrArg Fin.val (triangle.injective h)
  norm_num at hv

theorem d003825 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    triangle 1 ≠ triangle 2 := by
  intro h
  have hv := congrArg Fin.val (triangle.injective h)
  norm_num at hv

theorem d003826
    {k : ℕ} (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N0854.d003822 triangle (triangle 0) =
      (6 : ℝ) / (5 * (k : ℝ)) := by
  have h01 := _root_.GD.N0232.N0719.N0854.d003823 triangle
  simp [_root_.GD.N0232.N0719.N0854.d003822, h01]
  ring

theorem d003827
    {k : ℕ} (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N0854.d003822 triangle (triangle 1) =
      (4 : ℝ) / (5 * (k : ℝ)) := by
  have h10 : triangle 1 ≠ triangle 0 :=
    (_root_.GD.N0232.N0719.N0854.d003823 triangle).symm
  simp [_root_.GD.N0232.N0719.N0854.d003822, h10]
  ring

theorem d003828
    {k : ℕ} (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N0854.d003822 triangle (triangle 2) =
      (1 : ℝ) / (k : ℝ) := by
  have h20 : triangle 2 ≠ triangle 0 :=
    (_root_.GD.N0232.N0719.N0854.d003824 triangle).symm
  have h21 : triangle 2 ≠ triangle 1 :=
    (_root_.GD.N0232.N0719.N0854.d003825 triangle).symm
  simp [_root_.GD.N0232.N0719.N0854.d003822, h20, h21]

theorem d003829 {k : ℕ} (hk : 0 < k) :
    ∑ i, _root_.GD.N0232.N0719.N0854.d003821 k i = 1 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp [_root_.GD.N0232.N0719.N0854.d003821, one_div, hkR]

theorem d003830 {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    ∑ i, _root_.GD.N0232.N0719.N0854.d003822 triangle i = 1 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold _root_.GD.N0232.N0719.N0854.d003822
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp [hkR]

theorem d003831 {k : ℕ} (hk : 0 < k) :
    _root_.GD.N0232.N0719.N0951.d003581 (_root_.GD.N0232.N0719.N0854.d003821 k) := by
  constructor
  · intro i
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    simp [_root_.GD.N0232.N0719.N0854.d003821, (one_div_pos.mpr hkR).le]
  · exact _root_.GD.N0232.N0719.N0854.d003829 hk

theorem d003832 {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N0951.d003581 (_root_.GD.N0232.N0719.N0854.d003822 triangle) := by
  constructor
  · intro i
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    by_cases h0 : i = triangle 0
    · subst i
      rw [_root_.GD.N0232.N0719.N0854.d003826]
      positivity
    · by_cases h1 : i = triangle 1
      · subst i
        rw [_root_.GD.N0232.N0719.N0854.d003827]
        positivity
      · simpa [_root_.GD.N0232.N0719.N0854.d003822, h0, h1] using
          (one_div_pos.mpr hkR).le
  · exact _root_.GD.N0232.N0719.N0854.d003830 hk triangle

theorem d003833 {k : ℕ} (hk : 0 < k) :
    _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0854.d003821 k) := by
  intro i
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  unfold _root_.GD.N0232.N0719.N0854.d003821 _root_.GD.N0232.N0719.N0951.d003578 _root_.GD.N0232.N0719.N0951.d003579
  constructor <;> field_simp [hkR.ne'] <;> nlinarith

theorem d003834 {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0854.d003822 triangle) := by
  intro i
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  unfold _root_.GD.N0232.N0719.N0854.d003822 _root_.GD.N0232.N0719.N0951.d003578 _root_.GD.N0232.N0719.N0951.d003579
  by_cases h0 : i = triangle 0
  · have h1 : i ≠ triangle 1 := by
      rw [h0]
      exact _root_.GD.N0232.N0719.N0854.d003823 triangle
    simp [h0, h1]
    constructor <;> field_simp [hkR.ne'] <;> nlinarith
  · by_cases h1 : i = triangle 1
    · simp [h0, h1]
      constructor <;> field_simp [hkR.ne'] <;> nlinarith
    · simp [h0, h1]
      constructor <;> field_simp [hkR.ne'] <;> nlinarith

theorem d003835
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0854.d003821 k) =
      (3 : ℝ) / (k : ℝ) := by
  simp [_root_.GD.N0232.N0719.N0951.d003585, _root_.GD.N0232.N0719.N0854.d003821,
    Fin.sum_univ_succ, Fin.sum_univ_two]
  ring

theorem d003836
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0854.d003822 triangle) =
      (3 : ℝ) / (k : ℝ) := by
  rw [show
      _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0854.d003822 triangle) =
        _root_.GD.N0232.N0719.N0854.d003822 triangle (triangle 0) +
          _root_.GD.N0232.N0719.N0854.d003822 triangle (triangle 1) +
          _root_.GD.N0232.N0719.N0854.d003822 triangle (triangle 2) by
      simp [_root_.GD.N0232.N0719.N0951.d003585,
        Fin.sum_univ_succ, Fin.sum_univ_two]
      ring]
  rw [_root_.GD.N0232.N0719.N0854.d003826, _root_.GD.N0232.N0719.N0854.d003827,
    _root_.GD.N0232.N0719.N0854.d003828]
  ring

theorem d003837
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (j : Fin 3) :
    _root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003821 k) j = 1 / 3 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold _root_.GD.N0232.N0719.N0951.d003586
  rw [_root_.GD.N0232.N0719.N0854.d003835 hk triangle]
  simp [_root_.GD.N0232.N0719.N0854.d003821]
  field_simp [hkR]

theorem d003838
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003822 triangle) 0 = 2 / 5 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold _root_.GD.N0232.N0719.N0951.d003586
  rw [_root_.GD.N0232.N0719.N0854.d003836 hk triangle,
    _root_.GD.N0232.N0719.N0854.d003826]
  field_simp [hkR]
  ring

theorem d003839
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003822 triangle) 1 = 4 / 15 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold _root_.GD.N0232.N0719.N0951.d003586
  rw [_root_.GD.N0232.N0719.N0854.d003836 hk triangle,
    _root_.GD.N0232.N0719.N0854.d003827]
  field_simp [hkR]
  ring

theorem d003840
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003822 triangle) 2 = 1 / 3 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold _root_.GD.N0232.N0719.N0951.d003586
  rw [_root_.GD.N0232.N0719.N0854.d003836 hk triangle,
    _root_.GD.N0232.N0719.N0854.d003828]
  field_simp [hkR]





theorem d003841
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w₁ w₂ w₃ : ℝ) :
    (1 / 375) * (w₁ ^ 2 + w₂ ^ 2 + w₃ ^ 2) ≤
      _root_.GD.N0232.N0719.N1016.d003608
        (_root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003821 k) 0)
        (_root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003821 k) 1)
        (_root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003821 k) 2)
        ((_root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003821 k) 0) * w₁)
        ((_root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003821 k) 1) * w₂)
        ((_root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003821 k) 2) * w₃) +
      _root_.GD.N0232.N0719.N1016.d003608
        (_root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003822 triangle) 0)
        (_root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003822 triangle) 1)
        (_root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003822 triangle) 2)
        ((_root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003822 triangle) 0) * w₁)
        ((_root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003822 triangle) 1) * w₂)
        ((_root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0854.d003822 triangle) 2) * w₃) := by
  rw [_root_.GD.N0232.N0719.N0854.d003837 hk triangle 0,
    _root_.GD.N0232.N0719.N0854.d003837 hk triangle 1,
    _root_.GD.N0232.N0719.N0854.d003837 hk triangle 2,
    _root_.GD.N0232.N0719.N0854.d003838 hk triangle,
    _root_.GD.N0232.N0719.N0854.d003839 hk triangle,
    _root_.GD.N0232.N0719.N0854.d003840 hk triangle]
  exact _root_.GD.N0232.N0719.N1021.d003818 w₁ w₂ w₃

end

end GD.N0232.N0719.N0854
