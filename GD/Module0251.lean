import GD.Module0232






















open scoped BigOperators

namespace GD.N0232.N0719.N0951

noncomputable section


def d003578 (k : ℕ) : ℝ := 3 / (4 * k)


def d003579 (k : ℕ) : ℝ := 5 / (4 * k)


def d003580 {k : ℕ} (p : Fin k → ℝ) : Prop :=
  ∀ i, _root_.GD.N0232.N0719.N0951.d003578 k ≤ p i ∧ p i ≤ _root_.GD.N0232.N0719.N0951.d003579 k


def d003581 {k : ℕ} (α : Fin k → ℝ) : Prop :=
  (∀ i, 0 ≤ α i) ∧ ∑ i, α i = 1

theorem d003582
    {k : ℕ} {α : Fin k → ℝ} :
    _root_.GD.N0232.N0719.N0951.d003581 α ↔ α ∈ stdSimplex ℝ (Fin k) := by
  rfl

theorem d003583 (k : ℕ) :
    IsCompact {α : Fin k → ℝ | _root_.GD.N0232.N0719.N0951.d003581 α} := by
  change IsCompact (stdSimplex ℝ (Fin k))
  exact isCompact_stdSimplex ℝ (Fin k)

theorem d003584 {k : ℕ} (hk : 0 < k) :
    Set.Nonempty {α : Fin k → ℝ | _root_.GD.N0232.N0719.N0951.d003581 α} := by
  let i : Fin k := ⟨0, hk⟩
  exact ⟨Pi.single i 1, by
    exact (_root_.GD.N0232.N0719.N0951.d003582).2
      (single_mem_stdSimplex ℝ i)⟩


def d003585 {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (p : Fin k → ℝ) : ℝ :=
  ∑ j, p (triangle j)


def d003586 {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (p : Fin k → ℝ) (j : Fin 3) : ℝ :=
  p (triangle j) / _root_.GD.N0232.N0719.N0951.d003585 triangle p



def d003587 {k : ℕ} (α p : Fin k → ℝ) : ℝ :=
  ∑ i, α i / p i

theorem d003588 {k : ℕ} (hk : 0 < k) :
    0 < _root_.GD.N0232.N0719.N0951.d003578 k := by
  unfold _root_.GD.N0232.N0719.N0951.d003578
  positivity

theorem d003589 {k : ℕ} (hk : 0 < k) :
    0 < _root_.GD.N0232.N0719.N0951.d003579 k := by
  unfold _root_.GD.N0232.N0719.N0951.d003579
  positivity

theorem d003590
    {k : ℕ} (hk : 0 < k) {p : Fin k → ℝ}
    (hp : _root_.GD.N0232.N0719.N0951.d003580 p) (i : Fin k) :
    0 < p i :=
  lt_of_lt_of_le (_root_.GD.N0232.N0719.N0951.d003588 hk) (hp i).1

theorem d003591
    {k : ℕ} (hk : 0 < k) (triangle : Fin 3 ↪ Fin k)
    {p : Fin k → ℝ} (hp : _root_.GD.N0232.N0719.N0951.d003580 p) :
    9 / (4 * (k : ℝ)) ≤ _root_.GD.N0232.N0719.N0951.d003585 triangle p := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  calc
    9 / (4 * (k : ℝ)) =
        _root_.GD.N0232.N0719.N0951.d003578 k + _root_.GD.N0232.N0719.N0951.d003578 k + _root_.GD.N0232.N0719.N0951.d003578 k := by
          unfold _root_.GD.N0232.N0719.N0951.d003578
          field_simp [hkR]
          ring
    _ ≤ p (triangle 0) + p (triangle 1) + p (triangle 2) :=
      add_le_add (add_le_add (hp (triangle 0)).1 (hp (triangle 1)).1)
        (hp (triangle 2)).1
    _ = _root_.GD.N0232.N0719.N0951.d003585 triangle p := by
      simp [_root_.GD.N0232.N0719.N0951.d003585, Fin.sum_univ_succ, Fin.sum_univ_two]
      ring

theorem d003592
    {k : ℕ} (hk : 0 < k) (triangle : Fin 3 ↪ Fin k)
    {p : Fin k → ℝ} (hp : _root_.GD.N0232.N0719.N0951.d003580 p) :
    _root_.GD.N0232.N0719.N0951.d003585 triangle p ≤ 15 / (4 * (k : ℝ)) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  calc
    _root_.GD.N0232.N0719.N0951.d003585 triangle p =
        p (triangle 0) + p (triangle 1) + p (triangle 2) := by
          simp [_root_.GD.N0232.N0719.N0951.d003585, Fin.sum_univ_succ, Fin.sum_univ_two]
          ring
    _ ≤ _root_.GD.N0232.N0719.N0951.d003579 k + _root_.GD.N0232.N0719.N0951.d003579 k + _root_.GD.N0232.N0719.N0951.d003579 k :=
      add_le_add (add_le_add (hp (triangle 0)).2 (hp (triangle 1)).2)
        (hp (triangle 2)).2
    _ = 15 / (4 * (k : ℝ)) := by
      unfold _root_.GD.N0232.N0719.N0951.d003579
      field_simp [hkR]
      ring

theorem d003593
    {k : ℕ} (hk : 0 < k) (triangle : Fin 3 ↪ Fin k)
    {p : Fin k → ℝ} (hp : _root_.GD.N0232.N0719.N0951.d003580 p) :
    0 < _root_.GD.N0232.N0719.N0951.d003585 triangle p := by
  have h := _root_.GD.N0232.N0719.N0951.d003591 hk triangle hp
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  exact lt_of_lt_of_le (by positivity : 0 < 9 / (4 * (k : ℝ))) h

theorem d003594
    {k : ℕ} (hk : 0 < k) (triangle : Fin 3 ↪ Fin k)
    {p : Fin k → ℝ} (hp : _root_.GD.N0232.N0719.N0951.d003580 p) (j : Fin 3) :
    1 / 5 ≤ _root_.GD.N0232.N0719.N0951.d003586 triangle p j := by
  have hpj := (hp (triangle j)).1
  have hr := _root_.GD.N0232.N0719.N0951.d003592 hk triangle hp
  have hrpos := _root_.GD.N0232.N0719.N0951.d003593 hk triangle hp
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  unfold _root_.GD.N0232.N0719.N0951.d003586
  apply (le_div_iff₀ hrpos).2
  calc
    (1 / 5) * _root_.GD.N0232.N0719.N0951.d003585 triangle p ≤
        (1 / 5) * (15 / (4 * (k : ℝ))) :=
      mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = _root_.GD.N0232.N0719.N0951.d003578 k := by
      unfold _root_.GD.N0232.N0719.N0951.d003578
      field_simp [hkR]
      ring
    _ ≤ p (triangle j) := hpj

theorem d003595
    {k : ℕ} (hk : 0 < k) (triangle : Fin 3 ↪ Fin k)
    {p : Fin k → ℝ} (hp : _root_.GD.N0232.N0719.N0951.d003580 p) (j : Fin 3) :
    _root_.GD.N0232.N0719.N0951.d003586 triangle p j ≤ 5 / 9 := by
  have hpj := (hp (triangle j)).2
  have hr := _root_.GD.N0232.N0719.N0951.d003591 hk triangle hp
  have hrpos := _root_.GD.N0232.N0719.N0951.d003593 hk triangle hp
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  unfold _root_.GD.N0232.N0719.N0951.d003586
  apply (div_le_iff₀ hrpos).2
  calc
    p (triangle j) ≤ _root_.GD.N0232.N0719.N0951.d003579 k := hpj
    _ = (5 / 9) * (9 / (4 * (k : ℝ))) := by
      unfold _root_.GD.N0232.N0719.N0951.d003579
      ring
    _ ≤ (5 / 9) * _root_.GD.N0232.N0719.N0951.d003585 triangle p :=
      mul_le_mul_of_nonneg_left hr (by norm_num)

theorem d003596
    {k : ℕ} (hk : 0 < k) (triangle : Fin 3 ↪ Fin k)
    {p : Fin k → ℝ} (hp : _root_.GD.N0232.N0719.N0951.d003580 p) (j : Fin 3) :
    0 < _root_.GD.N0232.N0719.N0951.d003586 triangle p j :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 5)
    (_root_.GD.N0232.N0719.N0951.d003594 hk triangle hp j)

theorem d003597
    {k : ℕ} (hk : 0 < k) (triangle : Fin 3 ↪ Fin k)
    {p : Fin k → ℝ} (hp : _root_.GD.N0232.N0719.N0951.d003580 p) :
    ∑ j, _root_.GD.N0232.N0719.N0951.d003586 triangle p j = 1 := by
  unfold _root_.GD.N0232.N0719.N0951.d003586 _root_.GD.N0232.N0719.N0951.d003585
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (_root_.GD.N0232.N0719.N0951.d003593 hk triangle hp))

theorem d003598
    {k : ℕ} (hk : 0 < k) {p : Fin k → ℝ}
    (hp : _root_.GD.N0232.N0719.N0951.d003580 p) (i : Fin k) :
    4 * (k : ℝ) / 5 ≤ 1 / p i := by
  have hpi := (hp i).2
  have hpipos := _root_.GD.N0232.N0719.N0951.d003590 hk hp i
  have hkRpos : 0 < (k : ℝ) := by exact_mod_cast hk
  apply (le_div_iff₀ hpipos).2
  calc
    (4 * (k : ℝ) / 5) * p i ≤
        (4 * (k : ℝ) / 5) * _root_.GD.N0232.N0719.N0951.d003579 k :=
      mul_le_mul_of_nonneg_left hpi (by positivity)
    _ = 1 := by
      unfold _root_.GD.N0232.N0719.N0951.d003579
      field_simp [ne_of_gt hkRpos]

theorem d003599
    {k : ℕ} (hk : 0 < k) {p : Fin k → ℝ}
    (hp : _root_.GD.N0232.N0719.N0951.d003580 p) (i : Fin k) :
    1 / p i ≤ 4 * (k : ℝ) / 3 := by
  have hpi := (hp i).1
  have hpipos := _root_.GD.N0232.N0719.N0951.d003590 hk hp i
  have hkRpos : 0 < (k : ℝ) := by exact_mod_cast hk
  apply (div_le_iff₀ hpipos).2
  calc
    1 = (4 * (k : ℝ) / 3) * _root_.GD.N0232.N0719.N0951.d003578 k := by
      unfold _root_.GD.N0232.N0719.N0951.d003578
      field_simp [ne_of_gt hkRpos]
    _ ≤ (4 * (k : ℝ) / 3) * p i :=
      mul_le_mul_of_nonneg_left hpi (by positivity)

theorem d003600
    {k : ℕ} (hk : 0 < k) {α p : Fin k → ℝ}
    (hα : _root_.GD.N0232.N0719.N0951.d003581 α) (hp : _root_.GD.N0232.N0719.N0951.d003580 p) :
    4 * (k : ℝ) / 5 ≤ _root_.GD.N0232.N0719.N0951.d003587 α p := by
  have hterm : ∀ i : Fin k,
      α i * (4 * (k : ℝ) / 5) ≤ α i * (1 / p i) := by
    intro i
    exact mul_le_mul_of_nonneg_left
      (_root_.GD.N0232.N0719.N0951.d003598 hk hp i) (hα.1 i)
  calc
    4 * (k : ℝ) / 5 =
        ∑ i, α i * (4 * (k : ℝ) / 5) := by
          rw [← Finset.sum_mul, hα.2, one_mul]
    _ ≤ ∑ i, α i * (1 / p i) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = _root_.GD.N0232.N0719.N0951.d003587 α p := by
      simp only [_root_.GD.N0232.N0719.N0951.d003587, div_eq_mul_inv, one_mul]

theorem d003601
    {k : ℕ} (hk : 0 < k) {α p : Fin k → ℝ}
    (hα : _root_.GD.N0232.N0719.N0951.d003581 α) (hp : _root_.GD.N0232.N0719.N0951.d003580 p) :
    _root_.GD.N0232.N0719.N0951.d003587 α p ≤ 4 * (k : ℝ) / 3 := by
  have hterm : ∀ i : Fin k,
      α i * (1 / p i) ≤ α i * (4 * (k : ℝ) / 3) := by
    intro i
    exact mul_le_mul_of_nonneg_left
      (_root_.GD.N0232.N0719.N0951.d003599 hk hp i) (hα.1 i)
  calc
    _root_.GD.N0232.N0719.N0951.d003587 α p =
        ∑ i, α i * (1 / p i) := by
          simp only [_root_.GD.N0232.N0719.N0951.d003587, div_eq_mul_inv, one_mul]
    _ ≤ ∑ i, α i * (4 * (k : ℝ) / 3) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = 4 * (k : ℝ) / 3 := by
      rw [← Finset.sum_mul, hα.2, one_mul]

theorem d003602
    {k : ℕ} (hk : 0 < k) {α p : Fin k → ℝ}
    (hα : _root_.GD.N0232.N0719.N0951.d003581 α) (hp : _root_.GD.N0232.N0719.N0951.d003580 p) :
    0 < _root_.GD.N0232.N0719.N0951.d003587 α p := by
  have h := _root_.GD.N0232.N0719.N0951.d003600 hk hα hp
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  exact lt_of_lt_of_le (by positivity : 0 < 4 * (k : ℝ) / 5) h



def d003603 {k : ℕ} (a v : Fin k → ℝ) (i : Fin k) : ℝ :=
  (a i / v i) / ∑ j, a j / v j

theorem d003604
    {k : ℕ} (hk : 0 < k) {a v : Fin k → ℝ}
    (ha : ∀ i, 0 < a i) (hv : ∀ i, 0 < v i) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0951.d003603 a v i := by
  unfold _root_.GD.N0232.N0719.N0951.d003603
  have hsum : 0 < ∑ j, a j / v j := by
    exact Finset.sum_pos (fun j _ => div_pos (ha j) (hv j))
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  exact div_pos (div_pos (ha i) (hv i)) hsum

theorem d003605
    {k : ℕ} (hk : 0 < k) {a v : Fin k → ℝ}
    (ha : ∀ i, 0 < a i) (hv : ∀ i, 0 < v i) :
    ∑ i, _root_.GD.N0232.N0719.N0951.d003603 a v i = 1 := by
  unfold _root_.GD.N0232.N0719.N0951.d003603
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (Finset.sum_pos
    (fun j _ => div_pos (ha j) (hv j))
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩))

theorem d003606
    {k : ℕ} (hk : 0 < k) {a v : Fin k → ℝ}
    (ha : ∀ i, 0 < a i) (hv : ∀ i, 0 < v i) :
    _root_.GD.N0232.N0719.N0951.d003581 (_root_.GD.N0232.N0719.N0951.d003603 a v) := by
  constructor
  · intro i
    exact (_root_.GD.N0232.N0719.N0951.d003604 hk ha hv i).le
  · exact _root_.GD.N0232.N0719.N0951.d003605 hk ha hv

theorem d003607
    {k : ℕ} (hk : 0 < k) {a v : Fin k → ℝ}
    (ha : ∀ i, 0 < a i) (hv : ∀ i, 0 < v i)
    {c : ℝ} (hc : 0 < c) :
    _root_.GD.N0232.N0719.N0951.d003603 a (fun i => c * v i) = _root_.GD.N0232.N0719.N0951.d003603 a v := by
  funext i
  unfold _root_.GD.N0232.N0719.N0951.d003603
  have hcne : c ≠ 0 := ne_of_gt hc
  have hden : ∑ j, a j / v j ≠ 0 := ne_of_gt (Finset.sum_pos
    (fun j _ => div_pos (ha j) (hv j))
    ⟨⟨0, hk⟩, Finset.mem_univ _⟩)
  have hterm : ∀ j : Fin k,
      a j / (c * v j) = c⁻¹ * (a j / v j) := by
    intro j
    field_simp [hcne, ne_of_gt (hv j)]
  simp_rw [hterm, ← Finset.mul_sum]
  field_simp [hcne, hden]

end

end GD.N0232.N0719.N0951
