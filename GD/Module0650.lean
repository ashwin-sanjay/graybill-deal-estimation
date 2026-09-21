import GD.Module0642
import GD.Module0248
import GD.Module0649
import Mathlib.Probability.ConditionalProbability






















open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ProbabilityTheory

namespace GD.N0232.N0719.N0856

noncomputable section


def d009528 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k)
    (p : Fin k → ℝ) (w : Fin 3 → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1016.d003608
    (_root_.GD.N0232.N0719.N0951.d003586 triangle p 0)
    (_root_.GD.N0232.N0719.N0951.d003586 triangle p 1)
    (_root_.GD.N0232.N0719.N0951.d003586 triangle p 2)
    (_root_.GD.N0232.N0719.N0951.d003586 triangle p 0 * w 0)
    (_root_.GD.N0232.N0719.N0951.d003586 triangle p 1 * w 1)
    (_root_.GD.N0232.N0719.N0951.d003586 triangle p 2 * w 2)


def d009529 {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) (w : Fin 3 → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0856.d009528 triangle
    (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u) w


def d009530 {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) (w : Fin 3 → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0856.d009528 triangle
    (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) w




def d009531 {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) (w : Fin 3 → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w +
    _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w


def d009532 : Set (Fin 3 → ℝ) :=
  {w |
    (∀ j, 0 ≤ w j ∧ w j ≤ 1) ∧
      (w 0 = 1 ∨ w 1 = 1 ∨ w 2 = 1)}

theorem d009533 :
    _root_.GD.N0232.N0719.N0856.d009532 =
      Set.Icc (0 : Fin 3 → ℝ) 1 ∩
        ({w : Fin 3 → ℝ | w 0 = 1} ∪
          {w : Fin 3 → ℝ | w 1 = 1} ∪
          {w : Fin 3 → ℝ | w 2 = 1}) := by
  ext w
  simp only [_root_.GD.N0232.N0719.N0856.d009532, Set.mem_setOf_eq,
    Set.mem_inter_iff, Set.mem_Icc, Pi.zero_apply, Pi.one_apply,
    Set.mem_union, and_congr_right_iff]
  constructor
  · rintro ⟨hbox, hface⟩
    refine ⟨⟨fun j => (hbox j).1, fun j => (hbox j).2⟩, ?_⟩
    rcases hface with h0 | h1 | h2
    · exact Or.inl (Or.inl h0)
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h2
  · rintro ⟨⟨hlower, hupper⟩, hface⟩
    refine ⟨fun j => ⟨hlower j, hupper j⟩, ?_⟩
    rcases hface with (h0 | h1) | h2
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)

theorem d009534 :
    IsCompact _root_.GD.N0232.N0719.N0856.d009532 := by
  rw [_root_.GD.N0232.N0719.N0856.d009533]
  apply isCompact_Icc.inter_right
  exact
    ((isClosed_eq (continuous_apply 0) continuous_const).union
      (isClosed_eq (continuous_apply 1) continuous_const)).union
      (isClosed_eq (continuous_apply 2) continuous_const)

theorem d009535 :
    _root_.GD.N0232.N0719.N0856.d009532.Nonempty := by
  refine ⟨1, ?_⟩
  constructor
  · intro j
    simp
  · exact Or.inl rfl



def d009536 (k : ℕ) :
    Set (_root_.GD.N0232.N0719.N0857.d009377 k × (Fin 3 → ℝ)) :=
  _root_.GD.N0232.N0719.N0857.d009383 k ×ˢ _root_.GD.N0232.N0719.N0856.d009532

theorem d009537 (k : ℕ) :
    IsCompact (_root_.GD.N0232.N0719.N0856.d009536 k) :=
  (_root_.GD.N0232.N0719.N0857.d009384 k).prod
    _root_.GD.N0232.N0719.N0856.d009534

theorem d009538 (k : ℕ) :
    (_root_.GD.N0232.N0719.N0856.d009536 k).Nonempty := by
  obtain ⟨w, hw⟩ := _root_.GD.N0232.N0719.N0856.d009535
  exact
    ⟨(0, w),
      interior_subset
        (_root_.GD.N0232.N0719.N0857.d009385 k),
      hw⟩



theorem d009539
    {X : Type*} [TopologicalSpace X]
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (p : X → Fin k → ℝ)
    (hp_cont : ∀ i, Continuous (fun x => p x i))
    (hp_bal : ∀ x, _root_.GD.N0232.N0719.N0951.d003580 (p x))
    (j : Fin 3) :
    Continuous (fun x => _root_.GD.N0232.N0719.N0951.d003586 triangle (p x) j) := by
  have hmass :
      Continuous (fun x => _root_.GD.N0232.N0719.N0951.d003585 triangle (p x)) := by
    unfold _root_.GD.N0232.N0719.N0951.d003585
    exact continuous_finset_sum _ fun i _ => hp_cont (triangle i)
  unfold _root_.GD.N0232.N0719.N0951.d003586
  exact (hp_cont (triangle j)).div hmass
    (fun x => (_root_.GD.N0232.N0719.N0951.d003593 hk triangle (hp_bal x)).ne')



theorem d009540
    {X : Type*} [TopologicalSpace X]
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (p : X → Fin k → ℝ)
    (hp_cont : ∀ i, Continuous (fun x => p x i))
    (hp_bal : ∀ x, _root_.GD.N0232.N0719.N0951.d003580 (p x)) :
    Continuous
      (Function.uncurry
        (fun x w => _root_.GD.N0232.N0719.N0856.d009528 triangle (p x) w)) := by
  let q : Fin 3 → X → ℝ :=
    fun j x => _root_.GD.N0232.N0719.N0951.d003586 triangle (p x) j
  have hq : ∀ j, Continuous (q j) :=
    fun j => _root_.GD.N0232.N0719.N0856.d009539
      hk triangle p hp_cont hp_bal j
  have hqpos : ∀ x j, 0 < q j x :=
    fun x j => _root_.GD.N0232.N0719.N0951.d003596 hk triangle (hp_bal x) j
  have hw : ∀ j : Fin 3,
      Continuous (fun z : X × (Fin 3 → ℝ) => z.2 j) :=
    fun j => (continuous_apply j).comp continuous_snd
  have hqw : ∀ j : Fin 3,
      Continuous (fun z : X × (Fin 3 → ℝ) => q j z.1 * z.2 j) :=
    fun j => ((hq j).comp continuous_fst).mul (hw j)
  have hden : ∀ i j : Fin 3,
      Continuous (fun z : X × (Fin 3 → ℝ) => q i z.1 + q j z.1) :=
    fun i j => ((hq i).comp continuous_fst).add ((hq j).comp continuous_fst)
  have h01 : Continuous (fun z : X × (Fin 3 → ℝ) =>
      (q 0 z.1 * z.2 0 - q 1 z.1 * z.2 1) ^ 2 /
        (q 0 z.1 + q 1 z.1)) :=
    (((hqw 0).sub (hqw 1)).pow 2).div (hden 0 1)
      (fun z => (add_pos (hqpos z.1 0) (hqpos z.1 1)).ne')
  have h02 : Continuous (fun z : X × (Fin 3 → ℝ) =>
      (q 0 z.1 * z.2 0 - q 2 z.1 * z.2 2) ^ 2 /
        (q 0 z.1 + q 2 z.1)) :=
    (((hqw 0).sub (hqw 2)).pow 2).div (hden 0 2)
      (fun z => (add_pos (hqpos z.1 0) (hqpos z.1 2)).ne')
  have h12 : Continuous (fun z : X × (Fin 3 → ℝ) =>
      (q 1 z.1 * z.2 1 - q 2 z.1 * z.2 2) ^ 2 /
        (q 1 z.1 + q 2 z.1)) :=
    (((hqw 1).sub (hqw 2)).pow 2).div (hden 1 2)
      (fun z => (add_pos (hqpos z.1 1) (hqpos z.1 2)).ne')
  unfold Function.uncurry _root_.GD.N0232.N0719.N0856.d009528 _root_.GD.N0232.N0719.N1016.d003608
  exact (h01.add h02).add h12

theorem d009541
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    Continuous
      (Function.uncurry
        (_root_.GD.N0232.N0719.N0856.d009529 hk triangle)) := by
  exact _root_.GD.N0232.N0719.N0856.d009540
    hk triangle
    (fun u => _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u)
    (fun i => _root_.GD.N0232.N0719.N0857.d009390 hk
      (_root_.GD.N0232.N0719.N0854.d003821 k) i)
    (_root_.GD.N0232.N0719.N0857.d009397 hk)

theorem d009542
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    Continuous
      (Function.uncurry
        (_root_.GD.N0232.N0719.N0856.d009530 hk triangle)) := by
  exact _root_.GD.N0232.N0719.N0856.d009540
    hk triangle
    (fun u => _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u)
    (fun i => _root_.GD.N0232.N0719.N0857.d009390 hk
      (_root_.GD.N0232.N0719.N0854.d003822 triangle) i)
    (_root_.GD.N0232.N0719.N0857.d009398 hk triangle)

theorem d009543
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    Continuous
      (Function.uncurry
        (_root_.GD.N0232.N0719.N0856.d009531 hk triangle)) :=
  (_root_.GD.N0232.N0719.N0856.d009541 hk triangle).add
    (_root_.GD.N0232.N0719.N0856.d009542 hk triangle)

theorem d009544
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {p : Fin k → ℝ} (hp : _root_.GD.N0232.N0719.N0951.d003580 p)
    (w : Fin 3 → ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N0856.d009528 triangle p w := by
  unfold _root_.GD.N0232.N0719.N0856.d009528
  exact _root_.GD.N0232.N0719.N1016.d003619
    (add_pos
      (_root_.GD.N0232.N0719.N0951.d003596 hk triangle hp 0)
      (_root_.GD.N0232.N0719.N0951.d003596 hk triangle hp 1))
    (add_pos
      (_root_.GD.N0232.N0719.N0951.d003596 hk triangle hp 0)
      (_root_.GD.N0232.N0719.N0951.d003596 hk triangle hp 2))
    (add_pos
      (_root_.GD.N0232.N0719.N0951.d003596 hk triangle hp 1)
      (_root_.GD.N0232.N0719.N0951.d003596 hk triangle hp 2))

theorem d009545
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) (w : Fin 3 → ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w :=
  _root_.GD.N0232.N0719.N0856.d009544 hk triangle
    (_root_.GD.N0232.N0719.N0857.d009397 hk u) w

theorem d009546
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) (w : Fin 3 → ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w :=
  _root_.GD.N0232.N0719.N0856.d009544 hk triangle
    (_root_.GD.N0232.N0719.N0857.d009398 hk triangle u) w



theorem d009547
    {k : ℕ} (hk : 0 < k)
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) (i : Fin k) :
    99 / (100 * (k : ℝ)) ≤
      _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u i := by
  have hdev :=
    (abs_le.mp
      (_root_.GD.N0232.N0719.N0857.d009393
        hk (_root_.GD.N0232.N0719.N0854.d003821 k) u i)).1
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  unfold _root_.GD.N0232.N0719.N0854.d003821 at hdev ⊢
  field_simp [hkR.ne'] at hdev ⊢
  nlinarith

theorem d009548
    {k : ℕ} (hk : 0 < k)
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) (i : Fin k) :
    _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u i ≤
      101 / (100 * (k : ℝ)) := by
  have hdev :=
    (abs_le.mp
      (_root_.GD.N0232.N0719.N0857.d009393
        hk (_root_.GD.N0232.N0719.N0854.d003821 k) u i)).2
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  unfold _root_.GD.N0232.N0719.N0854.d003821 at hdev ⊢
  field_simp [hkR.ne'] at hdev ⊢
  nlinarith

theorem d009549
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) :
    119 / (100 * (k : ℝ)) ≤
      _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u (triangle 0) := by
  have hdev :=
    (abs_le.mp
      (_root_.GD.N0232.N0719.N0857.d009393
        hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u (triangle 0))).1
  rw [_root_.GD.N0232.N0719.N0854.d003826] at hdev
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  field_simp [hkR.ne'] at hdev ⊢
  nlinarith

theorem d009550
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) :
    _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u (triangle 1) ≤
      81 / (100 * (k : ℝ)) := by
  have hdev :=
    (abs_le.mp
      (_root_.GD.N0232.N0719.N0857.d009393
        hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u (triangle 1))).2
  rw [_root_.GD.N0232.N0719.N0854.d003827] at hdev
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  field_simp [hkR.ne'] at hdev ⊢
  nlinarith






theorem d009551
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) :
    _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u (triangle 0) *
        _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u (triangle 1) <
      _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u (triangle 1) *
        _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u (triangle 0) := by
  let p := _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u
  let q := _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u
  have hp0u : p (triangle 0) ≤ 101 / (100 * (k : ℝ)) :=
    _root_.GD.N0232.N0719.N0856.d009548 hk u _
  have hp1l : 99 / (100 * (k : ℝ)) ≤ p (triangle 1) :=
    _root_.GD.N0232.N0719.N0856.d009547 hk u _
  have hq0l : 119 / (100 * (k : ℝ)) ≤ q (triangle 0) :=
    _root_.GD.N0232.N0719.N0856.d009549 hk triangle u
  have hq1u : q (triangle 1) ≤ 81 / (100 * (k : ℝ)) :=
    _root_.GD.N0232.N0719.N0856.d009550 hk triangle u
  have hp0n : 0 ≤ p (triangle 0) :=
    (_root_.GD.N0232.N0719.N0951.d003590 hk
      (_root_.GD.N0232.N0719.N0857.d009397 hk u) _).le
  have hq1n : 0 ≤ q (triangle 1) :=
    (_root_.GD.N0232.N0719.N0951.d003590 hk
      (_root_.GD.N0232.N0719.N0857.d009398 hk triangle u) _).le
  have hleft :
      p (triangle 0) * q (triangle 1) ≤
        (101 / (100 * (k : ℝ))) *
          (81 / (100 * (k : ℝ))) :=
    mul_le_mul hp0u hq1u hq1n
      (by positivity)
  have hright :
      (99 / (100 * (k : ℝ))) *
          (119 / (100 * (k : ℝ))) ≤
        p (triangle 1) * q (triangle 0) :=
    mul_le_mul hp1l hq0l
      (by positivity)
      (_root_.GD.N0232.N0719.N0951.d003590 hk
        (_root_.GD.N0232.N0719.N0857.d009397 hk u) _).le
  have hmiddle :
      (101 / (100 * (k : ℝ))) *
          (81 / (100 * (k : ℝ))) <
        (99 / (100 * (k : ℝ))) *
          (119 / (100 * (k : ℝ))) := by
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    field_simp [hkR.ne']
    norm_num
  exact hleft.trans_lt (hmiddle.trans_le hright)

theorem d009552
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) :
    _root_.GD.N0232.N0719.N0951.d003586 triangle
          (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u) 0 *
        _root_.GD.N0232.N0719.N0951.d003586 triangle
          (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) 1 <
      _root_.GD.N0232.N0719.N0951.d003586 triangle
          (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u) 1 *
        _root_.GD.N0232.N0719.N0951.d003586 triangle
          (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) 0 := by
  have hraw := _root_.GD.N0232.N0719.N0856.d009551 hk triangle u
  have hpm :
      0 < _root_.GD.N0232.N0719.N0951.d003585 triangle
        (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u) :=
    _root_.GD.N0232.N0719.N0951.d003593 hk triangle
      (_root_.GD.N0232.N0719.N0857.d009397 hk u)
  have hqm :
      0 < _root_.GD.N0232.N0719.N0951.d003585 triangle
        (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) :=
    _root_.GD.N0232.N0719.N0951.d003593 hk triangle
      (_root_.GD.N0232.N0719.N0857.d009398 hk triangle u)
  unfold _root_.GD.N0232.N0719.N0951.d003586
  field_simp [hpm.ne', hqm.ne']
  exact hraw


theorem d009553
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (u : _root_.GD.N0232.N0719.N0857.d009377 k) :
    (fun j =>
      _root_.GD.N0232.N0719.N0951.d003586 triangle
        (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u) j) ≠
    (fun j =>
      _root_.GD.N0232.N0719.N0951.d003586 triangle
        (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) j) := by
  intro h
  have hcross :=
    _root_.GD.N0232.N0719.N0856.d009552 hk triangle u
  have heq :
      _root_.GD.N0232.N0719.N0951.d003586 triangle
            (_root_.GD.N0232.N0719.N0857.d009388 hk
              (_root_.GD.N0232.N0719.N0854.d003821 k) u) 0 *
          _root_.GD.N0232.N0719.N0951.d003586 triangle
            (_root_.GD.N0232.N0719.N0857.d009388 hk
              (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) 1 =
        _root_.GD.N0232.N0719.N0951.d003586 triangle
            (_root_.GD.N0232.N0719.N0857.d009388 hk
              (_root_.GD.N0232.N0719.N0854.d003821 k) u) 1 *
          _root_.GD.N0232.N0719.N0951.d003586 triangle
            (_root_.GD.N0232.N0719.N0857.d009388 hk
              (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) 0 := by
    rw [congrFun h 0, congrFun h 1]
    ring
  exact (ne_of_lt hcross) heq



theorem d009554
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {u : _root_.GD.N0232.N0719.N0857.d009377 k} {w : Fin 3 → ℝ}
    (hw : w ∈ _root_.GD.N0232.N0719.N0856.d009532) :
    0 < _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w := by
  let pu : Fin 3 → ℝ :=
    fun j => _root_.GD.N0232.N0719.N0951.d003586 triangle
      (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u) j
  let ps : Fin 3 → ℝ :=
    fun j => _root_.GD.N0232.N0719.N0951.d003586 triangle
      (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) j
  have hpu : ∀ j, 0 < pu j :=
    fun j => _root_.GD.N0232.N0719.N0951.d003596 hk triangle
      (_root_.GD.N0232.N0719.N0857.d009397 hk u) j
  have hps : ∀ j, 0 < ps j :=
    fun j => _root_.GD.N0232.N0719.N0951.d003596 hk triangle
      (_root_.GD.N0232.N0719.N0857.d009398 hk triangle u) j
  have hu_nonneg :=
    _root_.GD.N0232.N0719.N0856.d009545 hk triangle u w
  have hs_nonneg :=
    _root_.GD.N0232.N0719.N0856.d009546 hk triangle u w
  by_contra hnot
  have hsum0 :
      _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w = 0 := by
    unfold _root_.GD.N0232.N0719.N0856.d009531
    exact le_antisymm (not_lt.mp hnot)
      (add_nonneg hu_nonneg hs_nonneg)
  have hu0 : _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w = 0 := by
    unfold _root_.GD.N0232.N0719.N0856.d009531 at hsum0
    nlinarith
  have hs0 : _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w = 0 := by
    unfold _root_.GD.N0232.N0719.N0856.d009531 at hsum0
    nlinarith
  have hueq :
      pu 0 * w 0 = pu 1 * w 1 ∧
        pu 0 * w 0 = pu 2 * w 2 := by
    apply (_root_.GD.N0232.N0719.N1016.d003620
      (add_pos (hpu 0) (hpu 1))
      (add_pos (hpu 0) (hpu 2))
      (add_pos (hpu 1) (hpu 2))).mp
    exact hu0
  have hseq :
      ps 0 * w 0 = ps 1 * w 1 ∧
        ps 0 * w 0 = ps 2 * w 2 := by
    apply (_root_.GD.N0232.N0719.N1016.d003620
      (add_pos (hps 0) (hps 1))
      (add_pos (hps 0) (hps 2))
      (add_pos (hps 1) (hps 2))).mp
    exact hs0
  have hz0pos : 0 < pu 0 * w 0 := by
    rcases hw.2 with h0 | h1 | h2
    · rw [h0, mul_one]
      exact hpu 0
    · rw [hueq.1, h1, mul_one]
      exact hpu 1
    · rw [hueq.2, h2, mul_one]
      exact hpu 2
  have hw0pos : 0 < w 0 :=
    pos_of_mul_pos_right hz0pos (hpu 0).le
  have hz1pos : 0 < pu 1 * w 1 := by
    rw [← hueq.1]
    exact hz0pos
  have hw1pos : 0 < w 1 :=
    pos_of_mul_pos_right hz1pos (hpu 1).le
  have hmul :
      (pu 0 * ps 1) * (w 0 * w 1) =
        (pu 1 * ps 0) * (w 0 * w 1) := by
    calc
      (pu 0 * ps 1) * (w 0 * w 1) =
          (pu 0 * w 0) * (ps 1 * w 1) := by ring
      _ = (pu 1 * w 1) * (ps 0 * w 0) := by
        rw [hueq.1, hseq.1]
      _ = (pu 1 * ps 0) * (w 0 * w 1) := by ring
  have hcrossEq : pu 0 * ps 1 = pu 1 * ps 0 :=
    mul_right_cancel₀
      (mul_ne_zero hw0pos.ne' hw1pos.ne') hmul
  have hcross :=
    _root_.GD.N0232.N0719.N0856.d009552 hk triangle u
  exact (ne_of_lt hcross) hcrossEq





theorem d009555
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u ∈ _root_.GD.N0232.N0719.N0857.d009383 k,
      ∀ w ∈ _root_.GD.N0232.N0719.N0856.d009532,
        δ ≤ _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w := by
  obtain ⟨δ, hδ, hfloor⟩ :=
    (_root_.GD.N0232.N0719.N0856.d009537 k).exists_forall_le'
      (_root_.GD.N0232.N0719.N0856.d009543 hk triangle).continuousOn
      (fun x hx => _root_.GD.N0232.N0719.N0856.d009554 hk triangle hx.2)
  refine ⟨δ, hδ, ?_⟩
  intro u hu w hw
  exact hfloor (u, w) ⟨hu, hw⟩




def d009556
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) : ℝ :=
  ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
    _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w

theorem d009557
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) :
    IntegrableOn
      (fun u => _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w)
      (_root_.GD.N0232.N0719.N0857.d009383 k) := by
  unfold _root_.GD.N0232.N0719.N0856.d009531
  have hwcont : Continuous
      (fun _ : _root_.GD.N0232.N0719.N0857.d009377 k => w) :=
    continuous_const
  have hgraph : Continuous
      (fun u : _root_.GD.N0232.N0719.N0857.d009377 k => (u, w)) :=
    continuous_id.prodMk hwcont
  have hu := (_root_.GD.N0232.N0719.N0856.d009541 hk triangle).comp hgraph
  have hs := (_root_.GD.N0232.N0719.N0856.d009542 hk triangle).comp hgraph
  have hcont : Continuous (fun u =>
      _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w + _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w) :=
    hu.add hs
  exact hcont.continuousOn.integrableOn_compact
    (_root_.GD.N0232.N0719.N0857.d009384 k)






theorem d009558
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ w ∈ _root_.GD.N0232.N0719.N0856.d009532,
        δ * (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal ≤
          _root_.GD.N0232.N0719.N0856.d009556 hk triangle w := by
  obtain ⟨δ, hδ, hfloor⟩ :=
    _root_.GD.N0232.N0719.N0856.d009555 hk triangle
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  have hconst :
      IntegrableOn (fun _ : _root_.GD.N0232.N0719.N0857.d009377 k => δ)
        (_root_.GD.N0232.N0719.N0857.d009383 k) :=
    integrableOn_const (_root_.GD.N0232.N0719.N0857.d009404 (k := k))
  have hpair :=
    _root_.GD.N0232.N0719.N0856.d009557 hk triangle w
  calc
    δ * (volume (_root_.GD.N0232.N0719.N0857.d009383 k)).toReal =
        ∫ _u : _root_.GD.N0232.N0719.N0857.d009377 k in _root_.GD.N0232.N0719.N0857.d009383 k, δ := by
          rw [setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
    _ ≤ ∫ u in _root_.GD.N0232.N0719.N0857.d009383 k,
          _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w := by
      exact setIntegral_mono_on hconst hpair
        (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet
        (fun u hu => hfloor u hu w hw)


def d009559 (k : ℕ) : Measure (_root_.GD.N0232.N0719.N0857.d009377 k) :=
  volume[|_root_.GD.N0232.N0719.N0857.d009383 k]

theorem d009560 (k : ℕ) :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N0856.d009559 k) := by
  exact cond_isProbabilityMeasure_of_finite
    (_root_.GD.N0232.N0719.N0857.d009403 (k := k)).ne'
    (_root_.GD.N0232.N0719.N0857.d009404 (k := k))

theorem d009561 (k : ℕ) :
    ∀ᵐ u ∂_root_.GD.N0232.N0719.N0856.d009559 k, u ∈ _root_.GD.N0232.N0719.N0857.d009383 k := by
  exact ae_cond_mem (_root_.GD.N0232.N0719.N0857.d009384 k).measurableSet

theorem d009562
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) :
    Integrable
      (fun u => _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w)
      (_root_.GD.N0232.N0719.N0856.d009559 k) := by
  unfold _root_.GD.N0232.N0719.N0856.d009559 ProbabilityTheory.cond
  exact
    (_root_.GD.N0232.N0719.N0856.d009557 hk triangle w).smul_measure
      (ENNReal.inv_ne_top.2
        (_root_.GD.N0232.N0719.N0857.d009403 (k := k)).ne')





theorem d009563
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ w ∈ _root_.GD.N0232.N0719.N0856.d009532,
        δ ≤
          ∫ u,
            _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w
              ∂_root_.GD.N0232.N0719.N0856.d009559 k := by
  obtain ⟨δ, hδ, hfloor⟩ :=
    _root_.GD.N0232.N0719.N0856.d009555 hk triangle
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0856.d009559 k) :=
    _root_.GD.N0232.N0719.N0856.d009560 k
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  have hconst :
      Integrable (fun _ : _root_.GD.N0232.N0719.N0857.d009377 k => δ)
        (_root_.GD.N0232.N0719.N0856.d009559 k) :=
    integrable_const δ
  have hpair :=
    _root_.GD.N0232.N0719.N0856.d009562 hk triangle w
  have hpoint :
      ∀ᵐ u ∂_root_.GD.N0232.N0719.N0856.d009559 k,
        δ ≤ _root_.GD.N0232.N0719.N0856.d009531 hk triangle u w := by
    filter_upwards [_root_.GD.N0232.N0719.N0856.d009561 k] with u hu
    exact hfloor u hu w hw
  have hmono := integral_mono_ae hconst hpair hpoint
  simpa using hmono







theorem d009564
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (w : Fin 3 → ℝ)
    (hF :
      Integrable
        (fun u =>
          _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w)
        (_root_.GD.N0232.N0719.N0856.d009559 k))
    (hkernel :
      Integrable
        (fun u =>
          _root_.GD.N0232.N0719.N0954.d009510 shape
            (_root_.GD.N0232.N0719.N0954.d009506 rate)
            (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u))
        (_root_.GD.N0232.N0719.N0856.d009559 k))
    (hmoment :
      Integrable
        (fun u =>
          _root_.GD.N0232.N0719.N0954.d009510 shape
              (_root_.GD.N0232.N0719.N0954.d009506 rate)
              (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u) *
            _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w)
        (_root_.GD.N0232.N0719.N0856.d009559 k)) :
    (_root_.GD.N0232.N0719.N0954.d009517 shape / _root_.GD.N0232.N0719.N0954.d009518 shape) *
          (_root_.GD.N0232.N0719.N0954.d009509 shape rate *
            _root_.GD.N0232.N0719.N0954.d009524 (_root_.GD.N0232.N0719.N0856.d009559 k) shape
              (_root_.GD.N0232.N0719.N0954.d009506 rate)
              (fun u =>
                _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u)) *
          (∫ u,
            _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w
            ∂_root_.GD.N0232.N0719.N0856.d009559 k) ≤
      _root_.GD.N0232.N0719.N0954.d009509 shape rate *
        _root_.GD.N0232.N0719.N0954.d009525 (_root_.GD.N0232.N0719.N0856.d009559 k) shape
          (_root_.GD.N0232.N0719.N0954.d009506 rate)
          (fun u =>
            _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003821 k) u)
          (fun u =>
            _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0856.d009559 k) :=
    _root_.GD.N0232.N0719.N0856.d009560 k
  let p : _root_.GD.N0232.N0719.N0857.d009377 k → Fin k → ℝ :=
    fun u => _root_.GD.N0232.N0719.N0857.d009388 hk
      (_root_.GD.N0232.N0719.N0854.d003821 k) u
  let F : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun u => _root_.GD.N0232.N0719.N0856.d009529 hk triangle u w
  have hp : ∀ᵐ u ∂_root_.GD.N0232.N0719.N0856.d009559 k,
      _root_.GD.N0232.N0719.N0951.d003580 (p u) := by
    filter_upwards [_root_.GD.N0232.N0719.N0856.d009561 k] with u hu
    exact _root_.GD.N0232.N0719.N0857.d009397 hk u
  have hF_nonneg : ∀ᵐ u ∂_root_.GD.N0232.N0719.N0856.d009559 k, 0 ≤ F u :=
    Filter.Eventually.of_forall fun u =>
      _root_.GD.N0232.N0719.N0856.d009545 hk triangle u w
  simpa only [p, F] using
    (_root_.GD.N0232.N0719.N0954.d009527
      (shape := shape) (rate := rate)
      hk (_root_.GD.N0232.N0719.N0856.d009559 k) hshape hrate p hp F hF hF_nonneg hkernel hmoment)





theorem d009565
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (w : Fin 3 → ℝ)
    (hF :
      Integrable
        (fun u =>
          _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w)
        (_root_.GD.N0232.N0719.N0856.d009559 k))
    (hkernel :
      Integrable
        (fun u =>
          _root_.GD.N0232.N0719.N0954.d009510 shape
            (_root_.GD.N0232.N0719.N0954.d009506 rate)
            (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u))
        (_root_.GD.N0232.N0719.N0856.d009559 k))
    (hmoment :
      Integrable
        (fun u =>
          _root_.GD.N0232.N0719.N0954.d009510 shape
              (_root_.GD.N0232.N0719.N0954.d009506 rate)
              (_root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u) *
            _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w)
        (_root_.GD.N0232.N0719.N0856.d009559 k)) :
    (_root_.GD.N0232.N0719.N0954.d009517 shape / _root_.GD.N0232.N0719.N0954.d009518 shape) *
          (_root_.GD.N0232.N0719.N0954.d009509 shape rate *
            _root_.GD.N0232.N0719.N0954.d009524 (_root_.GD.N0232.N0719.N0856.d009559 k) shape
              (_root_.GD.N0232.N0719.N0954.d009506 rate)
              (fun u =>
                _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u)) *
          (∫ u,
            _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w
            ∂_root_.GD.N0232.N0719.N0856.d009559 k) ≤
      _root_.GD.N0232.N0719.N0954.d009509 shape rate *
        _root_.GD.N0232.N0719.N0954.d009525 (_root_.GD.N0232.N0719.N0856.d009559 k) shape
          (_root_.GD.N0232.N0719.N0954.d009506 rate)
          (fun u =>
            _root_.GD.N0232.N0719.N0857.d009388 hk (_root_.GD.N0232.N0719.N0854.d003822 triangle) u)
          (fun u =>
            _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0856.d009559 k) :=
    _root_.GD.N0232.N0719.N0856.d009560 k
  let p : _root_.GD.N0232.N0719.N0857.d009377 k → Fin k → ℝ :=
    fun u => _root_.GD.N0232.N0719.N0857.d009388 hk
      (_root_.GD.N0232.N0719.N0854.d003822 triangle) u
  let F : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun u => _root_.GD.N0232.N0719.N0856.d009530 hk triangle u w
  have hp : ∀ᵐ u ∂_root_.GD.N0232.N0719.N0856.d009559 k,
      _root_.GD.N0232.N0719.N0951.d003580 (p u) := by
    filter_upwards [_root_.GD.N0232.N0719.N0856.d009561 k] with u hu
    exact _root_.GD.N0232.N0719.N0857.d009398 hk triangle u
  have hF_nonneg : ∀ᵐ u ∂_root_.GD.N0232.N0719.N0856.d009559 k, 0 ≤ F u :=
    Filter.Eventually.of_forall fun u =>
      _root_.GD.N0232.N0719.N0856.d009546 hk triangle u w
  simpa only [p, F] using
    (_root_.GD.N0232.N0719.N0954.d009527
      (shape := shape) (rate := rate)
      hk (_root_.GD.N0232.N0719.N0856.d009559 k) hshape hrate p hp F hF hF_nonneg hkernel hmoment)

end

end GD.N0232.N0719.N0856
