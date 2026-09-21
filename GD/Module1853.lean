import GD.Module1846
import GD.Module1848

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0080.N0325

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1220
open _root_.GD.N0034.N0289 _root_.GD.N0046.N0305
open _root_.GD.N0024.N0274
open _root_.GD.N0024.N0273
open _root_.GD.N0024.N0268

local instance : DecidableEq _root_.GD.N0232.N0720.N1080.d014168 := Classical.decEq _

def d030420 (m n : ℕ) (c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1220.d017301 m n F w - _root_.GD.N0024.N0274.d030344 c F w

def d030421 (m n : ℕ) (c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) : Prop :=
  ∃ p : _root_.GD.N0046.N0305.d030201 m n, ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ ENNReal.ofReal (c θ)

def d030422 (m n : ℕ) (c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) : Prop :=
  ∃ L : ℝ, ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
    (∀ θ ∈ F, 0 ≤ w θ) → _root_.GD.N0080.N0325.d030420 m n c F w ≤ L

def d030423 (m n : ℕ) (c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) : Prop :=
  ∀ L : ℝ, ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
    (∀ θ ∈ F, 0 ≤ w θ) ∧ L < _root_.GD.N0080.N0325.d030420 m n c F w

theorem d030424 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hc : ∀ θ, 0 ≤ c θ) :
    _root_.GD.N0080.N0325.d030421 m n c ↔ ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) → _root_.GD.N0080.N0325.d030420 m n c F w ≤ 0 := by
  simpa only [_root_.GD.N0080.N0325.d030421, _root_.GD.N0080.N0325.d030420, _root_.GD.N0024.N0274.d030344, sub_nonpos] using
    _root_.GD.N0232.N0720.N1220.d017305 m n hm hn c hc

theorem d030425 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hc : ∀ θ, 0 ≤ c θ) :
    _root_.GD.N0080.N0325.d030421 m n c ↔ _root_.GD.N0080.N0325.d030422 m n c := by
  rw [_root_.GD.N0080.N0325.d030424 m n hm hn c hc]
  constructor
  · exact fun h => ⟨0, h⟩
  · rintro ⟨L, hL⟩ F w hw
    by_contra h
    obtain ⟨F', w', hw', hlarge⟩ :=
      _root_.GD.N0024.N0273.d030360 m n c F w hw (lt_of_not_ge h) L
    exact (not_lt_of_ge (hL F' w' hw')) hlarge

theorem d030426 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hc : ∀ θ, 0 ≤ c θ) :
    ¬ _root_.GD.N0080.N0325.d030421 m n c ↔ _root_.GD.N0080.N0325.d030423 m n c := by
  rw [_root_.GD.N0080.N0325.d030425 m n hm hn c hc]
  simp only [_root_.GD.N0080.N0325.d030422, _root_.GD.N0080.N0325.d030423, not_exists, not_forall, not_le, exists_prop]

theorem d030427 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hc : ∀ θ, 0 ≤ c θ) :
    (_root_.GD.N0080.N0325.d030421 m n c ∧ ¬ _root_.GD.N0080.N0325.d030423 m n c) ∨
      (¬ _root_.GD.N0080.N0325.d030421 m n c ∧ _root_.GD.N0080.N0325.d030423 m n c) := by
  by_cases h : _root_.GD.N0080.N0325.d030421 m n c
  · left
    refine ⟨h, ?_⟩
    intro hU
    exact ((_root_.GD.N0080.N0325.d030426 m n hm hn c hc).mpr hU) h
  · exact Or.inr ⟨h, (_root_.GD.N0080.N0325.d030426 m n hm hn c hc).mp h⟩

theorem d030428 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty ↔ _root_.GD.N0080.N0325.d030422 m n (_root_.GD.N0034.N0289.d030220 m n hm hn) := by
  rw [← _root_.GD.N0080.N0325.d030425 m n hm hn _ (_root_.GD.N0034.N0289.d030221 m n hm hn)]
  simp only [_root_.GD.N0080.N0325.d030421, _root_.GD.N0034.N0289.d030223, Set.Nonempty]

theorem d030429
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) → _root_.GD.N0080.N0325.d030420 m n (_root_.GD.N0034.N0289.d030220 m n hm hn) F w ≤ -ε := by
  rw [_root_.GD.N0034.N0289.d030225,
    _root_.GD.N0034.N0288.d030333]
  constructor
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, fun F w hw => ?_⟩
    have hb := h F w hw
    change _root_.GD.N0232.N0720.N1220.d017301 m n F w + ε ≤ _root_.GD.N0024.N0274.d030344 (_root_.GD.N0034.N0289.d030220 m n hm hn) F w at hb
    dsimp only [_root_.GD.N0080.N0325.d030420]
    linarith
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, fun F w hw => ?_⟩
    have hb := h F w hw
    change _root_.GD.N0232.N0720.N1220.d017301 m n F w + ε ≤ _root_.GD.N0024.N0274.d030344 (_root_.GD.N0034.N0289.d030220 m n hm hn) F w
    dsimp only [_root_.GD.N0080.N0325.d030420] at hb
    linarith

theorem d030430 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) → _root_.GD.N0080.N0325.d030420 m n (_root_.GD.N0034.N0289.d030220 m n hm hn) F w ≤ -ε) ∨
        _root_.GD.N0080.N0325.d030423 m n (_root_.GD.N0034.N0289.d030220 m n hm hn) := by
  by_cases h : (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty
  · exact Or.inl ((_root_.GD.N0080.N0325.d030429 m n hm hn).mp h)
  · apply Or.inr
    apply (_root_.GD.N0080.N0325.d030426 m n hm hn _ (_root_.GD.N0034.N0289.d030221 m n hm hn)).mp
    rintro ⟨p, hp⟩
    exact h ⟨p, (_root_.GD.N0034.N0289.d030223 m n hm hn p).mp hp⟩

theorem d030431 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ)
    (hgap : 0 ≤ _root_.GD.N0080.N0325.d030420 m n (_root_.GD.N0034.N0289.d030220 m n hm hn) F w) :
    _root_.GD.N0080.N0325.d030423 m n (_root_.GD.N0034.N0289.d030220 m n hm hn) := by
  rcases _root_.GD.N0080.N0325.d030430 m n hm hn with ⟨ε, hε, h⟩ | h
  · have hb := h F w hw
    exfalso
    linarith
  · exact h

theorem d030432 :
    _root_.GD.N0080.N0325.d030423 6 6 (_root_.GD.N0034.N0289.d030220 6 6 (by norm_num) (by norm_num)) := by
  apply (_root_.GD.N0080.N0325.d030426 6 6 (by norm_num) (by norm_num) _
    (_root_.GD.N0034.N0289.d030221 6 6 (by norm_num) (by norm_num))).mp
  rintro ⟨p, hp⟩
  have hmem := (_root_.GD.N0034.N0289.d030223 6 6 (by norm_num) (by norm_num) p).mp hp
  rw [_root_.GD.N0024.N0268.d030374] at hmem
  exact hmem

theorem d030433 :
    ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) ∧
      ∀ L : ℝ, ∃ t : ℝ, 1 ≤ t ∧
        L < _root_.GD.N0080.N0325.d030420 6 6 (_root_.GD.N0034.N0289.d030220 6 6 (by norm_num) (by norm_num))
          (insert _root_.GD.N0232.N0720.N1080.d014169 F) (_root_.GD.N0024.N0273.d030355 F w t) := by
  obtain ⟨F, w, hw, hgap⟩ := _root_.GD.N0080.N0325.d030432 0
  refine ⟨F, w, hw, fun L => ?_⟩
  let A := _root_.GD.N0080.N0325.d030420 6 6 (_root_.GD.N0034.N0289.d030220 6 6 (by norm_num) (by norm_num)) F w
  let t := 1 + max L 0 / A
  have hA : 0 < A := hgap
  have ht : 1 ≤ t := by
    dsimp only [t]
    linarith [div_nonneg (le_max_right L 0) hA.le]
  refine ⟨t, ht, ?_⟩
  rw [_root_.GD.N0080.N0325.d030420, _root_.GD.N0024.N0273.d030359 6 6 _ F w t hw ht]
  change L < t * A
  have heq : t * A = A + max L 0 := by
    dsimp only [t]
    field_simp [hA.ne']
  rw [heq]
  linarith [le_max_left L 0]

end
end GD.N0080.N0325

#print axioms _root_.GD.N0080.N0325.d030424
#print axioms _root_.GD.N0080.N0325.d030425
#print axioms _root_.GD.N0080.N0325.d030426
#print axioms _root_.GD.N0080.N0325.d030427
#print axioms _root_.GD.N0080.N0325.d030428
#print axioms _root_.GD.N0080.N0325.d030429
#print axioms _root_.GD.N0080.N0325.d030430
#print axioms _root_.GD.N0080.N0325.d030431
#print axioms _root_.GD.N0080.N0325.d030432
#print axioms _root_.GD.N0080.N0325.d030433
