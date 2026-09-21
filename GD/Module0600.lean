import Mathlib
import GD.Module0424
import GD.Module0417
import GD.Module0418
import GD.Module0598
























open Set

namespace GD.N0146

noncomputable section

open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0135
open _root_.GD.N0110
open _root_.GD.N0132
open _root_.GD.N0130
open _root_.GD.N0147
open _root_.GD.N0111



inductive d008620
  | unbalanced
  | balanced
deriving DecidableEq, Repr

def d008621 (D : _root_.GD.N0134.d006518) : _root_.GD.N0146.d008620 :=
  if _root_.GD.N0135.d006594 D = 0 then .balanced else .unbalanced

def d008622 (D : _root_.GD.N0134.d006518) (k : ℕ) : List _root_.GD.N0135.d006593 :=
  if _root_.GD.N0135.d006594 D = 0 then _root_.GD.N0135.d006608 D k else _root_.GD.N0135.d006607 D k

theorem d008623 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    ∀ a ∈ _root_.GD.N0146.d008622 D k, _root_.GD.N0135.d006609 a := by
  unfold _root_.GD.N0146.d008622
  split_ifs
  · exact _root_.GD.N0135.d006611 D k
  · exact _root_.GD.N0135.d006610 D k

theorem d008624 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    (_root_.GD.N0146.d008622 D k).length =
      match _root_.GD.N0146.d008621 D with
      | .unbalanced => 4
      | .balanced => 6 := by
  unfold _root_.GD.N0146.d008622 _root_.GD.N0146.d008621
  split_ifs <;> rfl


structure d008625
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) where
  C₁ : ℚ
  C₂ : ℚ
  Cstar : ℚ
  C₁_nonneg : 0 ≤ C₁
  C₂_nonneg : 0 ≤ C₂
  Cstar_pos : 0 < Cstar
  k : ℕ
  stopping :
    C₁ / _root_.GD.N0134.d006546 k + C₂ / (_root_.GD.N0134.d006546 k) ^ 2 ≤ Cstar / 4
  branch : _root_.GD.N0146.d008620
  branch_eq : branch = _root_.GD.N0146.d008621 (_root_.GD.N0134.d006543 m n hm hn)
  atoms : List _root_.GD.N0135.d006593
  atoms_eq : atoms = _root_.GD.N0146.d008622 (_root_.GD.N0134.d006543 m n hm hn) k
  atoms_physical : ∀ a ∈ atoms, _root_.GD.N0135.d006609 a



theorem d008626
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (C₁ C₂ Cstar : ℚ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCstar : 0 < Cstar) :
    ∃ S : _root_.GD.N0146.d008625 m n hm hn,
      S.C₁ = C₁ ∧ S.C₂ = C₂ ∧ S.Cstar = Cstar := by
  obtain ⟨k, hk, -, -⟩ :=
    _root_.GD.N0135.d006614
      m n hm hn C₁ C₂ Cstar hC₁ hC₂ hCstar
  let D := _root_.GD.N0134.d006543 m n hm hn
  let S : _root_.GD.N0146.d008625 m n hm hn :=
    { C₁ := C₁
      C₂ := C₂
      Cstar := Cstar
      C₁_nonneg := hC₁
      C₂_nonneg := hC₂
      Cstar_pos := hCstar
      k := k
      stopping := hk
      branch := _root_.GD.N0146.d008621 D
      branch_eq := rfl
      atoms := _root_.GD.N0146.d008622 D k
      atoms_eq := rfl
      atoms_physical := _root_.GD.N0146.d008623 D k }
  exact ⟨S, rfl, rfl, rfl⟩





theorem d008627
    (v₀ v₁ v₂ v₃ x₀ x₁ x₂ x₃ B₀ B₁ B₂ B₃ : ℝ)
    (h₀ : |x₀| ≤ B₀) (h₁ : |x₁| ≤ B₁)
    (h₂ : |x₂| ≤ B₂) (h₃ : |x₃| ≤ B₃)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃) :
    |v₀ * x₀ + v₁ * x₁ + v₂ * x₂ + v₃ * x₃|
      ≤ |v₀| * B₀ + |v₁| * B₁ + |v₂| * B₂ + |v₃| * B₃ := by
  calc
    |v₀ * x₀ + v₁ * x₁ + v₂ * x₂ + v₃ * x₃|
        ≤ |v₀ * x₀| + |v₁ * x₁| + |v₂ * x₂| + |v₃ * x₃| := by
          have h01 := abs_add_le (v₀ * x₀) (v₁ * x₁)
          have h012 :=
            abs_add_le (v₀ * x₀ + v₁ * x₁) (v₂ * x₂)
          have h0123 :=
            abs_add_le (v₀ * x₀ + v₁ * x₁ + v₂ * x₂) (v₃ * x₃)
          linarith
    _ ≤ |v₀| * B₀ + |v₁| * B₁ + |v₂| * B₂ + |v₃| * B₃ := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
      exact add_le_add
        (add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_left h₀ (abs_nonneg v₀))
            (mul_le_mul_of_nonneg_left h₁ (abs_nonneg v₁)))
          (mul_le_mul_of_nonneg_left h₂ (abs_nonneg v₂)))
        (mul_le_mul_of_nonneg_left h₃ (abs_nonneg v₃))

theorem d008628
    (v₁ v₂ v₃ x₁ x₂ x₃ B₁ B₂ B₃ : ℝ)
    (h₁ : |x₁| ≤ B₁) (h₂ : |x₂| ≤ B₂) (h₃ : |x₃| ≤ B₃)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃) :
    |v₁ * x₁ + v₂ * x₂ + v₃ * x₃|
      ≤ |v₁| * B₁ + |v₂| * B₂ + |v₃| * B₃ := by
  calc
    |v₁ * x₁ + v₂ * x₂ + v₃ * x₃|
        ≤ |v₁ * x₁| + |v₂ * x₂| + |v₃ * x₃| := by
          have h12 := abs_add_le (v₁ * x₁) (v₂ * x₂)
          have h123 :=
            abs_add_le (v₁ * x₁ + v₂ * x₂) (v₃ * x₃)
          linarith
    _ ≤ |v₁| * B₁ + |v₂| * B₂ + |v₃| * B₃ := by
      rw [abs_mul, abs_mul, abs_mul]
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left h₁ (abs_nonneg v₁))
          (mul_le_mul_of_nonneg_left h₂ (abs_nonneg v₂)))
        (mul_le_mul_of_nonneg_left h₃ (abs_nonneg v₃))

def d008629
    (α β e r v₀ v₁ v₂ vt : ℝ) (N : ℕ) : ℝ :=
  let η := _root_.GD.N0132.d006444 α β N
  let h := _root_.GD.N0132.d006443 α β N
  (-v₀ * _root_.GD.N0132.d006446 α β e r 0 η 0 0
    - v₁ * _root_.GD.N0110.d006121
        (fun s => _root_.GD.N0132.d006445 α β e r s η) h
    - v₂ * _root_.GD.N0110.d006122
        (fun s => _root_.GD.N0132.d006445 α β e r s η) h
    - vt * _root_.GD.N0130.d006472 α β e r N 0)

def d008630
    (α β e r v₀ v₁ v₂ vt : ℝ) : ℝ :=
  v₀ * _root_.GD.N0132.d006446 α β e r 0 0 0 0
    + v₁ * _root_.GD.N0132.d006446 α β e r 0 0 1 0
    + v₂ * _root_.GD.N0132.d006446 α β e r 0 0 2 0
    + vt * _root_.GD.N0132.d006446 α β e r 0 0 0 1

def d008631
    (α β r v₀ v₁ v₂ vt : ℝ) (N : ℕ) : ℝ :=
  let η := _root_.GD.N0132.d006444 α β N
  let h := _root_.GD.N0132.d006443 α β N
  |v₀| * (η * _root_.GD.N0111.d006160 α β r 0 1)
    + |v₁| *
        (η * _root_.GD.N0111.d006160 α β r 1 1
          + _root_.GD.N0111.d006160 α β r 3 0 * h ^ 2 / 6)
    + |v₂| *
        (η * _root_.GD.N0111.d006160 α β r 2 1
          + _root_.GD.N0111.d006160 α β r 4 0 * h ^ 2 / 12)
    + |vt| * (2 * η * _root_.GD.N0111.d006160 α β r 0 2)



theorem d008632
    {α β e r v₀ v₁ v₂ vt : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N) :
    |_root_.GD.N0146.d008629 α β e r v₀ v₁ v₂ vt N
        + _root_.GD.N0146.d008630 α β e r v₀ v₁ v₂ vt|
      ≤ _root_.GD.N0146.d008631 α β r v₀ v₁ v₂ vt N := by
  let η := _root_.GD.N0132.d006444 α β N
  let h := _root_.GD.N0132.d006443 α β N
  let x₀ :=
    _root_.GD.N0132.d006446 α β e r 0 η 0 0 -
      _root_.GD.N0132.d006446 α β e r 0 0 0 0
  let x₁ :=
    _root_.GD.N0110.d006121 (fun s => _root_.GD.N0132.d006445 α β e r s η) h -
      _root_.GD.N0132.d006446 α β e r 0 0 1 0
  let x₂ :=
    _root_.GD.N0110.d006122 (fun s => _root_.GD.N0132.d006445 α β e r s η) h -
      _root_.GD.N0132.d006446 α β e r 0 0 2 0
  let x₃ :=
    _root_.GD.N0130.d006472 α β e r N 0 -
      _root_.GD.N0132.d006446 α β e r 0 0 0 1
  let B₀ := η * _root_.GD.N0111.d006160 α β r 0 1
  let B₁ :=
    η * _root_.GD.N0111.d006160 α β r 1 1
      + _root_.GD.N0111.d006160 α β r 3 0 * h ^ 2 / 6
  let B₂ :=
    η * _root_.GD.N0111.d006160 α β r 2 1
      + _root_.GD.N0111.d006160 α β r 4 0 * h ^ 2 / 12
  let B₃ := 2 * η * _root_.GD.N0111.d006160 α β r 0 2
  have hx₀ : |x₀| ≤ B₀ := by
    simpa [x₀, B₀, η] using
      (_root_.GD.N0132.d006468 0 0 hα hβ he₀ he₁ hr hN)
  have hx₁ : |x₁| ≤ B₁ := by
    simpa [x₁, B₁, η, h] using
      (_root_.GD.N0132.d006469 hα hβ he₀ he₁ hr hN)
  have hx₂ : |x₂| ≤ B₂ := by
    simpa [x₂, B₂, η, h] using
      (_root_.GD.N0132.d006470 hα hβ he₀ he₁ hr hN)
  have hx₃ : |x₃| ≤ B₃ := by
    simpa [x₃, B₃, η, _root_.GD.N0130.d006472] using
      (_root_.GD.N0130.d006476 hα hβ he₀ he₁ hr hN)
  have hη : 0 ≤ η := (_root_.GD.N0132.d006449 hα hβ hN).le
  have hh : 0 ≤ h := (_root_.GD.N0132.d006448 hα hβ hN).le
  have hB (p q : ℕ) :
      0 ≤ _root_.GD.N0111.d006160 α β r p q :=
    _root_.GD.N0132.d006467 p q hα hβ hr
  have hB₀ : 0 ≤ B₀ := by
    exact mul_nonneg hη (hB 0 1)
  have hB₁ : 0 ≤ B₁ := by
    exact add_nonneg
      (mul_nonneg hη (hB 1 1))
      (div_nonneg (mul_nonneg (hB 3 0) (sq_nonneg h)) (by norm_num))
  have hB₂ : 0 ≤ B₂ := by
    exact add_nonneg
      (mul_nonneg hη (hB 2 1))
      (div_nonneg (mul_nonneg (hB 4 0) (sq_nonneg h)) (by norm_num))
  have hB₃ : 0 ≤ B₃ := by
    exact mul_nonneg (mul_nonneg (by norm_num) hη) (hB 0 2)
  have hsum :=
    _root_.GD.N0146.d008627 (-v₀) (-v₁) (-v₂) (-vt)
      x₀ x₁ x₂ x₃ B₀ B₁ B₂ B₃
      hx₀ hx₁ hx₂ hx₃ hB₀ hB₁ hB₂ hB₃
  have hrearrange :
      _root_.GD.N0146.d008629 α β e r v₀ v₁ v₂ vt N
          + _root_.GD.N0146.d008630 α β e r v₀ v₁ v₂ vt
        = (-v₀) * x₀ + (-v₁) * x₁ + (-v₂) * x₂ + (-vt) * x₃ := by
    dsimp [_root_.GD.N0146.d008629, _root_.GD.N0146.d008630,
      x₀, x₁, x₂, x₃, η, h, _root_.GD.N0130.d006472]
    ring
  rw [hrearrange]
  simpa [_root_.GD.N0146.d008631, B₀, B₁, B₂, B₃, η, h] using hsum

def d008633
    (α β e r v₁ v₃ vst : ℝ) (N : ℕ) : ℝ :=
  let η := _root_.GD.N0132.d006444 α β N
  let h := _root_.GD.N0132.d006443 α β N
  (-v₁ * _root_.GD.N0110.d006121
      (fun s => _root_.GD.N0132.d006445 α β e r s η) h
    - v₃ * _root_.GD.N0110.d006123
      (fun s => _root_.GD.N0132.d006445 α β e r s η) h
    - vst * _root_.GD.N0110.d006121
      (fun s => _root_.GD.N0130.d006472 α β e r N s) h)

def d008634
    (α β e r v₁ v₃ vst : ℝ) : ℝ :=
  v₁ * _root_.GD.N0132.d006446 α β e r 0 0 1 0
    + v₃ * _root_.GD.N0132.d006446 α β e r 0 0 3 0
    + vst * _root_.GD.N0132.d006446 α β e r 0 0 1 1

def d008635
    (α β r v₁ v₃ vst : ℝ) (N : ℕ) : ℝ :=
  let η := _root_.GD.N0132.d006444 α β N
  let h := _root_.GD.N0132.d006443 α β N
  |v₁| *
      (η * _root_.GD.N0111.d006160 α β r 1 1
        + _root_.GD.N0111.d006160 α β r 3 0 * h ^ 2 / 6)
    + |v₃| *
      (η * _root_.GD.N0111.d006160 α β r 3 1
        + (17 / 60 : ℝ) * _root_.GD.N0111.d006160 α β r 5 0 * h ^ 2)
    + |vst| *
      (2 * η * _root_.GD.N0111.d006160 α β r 1 2
        + _root_.GD.N0111.d006160 α β r 3 1 * h ^ 2 / 6)



theorem d008636
    {α β e r v₁ v₃ vst : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N) :
    |_root_.GD.N0146.d008633 α β e r v₁ v₃ vst N
        + _root_.GD.N0146.d008634 α β e r v₁ v₃ vst|
      ≤ _root_.GD.N0146.d008635 α β r v₁ v₃ vst N := by
  let η := _root_.GD.N0132.d006444 α β N
  let h := _root_.GD.N0132.d006443 α β N
  let x₁ :=
    _root_.GD.N0110.d006121 (fun s => _root_.GD.N0132.d006445 α β e r s η) h -
      _root_.GD.N0132.d006446 α β e r 0 0 1 0
  let x₃ :=
    _root_.GD.N0110.d006123 (fun s => _root_.GD.N0132.d006445 α β e r s η) h -
      _root_.GD.N0132.d006446 α β e r 0 0 3 0
  let xₛₜ :=
    _root_.GD.N0110.d006121 (fun s => _root_.GD.N0130.d006472 α β e r N s) h -
      _root_.GD.N0132.d006446 α β e r 0 0 1 1
  let B₁ :=
    η * _root_.GD.N0111.d006160 α β r 1 1
      + _root_.GD.N0111.d006160 α β r 3 0 * h ^ 2 / 6
  let B₃ :=
    η * _root_.GD.N0111.d006160 α β r 3 1
      + (17 / 60 : ℝ) * _root_.GD.N0111.d006160 α β r 5 0 * h ^ 2
  let Bₛₜ :=
    2 * η * _root_.GD.N0111.d006160 α β r 1 2
      + _root_.GD.N0111.d006160 α β r 3 1 * h ^ 2 / 6
  have hx₁ : |x₁| ≤ B₁ := by
    simpa [x₁, B₁, η, h] using
      (_root_.GD.N0132.d006469 hα hβ he₀ he₁ hr hN)
  have hx₃ : |x₃| ≤ B₃ := by
    simpa [x₃, B₃, η, h] using
      (_root_.GD.N0132.d006471 hα hβ he₀ he₁ hr hN)
  have hxₛₜ : |xₛₜ| ≤ Bₛₜ := by
    simpa [xₛₜ, Bₛₜ, η, h] using
      (_root_.GD.N0130.d006479 hα hβ he₀ he₁ hr hN)
  have hη : 0 ≤ η := (_root_.GD.N0132.d006449 hα hβ hN).le
  have hh : 0 ≤ h := (_root_.GD.N0132.d006448 hα hβ hN).le
  have hB (p q : ℕ) :
      0 ≤ _root_.GD.N0111.d006160 α β r p q :=
    _root_.GD.N0132.d006467 p q hα hβ hr
  have hB₁ : 0 ≤ B₁ := by
    exact add_nonneg
      (mul_nonneg hη (hB 1 1))
      (div_nonneg (mul_nonneg (hB 3 0) (sq_nonneg h)) (by norm_num))
  have hB₃ : 0 ≤ B₃ := by
    exact add_nonneg
      (mul_nonneg hη (hB 3 1))
      (mul_nonneg
        (mul_nonneg (by norm_num) (hB 5 0)) (sq_nonneg h))
  have hBₛₜ : 0 ≤ Bₛₜ := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hη) (hB 1 2))
      (div_nonneg (mul_nonneg (hB 3 1) (sq_nonneg h)) (by norm_num))
  have hsum :=
    _root_.GD.N0146.d008628 (-v₁) (-v₃) (-vst)
      x₁ x₃ xₛₜ B₁ B₃ Bₛₜ
      hx₁ hx₃ hxₛₜ hB₁ hB₃ hBₛₜ
  have hrearrange :
      _root_.GD.N0146.d008633 α β e r v₁ v₃ vst N
          + _root_.GD.N0146.d008634 α β e r v₁ v₃ vst
        = (-v₁) * x₁ + (-v₃) * x₃ + (-vst) * xₛₜ := by
    dsimp [_root_.GD.N0146.d008633, _root_.GD.N0146.d008634,
      x₁, x₃, xₛₜ, η, h]
    ring
  rw [hrearrange]
  simpa [_root_.GD.N0146.d008635, B₁, B₃, Bₛₜ, η, h] using hsum




structure d008637 where
  centers : List (ℚ × ℚ)
  width : ℚ
  width_pos : 0 < width
  multipliers : List ℚ
  multiplier_count : multipliers.length = centers.length
  all_boxes_physical :
    ∀ center ∈ centers, ∀ p : ℚ × ℚ,
      (|p.1 - center.1| < width ∧ |p.2 - center.2| < width) →
        0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2
  boxes_pairwise_disjoint :
    ∀ first ∈ centers, ∀ second ∈ centers,
      first ≠ second →
        ¬ ∃ p : ℚ × ℚ,
          (|p.1 - first.1| < width ∧ |p.2 - first.2| < width)
            ∧ (|p.1 - second.1| < width ∧ |p.2 - second.2| < width)




structure d008638
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) where
  seed : _root_.GD.N0146.d008625 m n hm hn
  geometry : _root_.GD.N0146.d008637
  centers_match :
    geometry.centers = seed.atoms.map (fun a => (a.ell, a.f))
  C : ℚ
  M : ℚ
  C_pos : 0 < C
  M_pos : 0 < M
  atomic : ℝ
  smear : ℝ
  densityError : ℝ
  energy : ℝ
  trace : ℝ
  trace_eq : trace = atomic + smear + densityError
  atomic_margin : atomic ≤ -(3 * (C : ℝ) / 4)
  smearing_bound : |smear| ≤ (C : ℝ) / 16
  density_bound : |densityError| ≤ (C : ℝ) / 16
  energy_nonneg : 0 ≤ energy
  energy_ceiling : energy ≤ (M : ℝ)

namespace d008638

def d008639 {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (C : _root_.GD.N0146.d008638 m n hm hn) : ℚ :=
  C.C / 2

def d008640 {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (C : _root_.GD.N0146.d008638 m n hm hn) : ℚ :=
  C.d008639 / C.M

theorem d008641
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (C : _root_.GD.N0146.d008638 m n hm hn) :
    C.trace ≤ -((C.C : ℝ) / 2) := by
  rw [C.trace_eq]
  exact _root_.GD.N0147.d008613
    C.atomic C.smear C.densityError (C.C : ℝ)
    (by exact_mod_cast C.C_pos.le)
    C.atomic_margin C.smearing_bound C.density_bound

theorem d008642
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (C : _root_.GD.N0146.d008638 m n hm hn) :
    0 < C.d008640 := by
  unfold _root_.GD.N0146.d008638.d008640 _root_.GD.N0146.d008638.d008639
  exact div_pos (div_pos C.C_pos (by norm_num)) C.M_pos

theorem d008643
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (C : _root_.GD.N0146.d008638 m n hm hn) :
    2 * (C.d008640 : ℝ) * C.trace + (C.d008640 : ℝ) ^ 2 * C.energy
      ≤ -(((C.d008639 : ℚ) : ℝ) ^ 2 / (C.M : ℝ)) := by
  have hδQ : 0 < C.d008639 := by
    unfold _root_.GD.N0146.d008638.d008639
    exact div_pos C.C_pos (by norm_num)
  have hδR : 0 < ((C.d008639 : ℚ) : ℝ) := by exact_mod_cast hδQ
  have hMR : 0 < (C.M : ℝ) := by exact_mod_cast C.M_pos
  have htrace :
      C.trace ≤ -(((C.d008639 : ℚ) : ℝ)) := by
    simpa [_root_.GD.N0146.d008638.d008639] using C.d008641
  have h :=
    _root_.GD.N0147.d008614
      C.trace C.energy ((C.d008639 : ℚ) : ℝ) (C.M : ℝ)
      hδR hMR htrace C.energy_ceiling
  simpa [_root_.GD.N0146.d008638.d008640] using h

theorem d008644
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (C : _root_.GD.N0146.d008638 m n hm hn) :
    2 * (C.d008640 : ℝ) * C.trace + (C.d008640 : ℝ) ^ 2 * C.energy < 0 := by
  have hδQ : 0 < C.d008639 := by
    unfold _root_.GD.N0146.d008638.d008639
    exact div_pos C.C_pos (by norm_num)
  have hδR : 0 < ((C.d008639 : ℚ) : ℝ) := by exact_mod_cast hδQ
  have hMR : 0 < (C.M : ℝ) := by exact_mod_cast C.M_pos
  have hneg :
      -(((C.d008639 : ℚ) : ℝ) ^ 2 / (C.M : ℝ)) < 0 := by
    exact neg_lt_zero.mpr (div_pos (sq_pos_of_pos hδR) hMR)
  exact C.d008643.trans_lt hneg

end d008638










theorem d008645
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (C : _root_.GD.N0146.d008638 m n hm hn) :
    C.seed.branch = _root_.GD.N0146.d008621 (_root_.GD.N0134.d006543 m n hm hn)
      ∧ C.seed.atoms =
          _root_.GD.N0146.d008622 (_root_.GD.N0134.d006543 m n hm hn) C.seed.k
      ∧ (∀ a ∈ C.seed.atoms, _root_.GD.N0135.d006609 a)
      ∧ C.trace ≤ -((C.C : ℝ) / 2)
      ∧ 0 < C.d008640
      ∧ 2 * (C.d008640 : ℝ) * C.trace
          + (C.d008640 : ℝ) ^ 2 * C.energy
            ≤ -(((C.d008639 : ℚ) : ℝ) ^ 2 / (C.M : ℝ))
      ∧ 2 * (C.d008640 : ℝ) * C.trace
          + (C.d008640 : ℝ) ^ 2 * C.energy < 0 := by
  exact ⟨C.seed.branch_eq, C.seed.atoms_eq, C.seed.atoms_physical,
    C.d008641, C.d008642, C.d008643,
    C.d008644⟩

end

end GD.N0146
