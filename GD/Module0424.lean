import Mathlib
import GD.Module0422
import GD.Module0423













namespace GD.N0135

open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0136

@[ext] structure d006593 where
  ell : ℚ
  f : ℚ
  weight : ℚ
deriving DecidableEq, Repr

def d006594 (D : _root_.GD.N0134.d006518) : ℚ :=
  D.alpha - D.beta

def d006595 (D : _root_.GD.N0134.d006518) : ℚ :=
  D.alpha * D.beta

def d006596 (D : _root_.GD.N0134.d006518) : ℚ :=
  _root_.GD.N0136.d006584 D.d006519 (_root_.GD.N0135.d006594 D) D.d006524

def d006597 (D : _root_.GD.N0134.d006518) : ℚ :=
  _root_.GD.N0136.d006585 D.d006524

def d006598 (D : _root_.GD.N0134.d006518) : ℚ :=
  _root_.GD.N0136.d006586 D.d006519 (_root_.GD.N0135.d006594 D) (_root_.GD.N0135.d006595 D) D.d006524

def d006599 (D : _root_.GD.N0134.d006518) : ℚ :=
  _root_.GD.N0136.d006587 D.d006519 (_root_.GD.N0135.d006594 D) D.d006524

def d006600 (D : _root_.GD.N0134.d006518) : ℚ :=
  -(D.d006524 ^ 2 + D.d006524 + 1) / (D.d006524 - 1)

def d006601 (D : _root_.GD.N0134.d006518) : ℚ :=
  1 / (4 * (D.d006524 - 1))

def d006602 (D : _root_.GD.N0134.d006518) : ℚ :=
  -4 * D.alpha * (D.d006524 + 2) / (D.d006524 - 1)

@[simp] theorem d006603 (D : _root_.GD.N0134.d006518) :
    _root_.GD.N0135.d006594 D.d006525 = -_root_.GD.N0135.d006594 D := by
  simp [_root_.GD.N0135.d006594, _root_.GD.N0134.d006518.d006525]

@[simp] theorem d006604 (D : _root_.GD.N0134.d006518) :
    _root_.GD.N0135.d006595 D.d006525 = _root_.GD.N0135.d006595 D := by
  simp [_root_.GD.N0135.d006595, _root_.GD.N0134.d006518.d006525, mul_comm]

theorem d006605 (D : _root_.GD.N0134.d006518) :
    1 < D.d006524 := by
  unfold _root_.GD.N0134.d006518.d006524
  have hν := D.d006526
  linarith

theorem d006606 (D : _root_.GD.N0134.d006518) :
    D.d006524 - 1 ≠ 0 :=
  ne_of_gt (sub_pos.mpr (_root_.GD.N0135.d006605 D))

def d006607 (D : _root_.GD.N0134.d006518) (k : ℕ) : List _root_.GD.N0135.d006593 :=
  let h := _root_.GD.N0134.d006550 D k
  let eta := _root_.GD.N0134.d006551 D k
  let v0 := _root_.GD.N0135.d006596 D
  let v1 := _root_.GD.N0135.d006597 D
  let v2 := _root_.GD.N0135.d006598 D
  let vt := _root_.GD.N0135.d006599 D
  [ ⟨D.d006520 - h, eta, _root_.GD.N0136.d006564 h v1 v2⟩,
    ⟨D.d006520, eta, _root_.GD.N0136.d006565 h eta v0 v2 vt⟩,
    ⟨D.d006520 + h, eta, _root_.GD.N0136.d006566 h v1 v2⟩,
    ⟨D.d006520, 2 * eta, _root_.GD.N0136.d006567 eta vt⟩ ]

def d006608 (D : _root_.GD.N0134.d006518) (k : ℕ) : List _root_.GD.N0135.d006593 :=
  let h := _root_.GD.N0134.d006550 D k
  let eta := _root_.GD.N0134.d006551 D k
  let v1 := _root_.GD.N0135.d006600 D
  let v3 := _root_.GD.N0135.d006601 D
  let vst := _root_.GD.N0135.d006602 D
  [ ⟨D.d006520 + h, eta, _root_.GD.N0136.d006573 h eta v1 v3 vst⟩,
    ⟨D.d006520 - h, eta, _root_.GD.N0136.d006574 h eta v1 v3 vst⟩,
    ⟨D.d006520 + 2 * h, eta, _root_.GD.N0136.d006575 h v3⟩,
    ⟨D.d006520 - 2 * h, eta, _root_.GD.N0136.d006576 h v3⟩,
    ⟨D.d006520 + h, 2 * eta, _root_.GD.N0136.d006577 h eta vst⟩,
    ⟨D.d006520 - h, 2 * eta, _root_.GD.N0136.d006578 h eta vst⟩ ]

def d006609 (a : _root_.GD.N0135.d006593) : Prop :=
  _root_.GD.N0134.d006552 (a.ell, a.f)

theorem d006610 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    ∀ a ∈ _root_.GD.N0135.d006607 D k, _root_.GD.N0135.d006609 a := by
  intro a ha
  have hnodes := _root_.GD.N0134.d006559 D k
  simp only [_root_.GD.N0135.d006607, List.mem_cons, List.not_mem_nil,
    or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  all_goals
    apply hnodes
    simp [_root_.GD.N0134.d006553]

theorem d006611 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    ∀ a ∈ _root_.GD.N0135.d006608 D k, _root_.GD.N0135.d006609 a := by
  intro a ha
  have hnodes := _root_.GD.N0134.d006560 D k
  simp only [_root_.GD.N0135.d006608, List.mem_cons, List.not_mem_nil,
    or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply hnodes
    simp [_root_.GD.N0134.d006554]

theorem d006612
    (D : _root_.GD.N0134.d006518) (k : ℕ)
    (gm g0 gp gt : ℚ) :
    let h := _root_.GD.N0134.d006550 D k
    let eta := _root_.GD.N0134.d006551 D k
    _root_.GD.N0136.d006564 h (_root_.GD.N0135.d006597 D) (_root_.GD.N0135.d006598 D) * gm
      + _root_.GD.N0136.d006565 h eta (_root_.GD.N0135.d006596 D)
          (_root_.GD.N0135.d006598 D) (_root_.GD.N0135.d006599 D) * g0
      + _root_.GD.N0136.d006566 h (_root_.GD.N0135.d006597 D) (_root_.GD.N0135.d006598 D) * gp
      + _root_.GD.N0136.d006567 eta (_root_.GD.N0135.d006599 D) * gt
      =
      -_root_.GD.N0135.d006596 D * g0
        - _root_.GD.N0135.d006597 D * ((gp - gm) / (2 * h))
        - _root_.GD.N0135.d006598 D * ((gp - 2 * g0 + gm) / h ^ 2)
        - _root_.GD.N0135.d006599 D * ((gt - g0) / eta) := by
  dsimp only
  exact _root_.GD.N0136.d006568
    (_root_.GD.N0134.d006550 D k) (_root_.GD.N0134.d006551 D k)
    (_root_.GD.N0135.d006596 D) (_root_.GD.N0135.d006597 D)
    (_root_.GD.N0135.d006598 D) (_root_.GD.N0135.d006599 D)
    (ne_of_gt (_root_.GD.N0134.d006555 D k)) (ne_of_gt (_root_.GD.N0134.d006556 D k))
    gm g0 gp gt

theorem d006613
    (D : _root_.GD.N0134.d006518) (k : ℕ)
    (gh gmh g2h gm2h gh2t gmh2t : ℚ) :
    let h := _root_.GD.N0134.d006550 D k
    let eta := _root_.GD.N0134.d006551 D k
    _root_.GD.N0136.d006573 h eta (_root_.GD.N0135.d006600 D) (_root_.GD.N0135.d006601 D)
          (_root_.GD.N0135.d006602 D) * gh
      + _root_.GD.N0136.d006574 h eta (_root_.GD.N0135.d006600 D) (_root_.GD.N0135.d006601 D)
          (_root_.GD.N0135.d006602 D) * gmh
      + _root_.GD.N0136.d006575 h (_root_.GD.N0135.d006601 D) * g2h
      + _root_.GD.N0136.d006576 h (_root_.GD.N0135.d006601 D) * gm2h
      + _root_.GD.N0136.d006577 h eta (_root_.GD.N0135.d006602 D) * gh2t
      + _root_.GD.N0136.d006578 h eta (_root_.GD.N0135.d006602 D) * gmh2t
      =
      -_root_.GD.N0135.d006600 D * ((gh - gmh) / (2 * h))
        - _root_.GD.N0135.d006601 D *
          ((g2h - 2 * gh + 2 * gmh - gm2h) / (2 * h ^ 3))
        - _root_.GD.N0135.d006602 D *
          ((gh2t - gmh2t - gh + gmh) / (2 * h * eta)) := by
  dsimp only
  exact _root_.GD.N0136.d006579
    (_root_.GD.N0134.d006550 D k) (_root_.GD.N0134.d006551 D k)
    (_root_.GD.N0135.d006600 D) (_root_.GD.N0135.d006601 D) (_root_.GD.N0135.d006602 D)
    (ne_of_gt (_root_.GD.N0134.d006555 D k)) (ne_of_gt (_root_.GD.N0134.d006556 D k))
    gh gmh g2h gm2h gh2t gmh2t







theorem d006614
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (C₁ C₂ Cstar : ℚ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCstar : 0 < Cstar) :
    ∃ k : ℕ,
      C₁ / _root_.GD.N0134.d006546 k + C₂ / (_root_.GD.N0134.d006546 k) ^ 2 ≤ Cstar / 4
        ∧ (∀ a ∈ _root_.GD.N0135.d006607 (_root_.GD.N0134.d006543 m n hm hn) k,
            _root_.GD.N0135.d006609 a)
        ∧ (∀ a ∈ _root_.GD.N0135.d006608 (_root_.GD.N0134.d006543 m n hm hn) k,
            _root_.GD.N0135.d006609 a) := by
  obtain ⟨k, hk, -, -⟩ :=
    _root_.GD.N0134.d006563 m n hm hn
      C₁ C₂ Cstar hC₁ hC₂ hCstar
  exact ⟨k, hk,
    _root_.GD.N0135.d006610 (_root_.GD.N0134.d006543 m n hm hn) k,
    _root_.GD.N0135.d006611 (_root_.GD.N0134.d006543 m n hm hn) k⟩

end GD.N0135
