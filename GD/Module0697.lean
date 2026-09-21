import GD.Module0687
import GD.Module0264




















open scoped BigOperators

namespace GD.N0232.N0719.N1020

noncomputable section

open _root_.GD.N0232.N0719.N0900


theorem d010260 (f : Fin 3 → ℝ) :
    ∑ i, f i = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp
  ring

theorem d010261
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hcell : _root_.GD.N0232.N0719.N1018.d010019 s) (j : Fin 3) :
    (1 / 5 : ℝ) ≤ _root_.GD.N0232.N0719.N1018.d010013 triangle s j := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  let q : ℝ := (4 * (k : ℝ))⁻¹
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hx :
      3 * q ≤ _root_.GD.N0232.N0719.N0900.d009108 s (triangle j) := by
    simpa [q, div_eq_mul_inv] using (hcell (triangle j)).1
  have hy :
      _root_.GD.N0232.N0719.N0900.d009108 s (triangle 0) ≤ 5 * q := by
    simpa [q, div_eq_mul_inv] using (hcell (triangle 0)).2
  have hz :
      _root_.GD.N0232.N0719.N0900.d009108 s (triangle 1) ≤ 5 * q := by
    simpa [q, div_eq_mul_inv] using (hcell (triangle 1)).2
  have hw :
      _root_.GD.N0232.N0719.N0900.d009108 s (triangle 2) ≤ 5 * q := by
    simpa [q, div_eq_mul_inv] using (hcell (triangle 2)).2
  have hj0 : j = 0 ∨ j = 1 ∨ j = 2 := by
    fin_cases j <;> simp
  have hothers :
      _root_.GD.N0232.N0719.N0900.d009108 s (triangle 0) +
          _root_.GD.N0232.N0719.N0900.d009108 s (triangle 1) +
          _root_.GD.N0232.N0719.N0900.d009108 s (triangle 2) ≤
        5 * _root_.GD.N0232.N0719.N0900.d009108 s (triangle j) := by
    rcases hj0 with rfl | rfl | rfl <;> nlinarith
  have hmass :
      0 < _root_.GD.N0232.N0719.N1018.d010012 triangle s :=
    _root_.GD.N0232.N0719.N1018.d010026 hk triangle s hcell
  rw [_root_.GD.N0232.N0719.N1018.d010013]
  apply (le_div_iff₀ hmass).2
  rw [_root_.GD.N0232.N0719.N1018.d010012, _root_.GD.N0232.N0719.N1020.d010260]
  nlinarith



theorem d010262
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hcell : _root_.GD.N0232.N0719.N1018.d010019 s) :
    _root_.GD.N0232.N0719.N1018.d010012 triangle s ≤
      (15 : ℝ) / (4 * (k : ℝ)) := by
  have h0 := (hcell (triangle 0)).2
  have h1 := (hcell (triangle 1)).2
  have h2 := (hcell (triangle 2)).2
  rw [_root_.GD.N0232.N0719.N1018.d010012, _root_.GD.N0232.N0719.N1020.d010260]
  calc
    _root_.GD.N0232.N0719.N0900.d009108 s (triangle 0) + _root_.GD.N0232.N0719.N0900.d009108 s (triangle 1) +
          _root_.GD.N0232.N0719.N0900.d009108 s (triangle 2) ≤
        (5 : ℝ) / (4 * (k : ℝ)) +
          (5 : ℝ) / (4 * (k : ℝ)) +
            (5 : ℝ) / (4 * (k : ℝ)) := by
      linarith
    _ = (15 : ℝ) / (4 * (k : ℝ)) := by ring

theorem d010263
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    0 ≤ _root_.GD.N0232.N0719.N1018.d010012 triangle s := by
  unfold _root_.GD.N0232.N0719.N1018.d010012
  exact Finset.sum_nonneg fun j _ ↦ _root_.GD.N0232.N0719.N0900.d009132 hk s (triangle j)


theorem d010264
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010012 triangle s ≤ 3 := by
  have h0 := _root_.GD.N0232.N0719.N0900.d009133 hk s (triangle 0)
  have h1 := _root_.GD.N0232.N0719.N0900.d009133 hk s (triangle 1)
  have h2 := _root_.GD.N0232.N0719.N0900.d009133 hk s (triangle 2)
  rw [_root_.GD.N0232.N0719.N1018.d010012, _root_.GD.N0232.N0719.N1020.d010260]
  linarith

theorem d010265
    {k : ℕ} (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010017 triangle s =
      _root_.GD.N0232.N0719.N1019.d003790
        (_root_.GD.N0232.N0719.N1018.d010013 triangle s 0)
        (_root_.GD.N0232.N0719.N1018.d010013 triangle s 1)
        (_root_.GD.N0232.N0719.N1018.d010013 triangle s 2)
        (_root_.GD.N0232.N0719.N1018.d010014 triangle s 0)
        (_root_.GD.N0232.N0719.N1018.d010014 triangle s 1)
        (_root_.GD.N0232.N0719.N1018.d010014 triangle s 2) := by
  simp only [_root_.GD.N0232.N0719.N1018.d010017,
    _root_.GD.N0232.N0719.N1018.d010016,
    _root_.GD.N0232.N0719.N1019.d003790,
    _root_.GD.N0232.N0719.N1019.d003789, _root_.GD.N0232.N0719.N1020.d010260]

theorem d010266
    {k : ℕ} (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010018 triangle s =
      _root_.GD.N0232.N0719.N1016.d003609
        (_root_.GD.N0232.N0719.N1018.d010013 triangle s 0)
        (_root_.GD.N0232.N0719.N1018.d010013 triangle s 1)
        (_root_.GD.N0232.N0719.N1018.d010013 triangle s 2)
        (_root_.GD.N0232.N0719.N1018.d010014 triangle s 0)
        (_root_.GD.N0232.N0719.N1018.d010014 triangle s 1)
        (_root_.GD.N0232.N0719.N1018.d010014 triangle s 2) := by
  rfl



theorem d010267
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hvar : ∀ i, 0 < s.meanVariance i) :
    _root_.GD.N0232.N0719.N1018.d010021 triangle s ^ 2 ≤
      250000 * _root_.GD.N0232.N0719.N1018.d010012 triangle s ^ 2 *
        _root_.GD.N0232.N0719.N1018.d010017 triangle s := by
  by_cases hcell : _root_.GD.N0232.N0719.N1018.d010019 s
  · have hloc : _root_.GD.N0232.N0719.N1018.d010020 s = 1 := by
      simp [_root_.GD.N0232.N0719.N1018.d010020, hcell]
    have hmassPos := _root_.GD.N0232.N0719.N1018.d010026
      hk triangle s hcell
    have hsum :=
      _root_.GD.N0232.N0719.N1018.d010024 triangle s (ne_of_gt hmassPos)
    have hp0 := _root_.GD.N0232.N0719.N1020.d010261 hk triangle s hcell 0
    have hp1 := _root_.GD.N0232.N0719.N1020.d010261 hk triangle s hcell 1
    have hp2 := _root_.GD.N0232.N0719.N1020.d010261 hk triangle s hcell 2
    have hτ :
        0 ≤ _root_.GD.N0232.N0719.N1018.d010015 triangle s :=
      (_root_.GD.N0232.N0719.N1018.d010028 triangle s hvar).le
    have hres :=
      _root_.GD.N0232.N0719.N1019.d003805
        (p₁ := _root_.GD.N0232.N0719.N1018.d010013 triangle s 0)
        (p₂ := _root_.GD.N0232.N0719.N1018.d010013 triangle s 1)
        (p₃ := _root_.GD.N0232.N0719.N1018.d010013 triangle s 2)
        (z₁ := _root_.GD.N0232.N0719.N1018.d010014 triangle s 0)
        (z₂ := _root_.GD.N0232.N0719.N1018.d010014 triangle s 1)
        (z₃ := _root_.GD.N0232.N0719.N1018.d010014 triangle s 2)
        (τ := _root_.GD.N0232.N0719.N1018.d010015 triangle s)
        (by simpa only [_root_.GD.N0232.N0719.N1020.d010260] using hsum)
        hp0 hp1 hp2 hτ
    rw [_root_.GD.N0232.N0719.N1020.d010265]
    calc
      _root_.GD.N0232.N0719.N1018.d010021 triangle s ^ 2 =
          _root_.GD.N0232.N0719.N1018.d010012 triangle s ^ 2 *
            (_root_.GD.N0232.N0719.N1016.d003609
              (_root_.GD.N0232.N0719.N1018.d010013 triangle s 0)
              (_root_.GD.N0232.N0719.N1018.d010013 triangle s 1)
              (_root_.GD.N0232.N0719.N1018.d010013 triangle s 2)
              (_root_.GD.N0232.N0719.N1018.d010014 triangle s 0)
              (_root_.GD.N0232.N0719.N1018.d010014 triangle s 1)
              (_root_.GD.N0232.N0719.N1018.d010014 triangle s 2) /
              (_root_.GD.N0232.N0719.N1018.d010015 triangle s +
                _root_.GD.N0232.N0719.N1019.d003790
                  (_root_.GD.N0232.N0719.N1018.d010013 triangle s 0)
                  (_root_.GD.N0232.N0719.N1018.d010013 triangle s 1)
                  (_root_.GD.N0232.N0719.N1018.d010013 triangle s 2)
                  (_root_.GD.N0232.N0719.N1018.d010014 triangle s 0)
                  (_root_.GD.N0232.N0719.N1018.d010014 triangle s 1)
                  (_root_.GD.N0232.N0719.N1018.d010014 triangle s 2))) ^ 2 := by
            simp only [_root_.GD.N0232.N0719.N1018.d010021, hloc, one_mul, _root_.GD.N0232.N0719.N1018.d010018]
            rw [_root_.GD.N0232.N0719.N1020.d010265]
            ring
      _ ≤ _root_.GD.N0232.N0719.N1018.d010012 triangle s ^ 2 *
            (250000 *
              _root_.GD.N0232.N0719.N1019.d003790
                (_root_.GD.N0232.N0719.N1018.d010013 triangle s 0)
                (_root_.GD.N0232.N0719.N1018.d010013 triangle s 1)
                (_root_.GD.N0232.N0719.N1018.d010013 triangle s 2)
                (_root_.GD.N0232.N0719.N1018.d010014 triangle s 0)
                (_root_.GD.N0232.N0719.N1018.d010014 triangle s 1)
                (_root_.GD.N0232.N0719.N1018.d010014 triangle s 2)) :=
        mul_le_mul_of_nonneg_left hres (sq_nonneg _)
      _ = 250000 * _root_.GD.N0232.N0719.N1018.d010012 triangle s ^ 2 *
            _root_.GD.N0232.N0719.N1019.d003790
              (_root_.GD.N0232.N0719.N1018.d010013 triangle s 0)
              (_root_.GD.N0232.N0719.N1018.d010013 triangle s 1)
              (_root_.GD.N0232.N0719.N1018.d010013 triangle s 2)
              (_root_.GD.N0232.N0719.N1018.d010014 triangle s 0)
              (_root_.GD.N0232.N0719.N1018.d010014 triangle s 1)
              (_root_.GD.N0232.N0719.N1018.d010014 triangle s 2) := by ring
  · have hloc : _root_.GD.N0232.N0719.N1018.d010020 s = 0 := by
      simp [_root_.GD.N0232.N0719.N1018.d010020, hcell]
    have hmassNonneg := _root_.GD.N0232.N0719.N1020.d010263 hk triangle s
    have hdisp := _root_.GD.N0232.N0719.N1018.d010029
      hk triangle s hmassNonneg
    simp [_root_.GD.N0232.N0719.N1018.d010021, hloc]
    positivity



theorem d010268
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hvar : ∀ i, 0 < s.meanVariance i) :
    _root_.GD.N0232.N0719.N1018.d010021 triangle s ^ 2 ≤
      2250000 * _root_.GD.N0232.N0719.N1018.d010017 triangle s := by
  have hmain :=
    _root_.GD.N0232.N0719.N1020.d010267 hk triangle s hvar
  have hmassNonneg := _root_.GD.N0232.N0719.N1020.d010263 hk triangle s
  have hmassLe := _root_.GD.N0232.N0719.N1020.d010264 hk triangle s
  have hmassSq : _root_.GD.N0232.N0719.N1018.d010012 triangle s ^ 2 ≤ 9 := by
    nlinarith
  have hdisp := _root_.GD.N0232.N0719.N1018.d010029
    hk triangle s hmassNonneg
  have hmul :
      250000 * _root_.GD.N0232.N0719.N1018.d010012 triangle s ^ 2 *
          _root_.GD.N0232.N0719.N1018.d010017 triangle s ≤
        2250000 * _root_.GD.N0232.N0719.N1018.d010017 triangle s := by
    nlinarith
  exact hmain.trans hmul

end

end GD.N0232.N0719.N1020
