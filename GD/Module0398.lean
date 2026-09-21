import Mathlib



















noncomputable section

namespace GD.N0110

def d006121 (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  (f h - f (-h)) / (2 * h)

def d006122 (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  (f h - 2 * f 0 + f (-h)) / h ^ 2

def d006123 (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  (f (2 * h) - 2 * f h + 2 * f (-h) - f (-2 * h)) /
    (2 * h ^ 3)

def d006124 (f0 f1 f2 x : ℝ) : ℝ :=
  f0 + f1 * x + f2 * x ^ 2 / 2

def d006125 (f0 f1 f2 f3 x : ℝ) : ℝ :=
  _root_.GD.N0110.d006124 f0 f1 f2 x + f3 * x ^ 3 / 6

def d006126 (f0 f1 f2 f3 f4 x : ℝ) : ℝ :=
  _root_.GD.N0110.d006125 f0 f1 f2 f3 x + f4 * x ^ 4 / 24



theorem d006127
    (f : ℝ → ℝ) (h f0 f1 f2 M : ℝ)
    (hh : 0 < h)
    (hp :
      |f h - _root_.GD.N0110.d006124 f0 f1 f2 h| ≤ M * h ^ 3 / 6)
    (hm :
      |f (-h) - _root_.GD.N0110.d006124 f0 f1 f2 (-h)| ≤ M * h ^ 3 / 6) :
    |_root_.GD.N0110.d006121 f h - f1| ≤ M * h ^ 2 / 6 := by
  let rp := f h - _root_.GD.N0110.d006124 f0 f1 f2 h
  let rm := f (-h) - _root_.GD.N0110.d006124 f0 f1 f2 (-h)
  have hden : 0 < 2 * h := by positivity
  have hid :
      _root_.GD.N0110.d006121 f h - f1 = (rp - rm) / (2 * h) := by
    dsimp [_root_.GD.N0110.d006121, rp, rm, _root_.GD.N0110.d006124]
    field_simp [ne_of_gt hh]
    ring
  rw [hid, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  calc
    |rp - rm| ≤ |rp| + |rm| := abs_sub _ _
    _ ≤ M * h ^ 3 / 6 + M * h ^ 3 / 6 :=
      add_le_add (by simpa [rp] using hp) (by simpa [rm] using hm)
    _ = (M * h ^ 2 / 6) * (2 * h) := by ring



theorem d006128
    (f : ℝ → ℝ) (h f0 f1 f2 f3 M : ℝ)
    (hh : 0 < h) (h0 : f 0 = f0)
    (hp :
      |f h - _root_.GD.N0110.d006125 f0 f1 f2 f3 h| ≤ M * h ^ 4 / 24)
    (hm :
      |f (-h) - _root_.GD.N0110.d006125 f0 f1 f2 f3 (-h)| ≤
        M * h ^ 4 / 24) :
    |_root_.GD.N0110.d006122 f h - f2| ≤ M * h ^ 2 / 12 := by
  let rp := f h - _root_.GD.N0110.d006125 f0 f1 f2 f3 h
  let rm := f (-h) - _root_.GD.N0110.d006125 f0 f1 f2 f3 (-h)
  have hden : 0 < h ^ 2 := sq_pos_of_pos hh
  have hid :
      _root_.GD.N0110.d006122 f h - f2 = (rp + rm) / h ^ 2 := by
    dsimp [_root_.GD.N0110.d006122, rp, rm, _root_.GD.N0110.d006125, _root_.GD.N0110.d006124]
    rw [h0]
    field_simp [ne_of_gt hh]
    ring
  rw [hid, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  calc
    |rp + rm| ≤ |rp| + |rm| := abs_add_le _ _
    _ ≤ M * h ^ 4 / 24 + M * h ^ 4 / 24 :=
      add_le_add (by simpa [rp] using hp) (by simpa [rm] using hm)
    _ = (M * h ^ 2 / 12) * h ^ 2 := by ring






theorem d006129
    (f : ℝ → ℝ) (h f0 f1 f2 f3 f4 M : ℝ)
    (hh : 0 < h)
    (hp1 :
      |f h - _root_.GD.N0110.d006126 f0 f1 f2 f3 f4 h| ≤ M * h ^ 5 / 120)
    (hm1 :
      |f (-h) - _root_.GD.N0110.d006126 f0 f1 f2 f3 f4 (-h)| ≤
        M * h ^ 5 / 120)
    (hp2 :
      |f (2 * h) - _root_.GD.N0110.d006126 f0 f1 f2 f3 f4 (2 * h)| ≤
        M * (2 * h) ^ 5 / 120)
    (hm2 :
      |f (-2 * h) - _root_.GD.N0110.d006126 f0 f1 f2 f3 f4 (-2 * h)| ≤
        M * (2 * h) ^ 5 / 120) :
    |_root_.GD.N0110.d006123 f h - f3| ≤ (17 / 60 : ℝ) * M * h ^ 2 := by
  let rp1 := f h - _root_.GD.N0110.d006126 f0 f1 f2 f3 f4 h
  let rm1 := f (-h) - _root_.GD.N0110.d006126 f0 f1 f2 f3 f4 (-h)
  let rp2 := f (2 * h) - _root_.GD.N0110.d006126 f0 f1 f2 f3 f4 (2 * h)
  let rm2 := f (-2 * h) - _root_.GD.N0110.d006126 f0 f1 f2 f3 f4 (-2 * h)
  have hden : 0 < 2 * h ^ 3 := by positivity
  have hid :
      _root_.GD.N0110.d006123 f h - f3 =
        (rp2 - 2 * rp1 + 2 * rm1 - rm2) / (2 * h ^ 3) := by
    dsimp [_root_.GD.N0110.d006123, rp1, rm1, rp2, rm2,
      _root_.GD.N0110.d006126, _root_.GD.N0110.d006125, _root_.GD.N0110.d006124]
    field_simp [ne_of_gt hh]
    ring
  rw [hid, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  calc
    |rp2 - 2 * rp1 + 2 * rm1 - rm2|
        ≤ |rp2| + 2 * |rp1| + 2 * |rm1| + |rm2| := by
          calc
            |rp2 - 2 * rp1 + 2 * rm1 - rm2|
                ≤ |rp2 - 2 * rp1 + 2 * rm1| + |rm2| := abs_sub _ _
            _ ≤ (|rp2 - 2 * rp1| + |2 * rm1|) + |rm2| := by
              gcongr
              exact abs_add_le _ _
            _ ≤ ((|rp2| + |2 * rp1|) + |2 * rm1|) + |rm2| := by
              gcongr
              exact abs_sub _ _
            _ = |rp2| + 2 * |rp1| + 2 * |rm1| + |rm2| := by
              simp [abs_mul]
    _ ≤ M * (2 * h) ^ 5 / 120
          + 2 * (M * h ^ 5 / 120)
          + 2 * (M * h ^ 5 / 120)
          + M * (2 * h) ^ 5 / 120 := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (by simpa [rp2] using hp2)
            (mul_le_mul_of_nonneg_left
              (by simpa [rp1] using hp1) (by norm_num)))
          (mul_le_mul_of_nonneg_left
            (by simpa [rm1] using hm1) (by norm_num)))
        (by simpa [rm2] using hm2)
    _ = ((17 / 60 : ℝ) * M * h ^ 2) * (2 * h ^ 3) := by ring



def d006130 (f : ℝ → ℝ) (η : ℝ) : ℝ :=
  (f (2 * η) - f η) / η




theorem d006131
    (f f' f'' : ℝ → ℝ) (η M : ℝ)
    (hη : 0 < η) (hM : 0 ≤ M)
    (hf :
      ∀ x ∈ Set.Icc η (2 * η),
        HasDerivWithinAt f (f' x) (Set.Icc η (2 * η)) x)
    (hf' :
      ∀ x ∈ Set.Icc 0 (2 * η),
        HasDerivWithinAt f' (f'' x) (Set.Icc 0 (2 * η)) x)
    (hbound :
      ∀ x ∈ Set.Ico 0 (2 * η), |f'' x| ≤ M) :
    |_root_.GD.N0110.d006130 f η - f' 0| ≤ 2 * η * M := by
  have htwo : 0 ≤ 2 * η := by positivity
  have hlip :
      ∀ x ∈ Set.Icc 0 (2 * η), |f' x - f' 0| ≤ M * x := by
    intro x hx
    have h :=
      norm_image_sub_le_of_norm_deriv_le_segment'
        hf' (fun y hy => by simpa [Real.norm_eq_abs] using hbound y hy)
        x hx
    simpa [Real.norm_eq_abs] using h
  let g : ℝ → ℝ := f - fun x => f' 0 * x
  have hg :
      ∀ x ∈ Set.Icc η (2 * η),
        HasDerivWithinAt g (f' x - f' 0) (Set.Icc η (2 * η)) x := by
    intro x hx
    have hlin :
        HasDerivWithinAt (fun y : ℝ => f' 0 * y) (f' 0)
          (Set.Icc η (2 * η)) x := by
      simpa using
        (((hasDerivAt_id x).const_mul (f' 0)).hasDerivWithinAt)
    simpa [g] using (hf x hx).sub hlin
  have hgbound :
      ∀ x ∈ Set.Ico η (2 * η), ‖f' x - f' 0‖ ≤ 2 * η * M := by
    intro x hx
    have hx0 : x ∈ Set.Icc 0 (2 * η) := ⟨by linarith [hx.1], hx.2.le⟩
    have h₁ := hlip x hx0
    have h₂ : M * x ≤ M * (2 * η) :=
      mul_le_mul_of_nonneg_left hx.2.le hM
    rw [Real.norm_eq_abs]
    calc
      |f' x - f' 0| ≤ M * x := h₁
      _ ≤ M * (2 * η) := h₂
      _ = 2 * η * M := by ring
  have hseg :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      hg hgbound (2 * η) (Set.right_mem_Icc.mpr (by linarith))
  have hid :
      _root_.GD.N0110.d006130 f η - f' 0 =
        (g (2 * η) - g η) / η := by
    dsimp [_root_.GD.N0110.d006130, g]
    field_simp [ne_of_gt hη]
    ring
  rw [hid, abs_div, abs_of_pos hη]
  apply (div_le_iff₀ hη).2
  calc
    |g (2 * η) - g η|
        ≤ (2 * η * M) * (2 * η - η) := by
          simpa [Real.norm_eq_abs] using hseg
    _ = (2 * η * M) * η := by ring







theorem d006132
    (f : ℝ → ℝ) (h η target atEta Bs Bt : ℝ)
    (hcenter :
      |_root_.GD.N0110.d006121 f h - atEta| ≤ Bs * h ^ 2 / 6)
    (htransport : |atEta - target| ≤ η * Bt) :
    |_root_.GD.N0110.d006121 f h - target|
      ≤ η * Bt + Bs * h ^ 2 / 6 := by
  calc
    |_root_.GD.N0110.d006121 f h - target|
        = |(_root_.GD.N0110.d006121 f h - atEta) + (atEta - target)| := by ring
    _ ≤ |_root_.GD.N0110.d006121 f h - atEta| + |atEta - target| :=
      abs_add_le _ _
    _ ≤ Bs * h ^ 2 / 6 + η * Bt :=
      add_le_add hcenter htransport
    _ = η * Bt + Bs * h ^ 2 / 6 := by ring



theorem d006133
    (f : ℝ → ℝ) (h η target atEta Bs Bt : ℝ)
    (hcenter :
      |_root_.GD.N0110.d006122 f h - atEta| ≤ Bs * h ^ 2 / 12)
    (htransport : |atEta - target| ≤ η * Bt) :
    |_root_.GD.N0110.d006122 f h - target|
      ≤ η * Bt + Bs * h ^ 2 / 12 := by
  calc
    |_root_.GD.N0110.d006122 f h - target|
        = |(_root_.GD.N0110.d006122 f h - atEta) + (atEta - target)| := by ring
    _ ≤ |_root_.GD.N0110.d006122 f h - atEta| + |atEta - target| :=
      abs_add_le _ _
    _ ≤ Bs * h ^ 2 / 12 + η * Bt :=
      add_le_add hcenter htransport
    _ = η * Bt + Bs * h ^ 2 / 12 := by ring




theorem d006134
    (f : ℝ → ℝ) (h η target atEta Bs Bt : ℝ)
    (hcenter :
      |_root_.GD.N0110.d006123 f h - atEta| ≤ (17 / 60 : ℝ) * Bs * h ^ 2)
    (htransport : |atEta - target| ≤ η * Bt) :
    |_root_.GD.N0110.d006123 f h - target|
      ≤ η * Bt + (17 / 60 : ℝ) * Bs * h ^ 2 := by
  calc
    |_root_.GD.N0110.d006123 f h - target|
        = |(_root_.GD.N0110.d006123 f h - atEta) + (atEta - target)| := by ring
    _ ≤ |_root_.GD.N0110.d006123 f h - atEta| + |atEta - target| :=
      abs_add_le _ _
    _ ≤ (17 / 60 : ℝ) * Bs * h ^ 2 + η * Bt :=
      add_le_add hcenter htransport
    _ = η * Bt + (17 / 60 : ℝ) * Bs * h ^ 2 := by ring





theorem d006135
    (mixed forwardTarget target h η Bs Bt : ℝ)
    (hcenter : |mixed - forwardTarget| ≤ Bs * h ^ 2 / 6)
    (hforward : |forwardTarget - target| ≤ 2 * η * Bt) :
    |mixed - target| ≤ 2 * η * Bt + Bs * h ^ 2 / 6 := by
  calc
    |mixed - target| = |(mixed - forwardTarget) +
        (forwardTarget - target)| := by ring
    _ ≤ |mixed - forwardTarget| + |forwardTarget - target| :=
      abs_add_le _ _
    _ ≤ Bs * h ^ 2 / 6 + 2 * η * Bt :=
      add_le_add hcenter hforward
    _ = 2 * η * Bt + Bs * h ^ 2 / 6 := by ring

end GD.N0110
