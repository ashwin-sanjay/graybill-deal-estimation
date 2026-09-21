import GD.Module0306























namespace GD.N0238.N0754

open _root_.GD.N0238.N0753

noncomputable section


@[ext]
structure d004714 (k : ℕ) where
  mean : Fin k → ℝ
  scale : Fin k → ℝ



def d004715 {k : ℕ} (shift dilation : ℝ)
    (s : _root_.GD.N0238.N0754.d004714 k) : _root_.GD.N0238.N0754.d004714 k where
  mean i := shift + dilation * s.mean i
  scale i := dilation * s.scale i


def d004716 {k : ℕ} (s : _root_.GD.N0238.N0754.d004714 k) : Prop :=
  ∀ i, 0 ≤ s.scale i


abbrev d004717 (k : ℕ) :=
  (Fin k → ℝ) × (Fin k → ℝ)


def d004718 {k : ℕ} (anchor : Fin k) (s : _root_.GD.N0238.N0754.d004714 k) :
    _root_.GD.N0238.N0754.d004717 k :=
  (fun i ↦ s.mean i - s.mean anchor, s.scale)



theorem d004719 {k : ℕ} (anchor : Fin k)
    (shift dilation : ℝ) (s : _root_.GD.N0238.N0754.d004714 k) :
    _root_.GD.N0238.N0754.d004718 anchor (_root_.GD.N0238.N0754.d004715 shift dilation s) =
      dilation • _root_.GD.N0238.N0754.d004718 anchor s := by
  apply Prod.ext
  · funext i
    simp [_root_.GD.N0238.N0754.d004718, _root_.GD.N0238.N0754.d004715]
    ring
  · funext i
    simp [_root_.GD.N0238.N0754.d004718, _root_.GD.N0238.N0754.d004715]


theorem d004720 {k : ℕ} (anchor : Fin k)
    (s : _root_.GD.N0238.N0754.d004714 k) :
    (_root_.GD.N0238.N0754.d004718 anchor s).1 anchor = 0 := by
  simp [_root_.GD.N0238.N0754.d004718]


theorem d004721 {k : ℕ} {s : _root_.GD.N0238.N0754.d004714 k}
    (hs : _root_.GD.N0238.N0754.d004716 s) (shift dilation : ℝ) (hdilation : 0 ≤ dilation) :
    _root_.GD.N0238.N0754.d004716 (_root_.GD.N0238.N0754.d004715 shift dilation s) := by
  intro i
  exact mul_nonneg hdilation (hs i)



def d004722 {k : ℕ} (anchor : Fin k)
    (z : _root_.GD.N0238.N0754.d004717 k) : Prop :=
  z.1 anchor = 0 ∧ ∀ i, 0 ≤ z.2 i

theorem d004723 {k : ℕ} (anchor : Fin k)
    {s : _root_.GD.N0238.N0754.d004714 k} (hs : _root_.GD.N0238.N0754.d004716 s) :
    _root_.GD.N0238.N0754.d004722 anchor (_root_.GD.N0238.N0754.d004718 anchor s) := by
  exact ⟨_root_.GD.N0238.N0754.d004720 anchor s, hs⟩


theorem d004724 {k : ℕ} (anchor : Fin k)
    {z : _root_.GD.N0238.N0754.d004717 k} (hz : _root_.GD.N0238.N0754.d004722 anchor z)
    (a : ℝ) (ha : 0 ≤ a) :
    _root_.GD.N0238.N0754.d004722 anchor (a • z) := by
  constructor
  · change a * z.1 anchor = 0
    rw [hz.1, mul_zero]
  · intro i
    change 0 ≤ a * z.2 i
    exact mul_nonneg ha (hz.2 i)




abbrev d004725 (k : ℕ) (anchor : Fin k) :=
  {u : _root_.GD.N0238.N0753.d004398 (_root_.GD.N0238.N0754.d004717 k) //
    _root_.GD.N0238.N0754.d004722 anchor (u : _root_.GD.N0238.N0754.d004717 k)}


def d004726 {k : ℕ} (anchor : Fin k)
    (z : _root_.GD.N0238.N0754.d004717 k) (hz0 : z ≠ 0)
    (hz : _root_.GD.N0238.N0754.d004722 anchor z) : _root_.GD.N0238.N0754.d004725 k anchor :=
  ⟨_root_.GD.N0238.N0753.d004399 z hz0, by
    change _root_.GD.N0238.N0754.d004722 anchor ((‖z‖⁻¹ : ℝ) • z)
    exact _root_.GD.N0238.N0754.d004724 anchor hz ‖z‖⁻¹
      (inv_nonneg.mpr (norm_nonneg z))⟩


theorem d004727 {k : ℕ} (anchor : Fin k)
    (z : _root_.GD.N0238.N0754.d004717 k) (hz0 : z ≠ 0)
    (hz : _root_.GD.N0238.N0754.d004722 anchor z) (a : ℝ) (ha : 0 < a) :
    _root_.GD.N0238.N0754.d004726 anchor (a • z) (smul_ne_zero ha.ne' hz0)
        (_root_.GD.N0238.N0754.d004724 anchor hz a ha.le) =
      _root_.GD.N0238.N0754.d004726 anchor z hz0 hz := by
  apply Subtype.ext
  exact _root_.GD.N0238.N0753.d004400 a ha z hz0


theorem d004728 {k : ℕ} (anchor : Fin k)
    (z : _root_.GD.N0238.N0754.d004717 k) (hz0 : z ≠ 0)
    (hz : _root_.GD.N0238.N0754.d004722 anchor z) :
    ‖z‖ •
        ((_root_.GD.N0238.N0754.d004726 anchor z hz0 hz : _root_.GD.N0238.N0754.d004725 k anchor) :
          _root_.GD.N0238.N0754.d004717 k) = z := by
  exact _root_.GD.N0238.N0753.d004408 z hz0


def d004729 {k : ℕ} (anchor : Fin k)
    (f : _root_.GD.N0238.N0754.d004717 k → ℝ) : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ z, _root_.GD.N0238.N0754.d004722 anchor z →
    f (a • z) = a * f z


theorem d004730 {k : ℕ}
    (anchor : Fin k) (f : _root_.GD.N0238.N0754.d004717 k → ℝ)
    (hf : _root_.GD.N0238.N0754.d004729 anchor f) :
    f 0 = 0 := by
  have hcone : _root_.GD.N0238.N0754.d004722 anchor (0 : _root_.GD.N0238.N0754.d004717 k) := by
    constructor <;> simp
  have htwo := hf 2 (by norm_num) 0 hcone
  simp only [smul_zero] at htwo
  linarith




theorem d004731 {k : ℕ}
    (anchor : Fin k) (f g : _root_.GD.N0238.N0754.d004717 k → ℝ)
    (hf : _root_.GD.N0238.N0754.d004729 anchor f)
    (hg : _root_.GD.N0238.N0754.d004729 anchor g)
    (hcarrier : ∀ u : _root_.GD.N0238.N0754.d004725 k anchor,
      f (u : _root_.GD.N0238.N0754.d004717 k) = g (u : _root_.GD.N0238.N0754.d004717 k)) :
    ∀ z, _root_.GD.N0238.N0754.d004722 anchor z → f z = g z := by
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    rw [_root_.GD.N0238.N0754.d004730 anchor f hf,
      _root_.GD.N0238.N0754.d004730 anchor g hg]
  · let u : _root_.GD.N0238.N0754.d004725 k anchor :=
      _root_.GD.N0238.N0754.d004726 anchor z hz0 hz
    have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hucone : _root_.GD.N0238.N0754.d004722 anchor
        (u : _root_.GD.N0238.N0754.d004717 k) := u.property
    have hfu := hf ‖z‖ hnorm (u : _root_.GD.N0238.N0754.d004717 k) hucone
    have hgu := hg ‖z‖ hnorm (u : _root_.GD.N0238.N0754.d004717 k) hucone
    have hreconstruct :
        ‖z‖ • (u : _root_.GD.N0238.N0754.d004717 k) = z := by
      exact _root_.GD.N0238.N0754.d004728 anchor z hz0 hz
    rw [hreconstruct] at hfu hgu
    calc
      f z = ‖z‖ * f (u : _root_.GD.N0238.N0754.d004717 k) := hfu
      _ = ‖z‖ * g (u : _root_.GD.N0238.N0754.d004717 k) := by rw [hcarrier u]
      _ = g z := hgu.symm

end

end GD.N0238.N0754

#print axioms _root_.GD.N0238.N0754.d004719
#print axioms _root_.GD.N0238.N0754.d004727
#print axioms _root_.GD.N0238.N0754.d004731
