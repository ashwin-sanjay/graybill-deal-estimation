import Mathlib













noncomputable section

namespace GD.N0109

def d006097 (c d h s t : ℝ) : ℝ :=
  c + d * s + h * t

def d006098 (a c d h r s t : ℝ) : ℝ :=
  (a + s) * _root_.GD.N0109.d006097 c d h s t ^ (-r)

def d006099 (a c d h r s t : ℝ) : ℝ :=
  _root_.GD.N0109.d006097 c d h s t ^ (-r) +
    -((a + s) * (d * r * _root_.GD.N0109.d006097 c d h s t ^ (-r - 1)))

def d006100 (a c d h r s t : ℝ) : ℝ :=
  -((a + s) * (h * r * _root_.GD.N0109.d006097 c d h s t ^ (-r - 1)))

theorem d006101 (c d h s t : ℝ) :
    HasDerivAt (fun x => _root_.GD.N0109.d006097 c d h x t) d s := by
  simpa [_root_.GD.N0109.d006097] using
    ((hasDerivAt_const s c).add
      ((hasDerivAt_id s).const_mul d)).add_const (h * t)

theorem d006102 (c d h s t : ℝ) :
    HasDerivAt (fun y => _root_.GD.N0109.d006097 c d h s y) h t := by
  simpa [_root_.GD.N0109.d006097, add_assoc] using
    ((hasDerivAt_id t).const_mul h).const_add (c + d * s)

theorem d006103
    (a c d h r s t : ℝ) (hN : _root_.GD.N0109.d006097 c d h s t ≠ 0) :
    HasDerivAt
      ((fun x : ℝ => a + x) * fun x => _root_.GD.N0109.d006097 c d h x t ^ (-r))
      (_root_.GD.N0109.d006099 a c d h r s t) s := by
  have hn :
      HasDerivAt (fun x : ℝ => a + x) 1 s := by
    simpa [add_comm] using (hasDerivAt_id s).add_const a
  have hp :=
    (_root_.GD.N0109.d006101 c d h s t).rpow_const
      (p := -r) (Or.inl hN)
  have hprod := hn.mul hp
  simpa [_root_.GD.N0109.d006099] using hprod

theorem d006104
    (a c d h r s t : ℝ) (hN : _root_.GD.N0109.d006097 c d h s t ≠ 0) :
    HasDerivAt
      ((fun _ : ℝ => a + s) * fun y => _root_.GD.N0109.d006097 c d h s y ^ (-r))
      (_root_.GD.N0109.d006100 a c d h r s t) t := by
  have hn : HasDerivAt (fun _ : ℝ => a + s) 0 t :=
    hasDerivAt_const t (a + s)
  have hp :=
    (_root_.GD.N0109.d006102 c d h s t).rpow_const
      (p := -r) (Or.inl hN)
  have hprod := hn.mul hp
  simpa [_root_.GD.N0109.d006100] using hprod

theorem d006105
    (a c d h r s t : ℝ) (hN : _root_.GD.N0109.d006097 c d h s t ≠ 0) :
    deriv ((fun x : ℝ => a + x) *
      fun x => _root_.GD.N0109.d006097 c d h x t ^ (-r)) s =
      _root_.GD.N0109.d006099 a c d h r s t :=
  (_root_.GD.N0109.d006103 a c d h r s t hN).deriv

theorem d006106
    (a c d h r s t : ℝ) (hN : _root_.GD.N0109.d006097 c d h s t ≠ 0) :
    deriv ((fun _ : ℝ => a + s) *
      fun y => _root_.GD.N0109.d006097 c d h s y ^ (-r)) t =
      _root_.GD.N0109.d006100 a c d h r s t :=
  (_root_.GD.N0109.d006104 a c d h r s t hN).deriv



theorem d006107
    {L N z P : ℝ} (hL : 0 < L) (hLN : L ≤ N)
    (hz : z ≤ 0) (hP : L ^ z ≤ P) :
    N ^ z ≤ P :=
  (Real.rpow_le_rpow_of_nonpos hL hLN hz).trans hP

theorem d006108
    {N z : ℝ} (hN : 1 ≤ N) (hz : z ≤ 0) :
    N ^ z ≤ 1 :=
  (Real.rpow_le_one_iff_of_pos (zero_lt_one.trans_le hN)).2
    (Or.inl ⟨hN, hz⟩)

theorem d006109
    {L N r : ℝ} {k J : ℕ}
    (hL0 : 0 < L) (hL1 : L ≤ 1) (hLN : L ≤ N)
    (hr : 0 ≤ r) (hJ : r + k ≤ J) :
    N ^ (-r - (k : ℕ)) ≤ (L ^ J)⁻¹ := by
  have hz : -r - (k : ℝ) ≤ 0 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  calc
    N ^ (-r - (k : ℕ))
        ≤ L ^ (-r - (k : ℕ)) :=
          Real.rpow_le_rpow_of_nonpos hL0 hLN hz
    _ ≤ L ^ (-(J : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hL0 hL1 (by
            have hj := neg_le_neg hJ
            norm_num at hj ⊢
            linarith)
    _ = (L ^ J)⁻¹ := by
      rw [Real.rpow_neg hL0.le, Real.rpow_natCast]

def d006110 (L r : ℝ) (k : ℕ) : ℝ :=
  if 1 ≤ L then 1 else (L ^ Nat.ceil (r + k))⁻¹

theorem d006111
    {L N r : ℝ} {k : ℕ}
    (hL0 : 0 < L) (hLN : L ≤ N) (hr : 0 ≤ r) :
    N ^ (-r - (k : ℕ)) ≤ _root_.GD.N0109.d006110 L r k := by
  unfold _root_.GD.N0109.d006110
  split_ifs with hL1
  · apply _root_.GD.N0109.d006108
    · exact hL1.trans hLN
    · have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
  · apply _root_.GD.N0109.d006109 hL0 (le_of_not_ge hL1) hLN hr
    exact Nat.le_ceil _



theorem d006112
    {α β e : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    |β - (α + β) * e| ≤ max α β := by
  rw [abs_le]
  constructor
  · calc
      -(max α β) ≤ -α := neg_le_neg (le_max_left α β)
      _ ≤ β - (α + β) * e := by nlinarith
  · calc
      β - (α + β) * e ≤ β := by nlinarith
      _ ≤ max α β := le_max_right α β

theorem d006113
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 ≤ e * (1 - e) / 2 ∧ e * (1 - e) / 2 ≤ 1 / 8 := by
  constructor
  · exact div_nonneg (mul_nonneg he0 (sub_nonneg.mpr he1)) (by norm_num)
  · nlinarith [sq_nonneg (e - 1 / 2)]

theorem d006114
    {α β s : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hs : |s| ≤ min α β / (4 * (α + β))) :
    |s| ≤ 1 / 8 := by
  have hν : 0 < α + β := add_pos hα hβ
  have hmin2 : 2 * min α β ≤ α + β := by
    calc
      2 * min α β = min α β + min α β := by ring
      _ ≤ α + β := add_le_add (min_le_left α β) (min_le_right α β)
  refine hs.trans ?_
  apply (div_le_iff₀ (mul_pos (by norm_num) hν)).2
  nlinarith

theorem d006115
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    α / (α + β) ∈ Set.Icc (0 : ℝ) 1 := by
  have hν : 0 < α + β := add_pos hα hβ
  constructor
  · exact div_nonneg hα.le hν.le
  · exact (div_le_one hν).2 (by linarith)

theorem d006116
    {α β e s : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs : |s| ≤ min α β / (4 * (α + β))) :
    |α / (α + β) - e + s| ≤ 9 / 8 := by
  have hell := _root_.GD.N0109.d006115 hα hβ
  have ha : |α / (α + β) - e| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hell.1, hell.2]
  calc
    |α / (α + β) - e + s|
        ≤ |α / (α + β) - e| + |s| := abs_add_le _ _
    _ ≤ 1 + 1 / 8 :=
      add_le_add ha (_root_.GD.N0109.d006114 hα hβ hs)
    _ = 9 / 8 := by ring

theorem d006117
    {c d h s t : ℝ}
    (hds : |d| * |s| ≤ c / 4) (hh : 0 ≤ h) (ht : 0 ≤ t) :
    3 * c / 4 ≤ _root_.GD.N0109.d006097 c d h s t := by
  have habs : |d * s| ≤ c / 4 := by
    simpa [abs_mul] using hds
  have hmul : -(c / 4) ≤ d * s := (abs_le.mp habs).1
  dsimp [_root_.GD.N0109.d006097]
  nlinarith [mul_nonneg hh ht]

theorem d006118 (α β : ℝ) :
    max α β * min α β = α * β := by
  rcases le_total α β with hab | hba
  · simp [max_eq_right hab, min_eq_left hab, mul_comm]
  · simp [max_eq_left hba, min_eq_right hba]

theorem d006119
    {α β e s t : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs : |s| ≤ min α β / (4 * (α + β)))
    (ht : 0 ≤ t) :
    3 * (α * β / (α + β)) / 4 ≤
      _root_.GD.N0109.d006097 (α * β / (α + β)) (β - (α + β) * e)
        (e * (1 - e) / 2) s t := by
  have hν : 0 < α + β := add_pos hα hβ
  have hd := _root_.GD.N0109.d006112 hα.le hβ.le he0 he1
  apply _root_.GD.N0109.d006117
  · calc
      |β - (α + β) * e| * |s|
          ≤ max α β * (min α β / (4 * (α + β))) :=
            mul_le_mul hd hs (abs_nonneg _)
              (hα.le.trans (le_max_left α β))
      _ = (α * β / (α + β)) / 4 := by
        rw [← _root_.GD.N0109.d006118 α β]
        field_simp
  · exact (_root_.GD.N0109.d006113 he0 he1).1
  · exact ht

theorem d006120
    {α β e s t r : ℝ} {k : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs : |s| ≤ min α β / (4 * (α + β)))
    (ht : 0 ≤ t) (hr : 0 ≤ r) :
    _root_.GD.N0109.d006097 (α * β / (α + β)) (β - (α + β) * e)
        (e * (1 - e) / 2) s t ^ (-r - (k : ℕ)) ≤
      _root_.GD.N0109.d006110
        (3 * (α * β / (α + β)) / 4) r k := by
  apply _root_.GD.N0109.d006111
  · have : 0 < α * β / (α + β) := div_pos (mul_pos hα hβ) (add_pos hα hβ)
    nlinarith
  · exact _root_.GD.N0109.d006119 hα hβ he0 he1 hs ht
  · exact hr

end GD.N0109
