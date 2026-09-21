import GD.Module0597










set_option autoImplicit false
set_option warningAsError true

open Set

namespace GD.N0106.N0428.N0766.N1691
noncomputable section

open _root_.GD.N0118



theorem d024067 (c w x : ℝ) (hw : 0 < w) :
    _root_.GD.N0118.d008582 c w x = w⁻¹ * max (1 - |x - c| / w) 0 := by
  by_cases hxc : x ≤ c
  · have hR : x ∉ Ioc c (c + w) := by
      intro hx
      exact (not_lt_of_ge hxc) hx.1
    by_cases hxleft : c - w < x
    · have hL : x ∈ Ioc (c - w) c := ⟨hxleft, hxc⟩
      have harg : 0 ≤ 1 - |x - c| / w := by
        apply sub_nonneg.mpr
        rw [abs_of_nonpos (sub_nonpos.mpr hxc)]
        apply (div_le_one hw).mpr
        linarith
      simp only [_root_.GD.N0118.d008582, indicator_of_mem hL, indicator_of_notMem hR,
        add_zero, max_eq_left harg]
      rw [abs_of_nonpos (sub_nonpos.mpr hxc)]
      unfold _root_.GD.N0118.d008580
      field_simp [hw.ne']
      <;> ring
    · have hL : x ∉ Ioc (c - w) c := fun hx => hxleft hx.1
      have harg : 1 - |x - c| / w ≤ 0 := by
        apply sub_nonpos.mpr
        rw [abs_of_nonpos (sub_nonpos.mpr hxc)]
        apply (one_le_div hw).mpr
        linarith
      simp only [_root_.GD.N0118.d008582, indicator_of_notMem hL, indicator_of_notMem hR,
        zero_add, max_eq_right harg, mul_zero]
  · have hcx : c < x := lt_of_not_ge hxc
    have hL : x ∉ Ioc (c - w) c := fun hx => hxc hx.2
    by_cases hxright : x ≤ c + w
    · have hR : x ∈ Ioc c (c + w) := ⟨hcx, hxright⟩
      have harg : 0 ≤ 1 - |x - c| / w := by
        apply sub_nonneg.mpr
        rw [abs_of_nonneg (sub_nonneg.mpr hcx.le)]
        apply (div_le_one hw).mpr
        linarith
      simp only [_root_.GD.N0118.d008582, indicator_of_notMem hL, indicator_of_mem hR,
        zero_add, max_eq_left harg]
      rw [abs_of_nonneg (sub_nonneg.mpr hcx.le)]
      unfold _root_.GD.N0118.d008581
      field_simp [hw.ne']
      <;> ring
    · have hR : x ∉ Ioc c (c + w) := fun hx => hxright hx.2
      have harg : 1 - |x - c| / w ≤ 0 := by
        apply sub_nonpos.mpr
        rw [abs_of_nonneg (sub_nonneg.mpr hcx.le)]
        apply (one_le_div hw).mpr
        linarith
      simp only [_root_.GD.N0118.d008582, indicator_of_notMem hL, indicator_of_notMem hR,
        zero_add, max_eq_right harg, mul_zero]


theorem d024068 (c w : ℝ) (hw : 0 < w) : Continuous (_root_.GD.N0118.d008582 c w) := by
  have heq : _root_.GD.N0118.d008582 c w = fun x => w⁻¹ * max (1 - |x - c| / w) 0 :=
    funext fun x => _root_.GD.N0106.N0428.N0766.N1691.d024067 c w x hw
  rw [heq]
  exact continuous_const.mul
    ((continuous_const.sub ((continuous_id.sub continuous_const).abs.div_const w)).max
      continuous_const)


theorem d024069 (c₁ c₂ w : ℝ) (hw : 0 < w) :
    Continuous (_root_.GD.N0118.d008583 c₁ c₂ w) :=
  ((_root_.GD.N0106.N0428.N0766.N1691.d024068 c₁ w hw).comp continuous_fst).mul
    ((_root_.GD.N0106.N0428.N0766.N1691.d024068 c₂ w hw).comp continuous_snd)

theorem d024070 (c w x : ℝ) (hw : 0 < w) : 0 ≤ _root_.GD.N0118.d008582 c w x := by
  rw [_root_.GD.N0106.N0428.N0766.N1691.d024067 c w x hw]
  exact mul_nonneg (inv_nonneg.mpr hw.le) (le_max_right _ _)


theorem d024071 (c w x : ℝ) (hw : 0 < w) : _root_.GD.N0118.d008582 c w x ≤ w⁻¹ := by
  rw [_root_.GD.N0106.N0428.N0766.N1691.d024067 c w x hw]
  have harg : 1 - |x - c| / w ≤ 1 := by
    have hq : 0 ≤ |x - c| / w := div_nonneg (abs_nonneg _) hw.le
    linarith
  calc
    _ ≤ w⁻¹ * 1 := mul_le_mul_of_nonneg_left
      (max_le harg zero_le_one) (inv_nonneg.mpr hw.le)
    _ = _ := mul_one _

theorem d024072 (c₁ c₂ w : ℝ) (p : ℝ × ℝ) (hw : 0 < w) :
    0 ≤ _root_.GD.N0118.d008583 c₁ c₂ w p :=
  mul_nonneg (_root_.GD.N0106.N0428.N0766.N1691.d024070 c₁ w p.1 hw) (_root_.GD.N0106.N0428.N0766.N1691.d024070 c₂ w p.2 hw)

theorem d024073 (c₁ c₂ w : ℝ) (p : ℝ × ℝ) (hw : 0 < w) :
    _root_.GD.N0118.d008583 c₁ c₂ w p ≤ (w⁻¹) ^ 2 := by
  change _root_.GD.N0118.d008582 c₁ w p.1 * _root_.GD.N0118.d008582 c₂ w p.2 ≤ (w⁻¹) ^ 2
  simpa only [pow_two] using mul_le_mul
    (_root_.GD.N0106.N0428.N0766.N1691.d024071 c₁ w p.1 hw) (_root_.GD.N0106.N0428.N0766.N1691.d024071 c₂ w p.2 hw)
    (_root_.GD.N0106.N0428.N0766.N1691.d024070 c₂ w p.2 hw) (inv_nonneg.mpr hw.le)


theorem d024074 (c w x : ℝ) (hw : 0 < w) :
    _root_.GD.N0118.d008582 (1 - c) w (1 - x) = _root_.GD.N0118.d008582 c w x := by
  rw [_root_.GD.N0106.N0428.N0766.N1691.d024067 (1 - c) w (1 - x) hw, _root_.GD.N0106.N0428.N0766.N1691.d024067 c w x hw]
  rw [show (1 - x) - (1 - c) = -(x - c) by ring, abs_neg]


theorem d024075 (c₁ c₂ w : ℝ) (p : ℝ × ℝ) (hw : 0 < w) :
    _root_.GD.N0118.d008583 (1 - c₁) c₂ w (1 - p.1, p.2) = _root_.GD.N0118.d008583 c₁ c₂ w p := by
  change _root_.GD.N0118.d008582 (1 - c₁) w (1 - p.1) * _root_.GD.N0118.d008582 c₂ w p.2 =
    _root_.GD.N0118.d008582 c₁ w p.1 * _root_.GD.N0118.d008582 c₂ w p.2
  rw [_root_.GD.N0106.N0428.N0766.N1691.d024074 c₁ w p.1 hw]



theorem d024076 (c w x : ℝ) (hw : 0 ≤ w)
    (hx : x ∉ Icc (c - w) (c + w)) : _root_.GD.N0118.d008582 c w x = 0 := by
  have hxL : x ∉ Ioc (c - w) c := by
    intro h
    exact hx ⟨h.1.le, h.2.trans (by linarith)⟩
  have hxR : x ∉ Ioc c (c + w) := by
    intro h
    exact hx ⟨by linarith [h.1], h.2⟩
  simp [_root_.GD.N0118.d008582, hxL, hxR]



theorem d024077 (c w : ℝ) (hw : 0 ≤ w) :
    tsupport (_root_.GD.N0118.d008582 c w) ⊆ Icc (c - w) (c + w) := by
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  change _root_.GD.N0118.d008582 c w x ≠ 0 at hx
  by_contra hnot
  exact hx (_root_.GD.N0106.N0428.N0766.N1691.d024076 c w x hw hnot)

theorem d024078 (c w : ℝ) (hw : 0 ≤ w) :
    HasCompactSupport (_root_.GD.N0118.d008582 c w) := by
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (_root_.GD.N0106.N0428.N0766.N1691.d024077 c w hw)



theorem d024079 (c₁ c₂ w : ℝ) (hw : 0 ≤ w) :
    tsupport (_root_.GD.N0118.d008583 c₁ c₂ w) ⊆
      Icc (c₁ - w) (c₁ + w) ×ˢ Icc (c₂ - w) (c₂ + w) := by
  apply closure_minimal ?_ (isClosed_Icc.prod isClosed_Icc)
  intro p hp
  change _root_.GD.N0118.d008583 c₁ c₂ w p ≠ 0 at hp
  constructor
  · by_contra hnot
    apply hp
    simp only [_root_.GD.N0118.d008583, _root_.GD.N0106.N0428.N0766.N1691.d024076 c₁ w p.1 hw hnot, zero_mul]
  · by_contra hnot
    apply hp
    simp only [_root_.GD.N0118.d008583, _root_.GD.N0106.N0428.N0766.N1691.d024076 c₂ w p.2 hw hnot, mul_zero]

theorem d024080 (c₁ c₂ w : ℝ) (hw : 0 ≤ w) :
    HasCompactSupport (_root_.GD.N0118.d008583 c₁ c₂ w) := by
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (isClosed_tsupport _)
    (_root_.GD.N0106.N0428.N0766.N1691.d024079 c₁ c₂ w hw)



theorem d024081 (c₁ c₂ w : ℝ) (hw : 0 ≤ w)
    (hleft : 0 < c₁ - w) (hright : c₁ + w < 1) (hbottom : 0 < c₂ - w) :
    tsupport (_root_.GD.N0118.d008583 c₁ c₂ w) ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ) := by
  intro p hp
  have h := _root_.GD.N0106.N0428.N0766.N1691.d024079 c₁ c₂ w hw hp
  exact ⟨⟨lt_of_lt_of_le hleft h.1.1, lt_of_le_of_lt h.1.2 hright⟩,
    lt_of_lt_of_le hbottom h.2.1⟩

end
end GD.N0106.N0428.N0766.N1691

#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024067
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024068
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024069
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024070
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024071
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024072
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024073
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024074
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024075
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024076
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024077
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024078
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024079
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024080
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024081
