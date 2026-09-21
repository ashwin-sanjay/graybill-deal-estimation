import GD.Module0603
import GD.Module0604
import GD.Module0397
















open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0131

noncomputable section

open _root_.GD.N0118
open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0135
open _root_.GD.N0115
open _root_.GD.N0111
open _root_.GD.N0132
open _root_.GD.N0146
open _root_.GD.N0113
open _root_.GD.N0113.d008651



def d008759 (p : ℚ × ℚ) : ℝ × ℝ :=
  ((p.1 : ℝ), (p.2 : ℝ))

def d008760 (center : ℚ × ℚ) (width : ℚ) :
    Set (ℝ × ℝ) :=
  {p |
    |p.1 - (center.1 : ℝ)| < (width : ℝ) ∧
      |p.2 - (center.2 : ℝ)| < (width : ℝ)}

theorem d008761 (center : ℚ × ℚ) (width : ℚ) :
    IsOpen (_root_.GD.N0131.d008760 center width) := by
  exact
    (isOpen_lt
      (continuous_fst.sub continuous_const).abs
      continuous_const).inter
    (isOpen_lt
      (continuous_snd.sub continuous_const).abs
      continuous_const)

theorem d008762
    (center p : ℚ × ℚ) (width : ℚ) :
    _root_.GD.N0131.d008759 p ∈ _root_.GD.N0131.d008760 center width ↔
      _root_.GD.N0115.d006631 center width p := by
  unfold _root_.GD.N0131.d008759 _root_.GD.N0131.d008760 _root_.GD.N0115.d006631
  constructor
  · rintro ⟨h₁, h₂⟩
    simp only [Prod.fst, Prod.snd] at h₁ h₂
    constructor
    · exact_mod_cast h₁
    · exact_mod_cast h₂
  · rintro ⟨h₁, h₂⟩
    constructor
    · change |(p.1 : ℝ) - (center.1 : ℝ)| < (width : ℝ)
      exact_mod_cast h₁
    · change |(p.2 : ℝ) - (center.2 : ℝ)| < (width : ℝ)
      exact_mod_cast h₂

theorem d008763 : DenseRange _root_.GD.N0131.d008759 := by
  change DenseRange
    (Prod.map (fun q : ℚ => (q : ℝ)) (fun q : ℚ => (q : ℝ)))
  exact Rat.denseRange_cast.prodMap Rat.denseRange_cast





theorem d008764
    (f : ℝ × ℝ → ℝ)
    (center : ℚ × ℚ) (width lower upper : ℚ)
    (hcont :
      ∀ x ∈ _root_.GD.N0131.d008760 center width, ContinuousAt f x)
    (hrat :
      ∀ p : ℚ × ℚ, _root_.GD.N0115.d006631 center width p →
        (lower : ℝ) ≤ f (_root_.GD.N0131.d008759 p) ∧
          f (_root_.GD.N0131.d008759 p) ≤ (upper : ℝ))
    (x : ℝ × ℝ) (hx : x ∈ _root_.GD.N0131.d008760 center width) :
    (lower : ℝ) ≤ f x ∧ f x ≤ (upper : ℝ) := by
  constructor
  · by_contra h
    have hlt : f x < (lower : ℝ) := lt_of_not_ge h
    have hpre :
        f ⁻¹' Iio (lower : ℝ) ∈ 𝓝 x :=
      (hcont x hx).preimage_mem_nhds (isOpen_Iio.mem_nhds hlt)
    have hbox : _root_.GD.N0131.d008760 center width ∈ 𝓝 x :=
      (_root_.GD.N0131.d008761 center width).mem_nhds hx
    obtain ⟨U, hUsub, hUopen, hxU⟩ :=
      mem_nhds_iff.mp (inter_mem hbox hpre)
    obtain ⟨p, hpU⟩ :=
      _root_.GD.N0131.d008763.exists_mem_open hUopen ⟨x, hxU⟩
    have hp := hUsub hpU
    have hpbox : _root_.GD.N0115.d006631 center width p :=
      (_root_.GD.N0131.d008762 center p width).mp hp.1
    exact (not_lt_of_ge (hrat p hpbox).1) hp.2
  · by_contra h
    have hlt : (upper : ℝ) < f x := lt_of_not_ge h
    have hpre :
        f ⁻¹' Ioi (upper : ℝ) ∈ 𝓝 x :=
      (hcont x hx).preimage_mem_nhds (isOpen_Ioi.mem_nhds hlt)
    have hbox : _root_.GD.N0131.d008760 center width ∈ 𝓝 x :=
      (_root_.GD.N0131.d008761 center width).mem_nhds hx
    obtain ⟨U, hUsub, hUopen, hxU⟩ :=
      mem_nhds_iff.mp (inter_mem hbox hpre)
    obtain ⟨p, hpU⟩ :=
      _root_.GD.N0131.d008763.exists_mem_open hUopen ⟨x, hxU⟩
    have hp := hUsub hpU
    have hpbox : _root_.GD.N0115.d006631 center width p :=
      (_root_.GD.N0131.d008762 center p width).mp hp.1
    exact (not_lt_of_ge (hrat p hpbox).2) hp.2



def d008765 (D : _root_.GD.N0134.d006518) (p : ℝ × ℝ) : ℝ :=
  p.1 ^ ((D.beta : ℝ) - 1) *
    (1 - p.1) ^ ((D.alpha : ℝ) - 1) *
    p.2 ^ ((1 : ℝ) / 2)

def d008766 (D : _root_.GD.N0134.d006518) (p : ℚ × ℚ) : ℝ :=
  _root_.GD.N0131.d008765 D (_root_.GD.N0131.d008759 p)

def d008767
    (D : _root_.GD.N0134.d006518) (e : ℝ) (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0111.d006136 (D.d006522 : ℝ)
      ((D.beta : ℝ) - ((D.d006519 : ℚ) : ℝ) * e)
      (e * (1 - e) / 2)
      (p.1 - (D.d006520 : ℝ)) p.2 ^
    (-(D.d006524 : ℝ))

def d008768
    (D : _root_.GD.N0134.d006518) (e : ℝ) (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0113.d008651.d008730 D e p

theorem d008769
    (D : _root_.GD.N0134.d006518) (e : ℝ) :
    _root_.GD.N0131.d008768 D e =
      _root_.GD.N0113.d008651.d008730
        D e := by
  rfl

theorem d008770 (q : ℝ) :
    Measurable (fun x : ℝ => x ^ q) := by
  refine measurable_of_continuousOn_compl_singleton 0 ?_
  exact continuousOn_of_forall_continuousAt fun x (hx : x ≠ 0) =>
    Real.continuousAt_rpow_const x q (Or.inl hx)

theorem d008771 (D : _root_.GD.N0134.d006518) :
    Measurable (_root_.GD.N0131.d008765 D) := by
  unfold _root_.GD.N0131.d008765
  exact
    (((_root_.GD.N0131.d008770 _).comp measurable_fst).mul
      ((_root_.GD.N0131.d008770 _).comp
        (measurable_const.sub measurable_fst))).mul
      ((_root_.GD.N0131.d008770 _).comp measurable_snd)

theorem d008772 (D : _root_.GD.N0134.d006518) (e : ℝ) :
    Measurable (_root_.GD.N0131.d008767 D e) := by
  unfold _root_.GD.N0131.d008767 _root_.GD.N0111.d006136
  apply (_root_.GD.N0131.d008770 _).comp
  fun_prop

theorem d008773
    (D : _root_.GD.N0134.d006518) (e : ℝ) :
    Measurable (_root_.GD.N0131.d008768 D e) := by
  unfold _root_.GD.N0131.d008768
    _root_.GD.N0113.d008651.d008730
    _root_.GD.N0132.d006445
    _root_.GD.N0111.d006137
  apply Measurable.mul
  · fun_prop
  · apply (_root_.GD.N0131.d008770 _).comp
    unfold _root_.GD.N0111.d006136
    fun_prop

theorem d008774
    (D : _root_.GD.N0134.d006518) {p : ℝ × ℝ}
    (hL0 : 0 < p.1) (hL1 : p.1 < 1) (hF : 0 < p.2) :
    ContinuousAt (_root_.GD.N0131.d008765 D) p := by
  unfold _root_.GD.N0131.d008765
  exact
    ((continuousAt_fst.rpow_const (Or.inl hL0.ne')).mul
      ((continuousAt_const.sub continuousAt_fst).rpow_const
        (Or.inl (sub_pos.mpr hL1).ne'))).mul
      (continuousAt_snd.rpow_const (Or.inl hF.ne'))



theorem d008775
    {c w x : ℝ} (hw : 0 < w)
    (hx : _root_.GD.N0118.d008582 c w x ≠ 0) :
    |x - c| < w := by
  by_cases hL : x ∈ Ioc (c - w) c
  · rw [abs_lt]
    exact ⟨by linarith [hL.1], by linarith [hL.2]⟩
  · by_cases hR : x ∈ Ioc c (c + w)
    · have hne : c + w - x ≠ 0 := by
        intro hzero
        apply hx
        simp [_root_.GD.N0118.d008582, hL, hR, _root_.GD.N0118.d008581, hzero]
      rw [abs_lt]
      exact
        ⟨by linarith [hR.1],
          by
            have hstrict : x < c + w := by
              exact lt_of_le_of_ne hR.2 (Ne.symm (sub_ne_zero.mp hne))
            linarith⟩
    · exact False.elim (hx (by simp [_root_.GD.N0118.d008582, hL, hR]))

theorem d008776
    {c₁ c₂ w : ℝ} (hw : 0 < w) {x : ℝ × ℝ}
    (hx : _root_.GD.N0118.d008583 c₁ c₂ w x ≠ 0) :
    |x.1 - c₁| < w ∧ |x.2 - c₂| < w := by
  have hmul := mul_ne_zero_iff.mp hx
  exact
    ⟨_root_.GD.N0131.d008775 hw hmul.1,
      _root_.GD.N0131.d008775 hw hmul.2⟩

theorem d008777
    {rhoQ : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (i : _root_.GD.N0113.d008651.d008696 T) (x : ℝ × ℝ)
    (hx : T.d008697 i x ≠ 0) :
    x ∈ _root_.GD.N0131.d008760 (_root_.GD.N0115.d006635 (T.d008652 i)) T.width := by
  have hw : (0 : ℝ) < (T.width : ℝ) := by
    exact_mod_cast T.width_pos
  simpa [_root_.GD.N0131.d008760, _root_.GD.N0113.d008651.d008697, _root_.GD.N0115.d006635] using
    (_root_.GD.N0131.d008776 hw hx)

theorem d008778
    {rhoQ : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (i : _root_.GD.N0113.d008651.d008696 T) :
    _root_.GD.N0115.d006635 (T.d008652 i) ∈ _root_.GD.N0115.d006636 D k ∨
      _root_.GD.N0115.d006635 (T.d008652 i) ∈ _root_.GD.N0115.d006637 D k := by
  have hi : T.d008652 i ∈ _root_.GD.N0146.d008622 D k := by
    exact List.get_mem (_root_.GD.N0146.d008622 D k) i
  unfold _root_.GD.N0146.d008622 at hi
  by_cases hδ : _root_.GD.N0135.d006594 D = 0
  · rw [if_pos hδ] at hi
    exact Or.inr (List.mem_map_of_mem hi)
  · rw [if_neg hδ] at hi
    exact Or.inl (List.mem_map_of_mem hi)

theorem d008779
    (D : _root_.GD.N0134.d006518) (k : ℕ) :
    (4 : ℝ) * (_root_.GD.N0134.d006550 D k : ℝ) ≤
      _root_.GD.N0132.d006442 (D.alpha : ℝ) (D.beta : ℝ) := by
  rw [_root_.GD.N0113.d008651.d008728]
  unfold _root_.GD.N0132.d006443
  have hR :
      0 ≤ _root_.GD.N0132.d006442 (D.alpha : ℝ) (D.beta : ℝ) :=
    (_root_.GD.N0132.d006447
      (by exact_mod_cast D.alpha_pos)
      (by exact_mod_cast D.beta_pos)).le
  have hN : (1 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
    have hk : (0 : ℕ) < 2 ^ k := by positivity
    exact_mod_cast (show (1 : ℕ) ≤ 2 ^ k by omega)
  have hNpos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  calc
    4 *
        (_root_.GD.N0132.d006442 (D.alpha : ℝ) (D.beta : ℝ) /
          (4 * ((2 ^ k : ℕ) : ℝ)))
        =
      _root_.GD.N0132.d006442 (D.alpha : ℝ) (D.beta : ℝ) /
        ((2 ^ k : ℕ) : ℝ) := by field_simp
    _ ≤ _root_.GD.N0132.d006442 (D.alpha : ℝ) (D.beta : ℝ) := by
      exact (div_le_iff₀ hNpos).2 (by nlinarith)

theorem d008780
    {rhoQ : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (i : _root_.GD.N0113.d008651.d008696 T) (x : ℝ × ℝ)
    (hbox :
      x ∈ _root_.GD.N0131.d008760 (_root_.GD.N0115.d006635 (T.d008652 i)) T.width) :
    |x.1 - (D.d006520 : ℝ)|
        ≤ _root_.GD.N0132.d006442 (D.alpha : ℝ) (D.beta : ℝ)
      ∧ 0 < x.1 ∧ x.1 < 1 ∧ 0 < x.2 := by
  have hc :=
    _root_.GD.N0115.d006643 D k (_root_.GD.N0115.d006635 (T.d008652 i))
      (_root_.GD.N0131.d008778 T i)
  have hwH := T.width_le_generated.trans
    (_root_.GD.N0115.d006640 D k)
  have hwE := T.width_le_generated.trans
    (_root_.GD.N0115.d006641 D k)
  have hh := _root_.GD.N0134.d006555 D k
  have hη := _root_.GD.N0134.d006556 D k
  have hlambdaL := D.d006533
  have hlambdaR := D.d006534
  have hsum := D.d006529
  change
    |x.1 - ((_root_.GD.N0115.d006635 (T.d008652 i)).1 : ℝ)| < (T.width : ℝ) ∧
      |x.2 - ((_root_.GD.N0115.d006635 (T.d008652 i)).2 : ℝ)| < (T.width : ℝ)
    at hbox
  rw [abs_lt, abs_lt] at hbox
  rcases hbox with ⟨⟨hxL, hxU⟩, ⟨hfL, hfU⟩⟩
  have hdevQ :
      -(2 * _root_.GD.N0134.d006550 D k) ≤
          (_root_.GD.N0115.d006635 (T.d008652 i)).1 - D.d006520
        ∧
      (_root_.GD.N0115.d006635 (T.d008652 i)).1 - D.d006520 ≤
          2 * _root_.GD.N0134.d006550 D k := by
    constructor <;> linarith [hc.1, hc.2.1]
  have hdev :
      -((2 * _root_.GD.N0134.d006550 D k : ℚ) : ℝ) ≤
          ((_root_.GD.N0115.d006635 (T.d008652 i)).1 : ℝ) - (D.d006520 : ℝ)
        ∧
      ((_root_.GD.N0115.d006635 (T.d008652 i)).1 : ℝ) - (D.d006520 : ℝ) ≤
          ((2 * _root_.GD.N0134.d006550 D k : ℚ) : ℝ) := by
    exact_mod_cast hdevQ
  have hwHR : (T.width : ℝ) ≤ (_root_.GD.N0134.d006550 D k : ℝ) / 8 := by
    exact_mod_cast hwH
  have hs :
      |x.1 - (D.d006520 : ℝ)|
        ≤ (17 / 8 : ℝ) * (_root_.GD.N0134.d006550 D k : ℝ) := by
    rw [abs_le]
    constructor <;> push_cast at hdev ⊢ <;> linarith
  have hR := _root_.GD.N0131.d008779 D k
  have hsR :
      |x.1 - (D.d006520 : ℝ)|
        ≤ _root_.GD.N0132.d006442 (D.alpha : ℝ) (D.beta : ℝ) := by
    exact hs.trans (by
      have hhR : (0 : ℝ) < (_root_.GD.N0134.d006550 D k : ℝ) := by exact_mod_cast hh
      nlinarith)
  have hlambdaCastL : (D.d006523 : ℝ) ≤ (D.d006520 : ℝ) := by
    exact_mod_cast hlambdaL
  have hlambdaCastR : (D.d006523 : ℝ) ≤ (D.d006521 : ℝ) := by
    exact_mod_cast hlambdaR
  have hsumR :
      (D.d006520 : ℝ) + (D.d006521 : ℝ) = 1 := by
    exact_mod_cast hsum
  have hwER : (T.width : ℝ) ≤ (_root_.GD.N0134.d006551 D k : ℝ) / 8 := by
    exact_mod_cast hwE
  have hcenterF :
      (_root_.GD.N0134.d006551 D k : ℝ) ≤
        ((_root_.GD.N0115.d006635 (T.d008652 i)).2 : ℝ) := by
    exact_mod_cast hc.2.2
  have hstepLambda : (17 / 8 : ℝ) * (_root_.GD.N0134.d006550 D k : ℝ) <
      (D.d006523 : ℝ) := by
    unfold _root_.GD.N0134.d006550
    push_cast
    have hN : (1 : ℝ) ≤ ((_root_.GD.N0134.d006546 k : ℚ) : ℝ) := by
      exact_mod_cast _root_.GD.N0134.d006548 k
    have hlambdaPos : (0 : ℝ) < (D.d006523 : ℝ) := by
      exact_mod_cast D.d006532
    have hNp : (0 : ℝ) < ((_root_.GD.N0134.d006546 k : ℚ) : ℝ) := by
      exact_mod_cast _root_.GD.N0134.d006547 k
    rw [show
      (17 / 8 : ℝ) *
          ((D.d006523 : ℝ) /
            (16 * ((_root_.GD.N0134.d006546 k : ℚ) : ℝ))) =
        ((17 / 128 : ℝ) * (D.d006523 : ℝ)) /
          ((_root_.GD.N0134.d006546 k : ℚ) : ℝ) by ring]
    rw [div_lt_iff₀ hNp]
    nlinarith [hlambdaPos, hN]
  have hsides := (abs_le.mp hs)
  refine ⟨hsR, ?_, ?_, ?_⟩
  · linarith [hlambdaCastL, hstepLambda, hsides.1]
  · linarith [hlambdaCastR, hstepLambda, hsides.2]
  · have hηR : (0 : ℝ) < (_root_.GD.N0134.d006551 D k : ℝ) := by
      exact_mod_cast hη
    linarith

theorem d008781
    {rhoQ : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (i : _root_.GD.N0113.d008651.d008696 T) (x : ℝ × ℝ)
    (hx : T.d008697 i x ≠ 0) :
    |x.1 - (D.d006520 : ℝ)|
        ≤ _root_.GD.N0132.d006442 (D.alpha : ℝ) (D.beta : ℝ)
      ∧ 0 < x.1 ∧ x.1 < 1 ∧ 0 < x.2 :=
  _root_.GD.N0131.d008780 T i x
    (_root_.GD.N0131.d008777 T i x hx)

theorem d008782
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 (_root_.GD.N0131.d008766 D) D k)
    (i : _root_.GD.N0113.d008651.d008696 T) (x : ℝ × ℝ)
    (hx : T.d008697 i x ≠ 0) :
    ((T.boxes i).lower : ℝ) ≤ _root_.GD.N0131.d008765 D x ∧
      _root_.GD.N0131.d008765 D x ≤ ((T.boxes i).upper : ℝ) := by
  have hbox := _root_.GD.N0131.d008777 T i x hx
  apply _root_.GD.N0131.d008764
      (_root_.GD.N0131.d008765 D) (_root_.GD.N0115.d006635 (T.d008652 i)) T.width
      (T.boxes i).lower (T.boxes i).upper
  · intro y hy
    have hyPhysical :=
      _root_.GD.N0131.d008780 T i y hy
    exact _root_.GD.N0131.d008774 D
      hyPhysical.2.1 hyPhysical.2.2.1 hyPhysical.2.2.2
  · intro p hp
    simpa only [_root_.GD.N0131.d008766] using (T.boxes i).bounds p (by
      rw [T.center_exact i, T.width_exact i]
      exact hp)
  · exact hbox



theorem d008783
    {α β e r s t : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs : |s| ≤ _root_.GD.N0132.d006442 α β) (ht : 0 ≤ t) :
    HasDerivAt
      (fun u => _root_.GD.N0132.d006445 α β e r u t)
      (_root_.GD.N0109.d006099
        (α / (α + β) - e) (α * β / (α + β))
        (β - (α + β) * e) (e * (1 - e) / 2) r s t) s := by
  have hN :=
    (_root_.GD.N0132.d006453 hα hβ he0 he1 hs ht).ne'
  have h :=
    _root_.GD.N0109.d006103
      (α / (α + β) - e)
      (α * β / (α + β))
      (β - (α + β) * e)
      (e * (1 - e) / 2) r s t
      (by
        simpa [_root_.GD.N0109.d006097, _root_.GD.N0111.d006136] using hN)
  convert h using 1
  funext u
  rfl

theorem d008784
    {α β e r s t : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs : |s| ≤ _root_.GD.N0132.d006442 α β) (ht : 0 ≤ t) :
    HasDerivAt
      (fun u => _root_.GD.N0132.d006445 α β e r s u)
      (_root_.GD.N0109.d006100
        (α / (α + β) - e) (α * β / (α + β))
        (β - (α + β) * e) (e * (1 - e) / 2) r s t) t := by
  have hN :=
    (_root_.GD.N0132.d006453 hα hβ he0 he1 hs ht).ne'
  have h :=
    _root_.GD.N0109.d006104
      (α / (α + β) - e)
      (α * β / (α + β))
      (β - (α + β) * e)
      (e * (1 - e) / 2) r s t
      (by
        simpa [_root_.GD.N0109.d006097, _root_.GD.N0111.d006136] using hN)
  convert h using 1
  funext u
  rfl

theorem d008785
    (α β e r s t : ℝ) :
    _root_.GD.N0109.d006099
        (α / (α + β) - e) (α * β / (α + β))
        (β - (α + β) * e) (e * (1 - e) / 2) r s t =
      _root_.GD.N0132.d006446 α β e r s t 1 0 := by
  simp [_root_.GD.N0132.d006446, _root_.GD.N0111.d006141, _root_.GD.N0111.d006140, _root_.GD.N0111.d006138,
    _root_.GD.N0109.d006099,
    _root_.GD.N0109.d006097, _root_.GD.N0111.d006136]
  ring

theorem d008786
    (α β e r s t : ℝ) :
    _root_.GD.N0109.d006100
        (α / (α + β) - e) (α * β / (α + β))
        (β - (α + β) * e) (e * (1 - e) / 2) r s t =
      _root_.GD.N0132.d006446 α β e r s t 0 1 := by
  simp only [_root_.GD.N0132.d006446, _root_.GD.N0111.d006141, _root_.GD.N0111.d006140, _root_.GD.N0111.d006138,
    _root_.GD.N0109.d006100,
    _root_.GD.N0109.d006097, _root_.GD.N0111.d006136,
    Nat.zero_add, Nat.add_zero, Nat.cast_zero, Nat.cast_one,
    zero_mul, add_zero, sub_zero, pow_zero, pow_one, one_mul, mul_one]
  ring

theorem d008787
    {α β e r s₁ s₂ t : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r)
    (hs₁ : |s₁| ≤ _root_.GD.N0132.d006442 α β)
    (hs₂ : |s₂| ≤ _root_.GD.N0132.d006442 α β)
    (ht : 0 ≤ t) :
    |_root_.GD.N0132.d006445 α β e r s₁ t -
        _root_.GD.N0132.d006445 α β e r s₂ t|
      ≤ _root_.GD.N0111.d006160 α β r 1 0 * |s₁ - s₂| := by
  let B := _root_.GD.N0111.d006160 α β r 1 0
  let dS : ℝ → ℝ := fun u =>
    _root_.GD.N0109.d006099
      (α / (α + β) - e) (α * β / (α + β))
      (β - (α + β) * e) (e * (1 - e) / 2) r u t
  have hB : 0 ≤ B :=
    _root_.GD.N0132.d006467 1 0 hα hβ hr
  by_cases hle : s₂ ≤ s₁
  · have hderiv :
        ∀ u ∈ Icc s₂ s₁,
          HasDerivWithinAt
            (fun z => _root_.GD.N0132.d006445 α β e r z t)
            (dS u)
            (Icc s₂ s₁) u := by
      intro u hu
      have huR : |u| ≤ _root_.GD.N0132.d006442 α β := by
        rw [abs_le] at hs₁ hs₂ ⊢
        exact ⟨hs₂.1.trans hu.1, hu.2.trans hs₁.2⟩
      exact
        (_root_.GD.N0131.d008783 hα hβ he0 he1 huR ht
          (r := r)).hasDerivWithinAt
    have hbound :
        ∀ u ∈ Ico s₂ s₁,
          ‖dS u‖ ≤ B := by
      intro u hu
      rw [Real.norm_eq_abs]
      have huR : |u| ≤ _root_.GD.N0132.d006442 α β := by
        rw [abs_le] at hs₁ hs₂ ⊢
        exact ⟨hs₂.1.trans hu.1, hu.2.le.trans hs₁.2⟩
      rw [show dS u = _root_.GD.N0132.d006446 α β e r u t 1 0 by
        exact _root_.GD.N0131.d008785 α β e r u t]
      simpa [B, _root_.GD.N0132.d006442, _root_.GD.N0132.d006446] using
        (_root_.GD.N0111.d006168 hα hβ he0 he1
          (by simpa [_root_.GD.N0132.d006442] using huR) ht hr
          (p := 1) (q := 0))
    have hseg :=
      norm_image_sub_le_of_norm_deriv_le_segment'
        hderiv hbound s₁ ⟨hle, le_rfl⟩
    simpa [B, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)]
      using hseg
  · have hle' : s₁ ≤ s₂ := le_of_not_ge hle
    have hderiv :
        ∀ u ∈ Icc s₁ s₂,
          HasDerivWithinAt
            (fun z => _root_.GD.N0132.d006445 α β e r z t)
            (dS u)
            (Icc s₁ s₂) u := by
      intro u hu
      have huR : |u| ≤ _root_.GD.N0132.d006442 α β := by
        rw [abs_le] at hs₁ hs₂ ⊢
        exact ⟨hs₁.1.trans hu.1, hu.2.trans hs₂.2⟩
      exact
        (_root_.GD.N0131.d008783 hα hβ he0 he1 huR ht
          (r := r)).hasDerivWithinAt
    have hbound :
        ∀ u ∈ Ico s₁ s₂,
          ‖dS u‖ ≤ B := by
      intro u hu
      rw [Real.norm_eq_abs]
      have huR : |u| ≤ _root_.GD.N0132.d006442 α β := by
        rw [abs_le] at hs₁ hs₂ ⊢
        exact ⟨hs₁.1.trans hu.1, hu.2.le.trans hs₂.2⟩
      rw [show dS u = _root_.GD.N0132.d006446 α β e r u t 1 0 by
        exact _root_.GD.N0131.d008785 α β e r u t]
      simpa [B, _root_.GD.N0132.d006442, _root_.GD.N0132.d006446] using
        (_root_.GD.N0111.d006168 hα hβ he0 he1
          (by simpa [_root_.GD.N0132.d006442] using huR) ht hr
          (p := 1) (q := 0))
    have hseg :=
      norm_image_sub_le_of_norm_deriv_le_segment'
        hderiv hbound s₂ ⟨hle', le_rfl⟩
    have hseg' :
        |_root_.GD.N0132.d006445 α β e r s₂ t -
            _root_.GD.N0132.d006445 α β e r s₁ t|
          ≤ B * (s₂ - s₁) := by
      simpa [Real.norm_eq_abs] using hseg
    calc
      |_root_.GD.N0132.d006445 α β e r s₁ t -
          _root_.GD.N0132.d006445 α β e r s₂ t|
          =
        |_root_.GD.N0132.d006445 α β e r s₂ t -
          _root_.GD.N0132.d006445 α β e r s₁ t| := abs_sub_comm _ _
      _ ≤ B * (s₂ - s₁) := hseg'
      _ = _root_.GD.N0111.d006160 α β r 1 0 * |s₁ - s₂| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hle')]
        simp [B]

theorem d008788
    {α β e r s t₁ t₂ : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r)
    (hs : |s| ≤ _root_.GD.N0132.d006442 α β)
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) :
    |_root_.GD.N0132.d006445 α β e r s t₁ -
        _root_.GD.N0132.d006445 α β e r s t₂|
      ≤ _root_.GD.N0111.d006160 α β r 0 1 * |t₁ - t₂| := by
  let B := _root_.GD.N0111.d006160 α β r 0 1
  let dT : ℝ → ℝ := fun u =>
    _root_.GD.N0109.d006100
      (α / (α + β) - e) (α * β / (α + β))
      (β - (α + β) * e) (e * (1 - e) / 2) r s u
  have hB : 0 ≤ B :=
    _root_.GD.N0132.d006467 0 1 hα hβ hr
  by_cases hle : t₂ ≤ t₁
  · have hderiv :
        ∀ u ∈ Icc t₂ t₁,
          HasDerivWithinAt
            (fun z => _root_.GD.N0132.d006445 α β e r s z)
            (dT u)
            (Icc t₂ t₁) u := by
      intro u hu
      exact
        (_root_.GD.N0131.d008784 hα hβ he0 he1 hs
          (ht₂.trans hu.1) (r := r)).hasDerivWithinAt
    have hbound :
        ∀ u ∈ Ico t₂ t₁,
          ‖dT u‖ ≤ B := by
      intro u hu
      rw [Real.norm_eq_abs]
      rw [show dT u = _root_.GD.N0132.d006446 α β e r s u 0 1 by
        exact _root_.GD.N0131.d008786 α β e r s u]
      simpa [B, _root_.GD.N0132.d006442, _root_.GD.N0132.d006446] using
        (_root_.GD.N0111.d006168 hα hβ he0 he1
          (by simpa [_root_.GD.N0132.d006442] using hs)
          (ht₂.trans hu.1) hr (p := 0) (q := 1))
    have hseg :=
      norm_image_sub_le_of_norm_deriv_le_segment'
        hderiv hbound t₁ ⟨hle, le_rfl⟩
    simpa [B, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle)]
      using hseg
  · have hle' : t₁ ≤ t₂ := le_of_not_ge hle
    have hderiv :
        ∀ u ∈ Icc t₁ t₂,
          HasDerivWithinAt
            (fun z => _root_.GD.N0132.d006445 α β e r s z)
            (dT u)
            (Icc t₁ t₂) u := by
      intro u hu
      exact
        (_root_.GD.N0131.d008784 hα hβ he0 he1 hs
          (ht₁.trans hu.1) (r := r)).hasDerivWithinAt
    have hbound :
        ∀ u ∈ Ico t₁ t₂,
          ‖dT u‖ ≤ B := by
      intro u hu
      rw [Real.norm_eq_abs]
      rw [show dT u = _root_.GD.N0132.d006446 α β e r s u 0 1 by
        exact _root_.GD.N0131.d008786 α β e r s u]
      simpa [B, _root_.GD.N0132.d006442, _root_.GD.N0132.d006446] using
        (_root_.GD.N0111.d006168 hα hβ he0 he1
          (by simpa [_root_.GD.N0132.d006442] using hs)
          (ht₁.trans hu.1) hr (p := 0) (q := 1))
    have hseg :=
      norm_image_sub_le_of_norm_deriv_le_segment'
        hderiv hbound t₂ ⟨hle', le_rfl⟩
    have hseg' :
        |_root_.GD.N0132.d006445 α β e r s t₂ -
            _root_.GD.N0132.d006445 α β e r s t₁|
          ≤ B * (t₂ - t₁) := by
      simpa [Real.norm_eq_abs] using hseg
    calc
      |_root_.GD.N0132.d006445 α β e r s t₁ -
          _root_.GD.N0132.d006445 α β e r s t₂|
          =
        |_root_.GD.N0132.d006445 α β e r s t₂ -
          _root_.GD.N0132.d006445 α β e r s t₁| := abs_sub_comm _ _
      _ ≤ B * (t₂ - t₁) := hseg'
      _ = _root_.GD.N0111.d006160 α β r 0 1 * |t₁ - t₂| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hle')]
        simp [B]

theorem d008789
    {D : _root_.GD.N0134.d006518} {e : ℝ}
    {rhoQ : (ℚ × ℚ) → ℝ} {k : ℕ}
    {inversePower : ℚ}
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hmajor :
      _root_.GD.N0111.d006153
          (_root_.GD.N0111.d006159 (D.alpha : ℝ) (D.beta : ℝ))
          (D.d006524 : ℝ) 0 ≤ (inversePower : ℝ))
    (i : _root_.GD.N0113.d008651.d008696 T) (x : ℝ × ℝ)
    (hx : T.d008697 i x ≠ 0) :
    0 ≤ _root_.GD.N0131.d008767 D e x ∧
      _root_.GD.N0131.d008767 D e x ≤ (inversePower : ℝ) := by
  have hgeo := _root_.GD.N0131.d008781 T i x hx
  have hα : (0 : ℝ) < D.alpha := by exact_mod_cast D.alpha_pos
  have hβ : (0 : ℝ) < D.beta := by exact_mod_cast D.beta_pos
  have hr : (0 : ℝ) ≤ D.d006524 := by
    exact_mod_cast
      (show (0 : ℚ) ≤ D.d006524 from
        le_trans (by norm_num) (le_of_lt (_root_.GD.N0135.d006605 D)))
  have hell :
      (D.d006520 : ℝ) =
        (D.alpha : ℝ) / ((D.alpha : ℝ) + (D.beta : ℝ)) := by
    simp [_root_.GD.N0134.d006518.d006520, _root_.GD.N0134.d006518.d006519, Rat.cast_div]
  have hden :
      _root_.GD.N0111.d006159 (D.alpha : ℝ) (D.beta : ℝ) ≤
        _root_.GD.N0111.d006136 (D.d006522 : ℝ)
          ((D.beta : ℝ) - ((D.d006519 : ℚ) : ℝ) * e)
          (e * (1 - e) / 2)
          (x.1 - (D.d006520 : ℝ)) x.2 := by
    simpa [_root_.GD.N0134.d006518.d006522, _root_.GD.N0134.d006518.d006519, hell] using
      (_root_.GD.N0111.d006166 hα hβ he0 he1
        (by simpa [_root_.GD.N0132.d006442, hell] using hgeo.1)
        hgeo.2.2.2.le)
  have hL0 :
      0 < _root_.GD.N0111.d006159 (D.alpha : ℝ) (D.beta : ℝ) :=
    _root_.GD.N0111.d006167 hα hβ
  have hden0 : 0 ≤
      _root_.GD.N0111.d006136 (D.d006522 : ℝ)
        ((D.beta : ℝ) - ((D.d006519 : ℚ) : ℝ) * e)
        (e * (1 - e) / 2)
        (x.1 - (D.d006520 : ℝ)) x.2 :=
    hL0.le.trans hden
  constructor
  · exact Real.rpow_nonneg hden0 _
  · unfold _root_.GD.N0131.d008767
    simpa only [Nat.cast_zero, sub_zero] using
      ((_root_.GD.N0111.d006156 hL0 hden hr).trans
        hmajor)

theorem d008790
    {D : _root_.GD.N0134.d006518} {e : ℝ}
    {rhoQ : (ℚ × ℚ) → ℝ} {k : ℕ}
    {carrierBound : ℚ}
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hmajor :
      _root_.GD.N0111.d006160
          (D.alpha : ℝ) (D.beta : ℝ)
          (D.d006524 : ℝ) 0 0 ≤ (carrierBound : ℝ))
    (i : _root_.GD.N0113.d008651.d008696 T) (x : ℝ × ℝ)
    (hx : T.d008697 i x ≠ 0) :
    |_root_.GD.N0131.d008768 D e x| ≤ (carrierBound : ℝ) := by
  have hgeo := _root_.GD.N0131.d008781 T i x hx
  have hα : (0 : ℝ) < D.alpha := by exact_mod_cast D.alpha_pos
  have hβ : (0 : ℝ) < D.beta := by exact_mod_cast D.beta_pos
  have hr : (0 : ℝ) ≤ D.d006524 := by
    exact_mod_cast
      (show (0 : ℚ) ≤ D.d006524 from
        le_trans (by norm_num) (le_of_lt (_root_.GD.N0135.d006605 D)))
  have hbound :=
    _root_.GD.N0111.d006168 hα hβ he0 he1
      (by simpa [_root_.GD.N0132.d006442] using hgeo.1)
      hgeo.2.2.2.le hr (p := 0) (q := 0)
  rw [_root_.GD.N0131.d008769]
  simpa [_root_.GD.N0113.d008651.d008730,
    _root_.GD.N0132.d006446, _root_.GD.N0132.d006445, _root_.GD.N0111.d006148] using
      hbound.trans hmajor

theorem d008791
    {D : _root_.GD.N0134.d006518} {e : ℝ}
    {rhoQ : (ℚ × ℚ) → ℝ} {k : ℕ}
    {gradientBound : ℚ}
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hmajor :
      _root_.GD.N0111.d006160
          (D.alpha : ℝ) (D.beta : ℝ)
          (D.d006524 : ℝ) 1 0
        +
      _root_.GD.N0111.d006160
          (D.alpha : ℝ) (D.beta : ℝ)
          (D.d006524 : ℝ) 0 1
        ≤ (gradientBound : ℝ))
    (i : _root_.GD.N0113.d008651.d008696 T) (x : ℝ × ℝ)
    (hx : T.d008697 i x ≠ 0) :
    |_root_.GD.N0131.d008768 D e x -
        _root_.GD.N0131.d008768 D e (T.d008698 i)|
      ≤ (gradientBound : ℝ) * (T.width : ℝ) := by
  let α : ℝ := D.alpha
  let β : ℝ := D.beta
  let r : ℝ := D.d006524
  let sₓ : ℝ := x.1 - (D.d006520 : ℝ)
  let s₀ : ℝ := (T.d008698 i).1 - (D.d006520 : ℝ)
  let tₓ : ℝ := x.2
  let t₀ : ℝ := (T.d008698 i).2
  let Bₛ := _root_.GD.N0111.d006160 α β r 1 0
  let Bₜ := _root_.GD.N0111.d006160 α β r 0 1
  have hα : 0 < α := by
    dsimp [α]
    exact_mod_cast D.alpha_pos
  have hβ : 0 < β := by
    dsimp [β]
    exact_mod_cast D.beta_pos
  have hr : 0 ≤ r := by
    dsimp [r]
    exact_mod_cast
      (show (0 : ℚ) ≤ D.d006524 from
        le_trans (by norm_num) (le_of_lt (_root_.GD.N0135.d006605 D)))
  have hxgeo := _root_.GD.N0131.d008781 T i x hx
  have hcenterBox :
      T.d008698 i ∈
        _root_.GD.N0131.d008760 (_root_.GD.N0115.d006635 (T.d008652 i)) T.width := by
    have hw : (0 : ℝ) < (T.width : ℝ) := by
      exact_mod_cast T.width_pos
    simp [_root_.GD.N0131.d008760, _root_.GD.N0113.d008651.d008698, _root_.GD.N0115.d006635, hw]
  have h0geo :=
    _root_.GD.N0131.d008780 T i (T.d008698 i) hcenterBox
  have hsx : |sₓ| ≤ _root_.GD.N0132.d006442 α β := by
    simpa [sₓ, α, β] using hxgeo.1
  have hs0 : |s₀| ≤ _root_.GD.N0132.d006442 α β := by
    simpa [s₀, α, β] using h0geo.1
  have htx : 0 ≤ tₓ := by
    exact hxgeo.2.2.2.le
  have ht0 : 0 ≤ t₀ := by
    exact h0geo.2.2.2.le
  have hsbound :=
    _root_.GD.N0131.d008787 hα hβ he0 he1 hr
      hsx hs0 htx
  have htbound :=
    _root_.GD.N0131.d008788 hα hβ he0 he1 hr
      hs0 htx ht0
  have htri :
      |_root_.GD.N0132.d006445 α β e r sₓ tₓ -
          _root_.GD.N0132.d006445 α β e r s₀ t₀|
        ≤
      |_root_.GD.N0132.d006445 α β e r sₓ tₓ -
          _root_.GD.N0132.d006445 α β e r s₀ tₓ|
        +
      |_root_.GD.N0132.d006445 α β e r s₀ tₓ -
          _root_.GD.N0132.d006445 α β e r s₀ t₀| := by
    calc
      |_root_.GD.N0132.d006445 α β e r sₓ tₓ -
          _root_.GD.N0132.d006445 α β e r s₀ t₀|
          =
        |(_root_.GD.N0132.d006445 α β e r sₓ tₓ -
            _root_.GD.N0132.d006445 α β e r s₀ tₓ) +
          (_root_.GD.N0132.d006445 α β e r s₀ tₓ -
            _root_.GD.N0132.d006445 α β e r s₀ t₀)| := by
              congr 1
              ring
      _ ≤ _ := abs_add_le _ _
  have hbox := _root_.GD.N0131.d008777 T i x hx
  have hcoord₁ :
      |sₓ - s₀| < (T.width : ℝ) := by
    simpa [sₓ, s₀, _root_.GD.N0113.d008651.d008698, _root_.GD.N0115.d006635] using hbox.1
  have hcoord₂ :
      |tₓ - t₀| < (T.width : ℝ) := by
    simpa [tₓ, t₀, _root_.GD.N0113.d008651.d008698, _root_.GD.N0115.d006635] using hbox.2
  have hBs : 0 ≤ Bₛ :=
    _root_.GD.N0132.d006467 1 0 hα hβ hr
  have hBt : 0 ≤ Bₜ :=
    _root_.GD.N0132.d006467 0 1 hα hβ hr
  have hw : (0 : ℝ) < (T.width : ℝ) := by
    exact_mod_cast T.width_pos
  rw [_root_.GD.N0131.d008769]
  change
    |_root_.GD.N0132.d006445 α β e r sₓ tₓ -
        _root_.GD.N0132.d006445 α β e r s₀ t₀|
      ≤ (gradientBound : ℝ) * (T.width : ℝ)
  calc
    _ ≤
        |_root_.GD.N0132.d006445 α β e r sₓ tₓ -
            _root_.GD.N0132.d006445 α β e r s₀ tₓ|
          +
        |_root_.GD.N0132.d006445 α β e r s₀ tₓ -
            _root_.GD.N0132.d006445 α β e r s₀ t₀| := htri
    _ ≤ Bₛ * |sₓ - s₀| + Bₜ * |tₓ - t₀| :=
      add_le_add hsbound htbound
    _ ≤ (Bₛ + Bₜ) * (T.width : ℝ) := by
      calc
        Bₛ * |sₓ - s₀| + Bₜ * |tₓ - t₀|
            ≤ Bₛ * (T.width : ℝ) +
                Bₜ * (T.width : ℝ) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hcoord₁.le hBs)
                (mul_le_mul_of_nonneg_left hcoord₂.le hBt)
        _ = (Bₛ + Bₜ) * (T.width : ℝ) := by ring
    _ ≤ (gradientBound : ℝ) * (T.width : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (by simpa [Bₛ, Bₜ, α, β, r] using hmajor) hw.le



theorem d008792
    (D : _root_.GD.N0134.d006518) (k : ℕ) :
    (_root_.GD.N0115.d006636 D k).Nodup := by
  have hh := _root_.GD.N0134.d006555 D k
  have heta := _root_.GD.N0134.d006556 D k
  have h₁ :
      D.d006520 - _root_.GD.N0134.d006550 D k ≠ D.d006520 := by linarith
  have h₂ :
      D.d006520 - _root_.GD.N0134.d006550 D k ≠ D.d006520 + _root_.GD.N0134.d006550 D k := by
    linarith
  have h₃ :
      D.d006520 ≠ D.d006520 + _root_.GD.N0134.d006550 D k := by linarith
  have hf : _root_.GD.N0134.d006551 D k ≠ 2 * _root_.GD.N0134.d006551 D k := by linarith
  simp [_root_.GD.N0115.d006636, _root_.GD.N0135.d006607, _root_.GD.N0115.d006635,
    h₁, h₂, h₃, hf]

theorem d008793
    (D : _root_.GD.N0134.d006518) (k : ℕ) :
    (_root_.GD.N0115.d006637 D k).Nodup := by
  have hh := _root_.GD.N0134.d006555 D k
  have heta := _root_.GD.N0134.d006556 D k
  have h₁ :
      D.d006520 + _root_.GD.N0134.d006550 D k ≠ D.d006520 - _root_.GD.N0134.d006550 D k := by
    linarith
  have h₂ :
      D.d006520 + _root_.GD.N0134.d006550 D k ≠ D.d006520 + 2 * _root_.GD.N0134.d006550 D k := by
    linarith
  have h₃ :
      D.d006520 + _root_.GD.N0134.d006550 D k ≠ D.d006520 - 2 * _root_.GD.N0134.d006550 D k := by
    linarith
  have h₄ :
      D.d006520 - _root_.GD.N0134.d006550 D k ≠ D.d006520 + 2 * _root_.GD.N0134.d006550 D k := by
    linarith
  have h₅ :
      D.d006520 - _root_.GD.N0134.d006550 D k ≠ D.d006520 - 2 * _root_.GD.N0134.d006550 D k := by
    linarith
  have h₆ :
      D.d006520 + 2 * _root_.GD.N0134.d006550 D k ≠ D.d006520 - 2 * _root_.GD.N0134.d006550 D k := by
    linarith
  have hf : _root_.GD.N0134.d006551 D k ≠ 2 * _root_.GD.N0134.d006551 D k := by linarith
  simp [_root_.GD.N0115.d006637, _root_.GD.N0135.d006608, _root_.GD.N0115.d006635,
    h₁, h₂, h₃, h₄, h₅, h₆, hf]

theorem d008794
    (D : _root_.GD.N0134.d006518) (k : ℕ) :
    (_root_.GD.N0113.d008649 D k).Nodup := by
  unfold _root_.GD.N0113.d008649 _root_.GD.N0146.d008622
  by_cases hδ : _root_.GD.N0135.d006594 D = 0
  · rw [if_pos hδ]
    exact _root_.GD.N0131.d008793 D k
  · rw [if_neg hδ]
    exact _root_.GD.N0131.d008792 D k

theorem d008795
    {rhoQ : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rhoQ D k) :
    Function.Injective (fun i : _root_.GD.N0113.d008651.d008696 T =>
      _root_.GD.N0115.d006635 (T.d008652 i)) := by
  intro i j hij
  let i' : Fin (_root_.GD.N0113.d008649 D k).length :=
    ⟨i.val, by simpa [_root_.GD.N0113.d008649] using i.isLt⟩
  let j' : Fin (_root_.GD.N0113.d008649 D k).length :=
    ⟨j.val, by simpa [_root_.GD.N0113.d008649] using j.isLt⟩
  have hget :
      (_root_.GD.N0113.d008649 D k).get i' =
        (_root_.GD.N0113.d008649 D k).get j' := by
    simpa [_root_.GD.N0113.d008649, _root_.GD.N0113.d008651.d008652, i', j'] using hij
  have hij' : i' = j' :=
    (_root_.GD.N0131.d008794 D k).injective_get hget
  apply Fin.ext
  simpa [i', j'] using congrArg Fin.val hij'

theorem d008796
    {rhoQ : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (i j : _root_.GD.N0113.d008651.d008696 T) (hij : i ≠ j) :
    _root_.GD.N0134.d006550 D k ≤
        |(_root_.GD.N0115.d006635 (T.d008652 i)).1 -
          (_root_.GD.N0115.d006635 (T.d008652 j)).1|
      ∨
    _root_.GD.N0134.d006551 D k ≤
        |(_root_.GD.N0115.d006635 (T.d008652 i)).2 -
          (_root_.GD.N0115.d006635 (T.d008652 j)).2| := by
  have hcne :
      _root_.GD.N0115.d006635 (T.d008652 i) ≠ _root_.GD.N0115.d006635 (T.d008652 j) := by
    exact fun h => hij (_root_.GD.N0131.d008795 T h)
  by_cases hδ : _root_.GD.N0135.d006594 D = 0
  · apply _root_.GD.N0115.d006647 D k _ _ _ _ hcne
    · unfold _root_.GD.N0115.d006637
      apply List.mem_map_of_mem
      have hi := List.get_mem (_root_.GD.N0146.d008622 D k) i
      simpa only [_root_.GD.N0113.d008651.d008652, _root_.GD.N0146.d008622, hδ, if_pos] using hi
    · unfold _root_.GD.N0115.d006637
      apply List.mem_map_of_mem
      have hj := List.get_mem (_root_.GD.N0146.d008622 D k) j
      simpa only [_root_.GD.N0113.d008651.d008652, _root_.GD.N0146.d008622, hδ, if_pos] using hj
  · apply _root_.GD.N0115.d006646 D k _ _ _ _ hcne
    · unfold _root_.GD.N0115.d006636
      apply List.mem_map_of_mem
      have hi := List.get_mem (_root_.GD.N0146.d008622 D k) i
      simpa [_root_.GD.N0113.d008651.d008652, _root_.GD.N0146.d008622, hδ] using hi
    · unfold _root_.GD.N0115.d006636
      apply List.mem_map_of_mem
      have hj := List.get_mem (_root_.GD.N0146.d008622 D k) j
      simpa [_root_.GD.N0113.d008651.d008652, _root_.GD.N0146.d008622, hδ] using hj

theorem d008797
    {rhoQ : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rhoQ D k) :
    ∀ i j : _root_.GD.N0113.d008651.d008696 T, i ≠ j → ∀ x,
      T.d008697 i x * T.d008697 j x = 0 := by
  intro i j hij x
  by_contra hprod
  have hne := mul_ne_zero_iff.mp hprod
  have hi := _root_.GD.N0131.d008777 T i x hne.1
  have hj := _root_.GD.N0131.d008777 T j x hne.2
  have hsep := _root_.GD.N0131.d008796 T i j hij
  have hwH := T.width_le_generated.trans
    (_root_.GD.N0115.d006640 D k)
  have hwE := T.width_le_generated.trans
    (_root_.GD.N0115.d006641 D k)
  change
    |x.1 - ((_root_.GD.N0115.d006635 (T.d008652 i)).1 : ℝ)| < (T.width : ℝ) ∧
      |x.2 - ((_root_.GD.N0115.d006635 (T.d008652 i)).2 : ℝ)| < (T.width : ℝ)
    at hi
  change
    |x.1 - ((_root_.GD.N0115.d006635 (T.d008652 j)).1 : ℝ)| < (T.width : ℝ) ∧
      |x.2 - ((_root_.GD.N0115.d006635 (T.d008652 j)).2 : ℝ)| < (T.width : ℝ)
    at hj
  rcases hsep with hsep | hsep
  · have hsepR :
        (_root_.GD.N0134.d006550 D k : ℝ) ≤
          |((_root_.GD.N0115.d006635 (T.d008652 i)).1 : ℝ) -
            ((_root_.GD.N0115.d006635 (T.d008652 j)).1 : ℝ)| := by
      exact_mod_cast hsep
    have hwR : (T.width : ℝ) ≤ (_root_.GD.N0134.d006550 D k : ℝ) / 8 := by
      exact_mod_cast hwH
    have hstepPos : (0 : ℝ) < (_root_.GD.N0134.d006550 D k : ℝ) := by
      exact_mod_cast (_root_.GD.N0134.d006555 D k)
    have htri :
        |((_root_.GD.N0115.d006635 (T.d008652 i)).1 : ℝ) -
            ((_root_.GD.N0115.d006635 (T.d008652 j)).1 : ℝ)|
          ≤
        |x.1 - ((_root_.GD.N0115.d006635 (T.d008652 i)).1 : ℝ)| +
          |x.1 - ((_root_.GD.N0115.d006635 (T.d008652 j)).1 : ℝ)| := by
      calc
        |((_root_.GD.N0115.d006635 (T.d008652 i)).1 : ℝ) -
            ((_root_.GD.N0115.d006635 (T.d008652 j)).1 : ℝ)|
            =
          |-(x.1 - ((_root_.GD.N0115.d006635 (T.d008652 i)).1 : ℝ)) +
            (x.1 - ((_root_.GD.N0115.d006635 (T.d008652 j)).1 : ℝ))| := by
              congr 1
              ring
        _ ≤ _ := by
          simpa only [abs_neg] using
            abs_add_le
              (-(x.1 - ((_root_.GD.N0115.d006635 (T.d008652 i)).1 : ℝ)))
              (x.1 - ((_root_.GD.N0115.d006635 (T.d008652 j)).1 : ℝ))
    linarith [hi.1, hj.1, hstepPos]
  · have hsepR :
        (_root_.GD.N0134.d006551 D k : ℝ) ≤
          |((_root_.GD.N0115.d006635 (T.d008652 i)).2 : ℝ) -
            ((_root_.GD.N0115.d006635 (T.d008652 j)).2 : ℝ)| := by
      exact_mod_cast hsep
    have hwR : (T.width : ℝ) ≤ (_root_.GD.N0134.d006551 D k : ℝ) / 8 := by
      exact_mod_cast hwE
    have hstepPos : (0 : ℝ) < (_root_.GD.N0134.d006551 D k : ℝ) := by
      exact_mod_cast (_root_.GD.N0134.d006556 D k)
    have htri :
        |((_root_.GD.N0115.d006635 (T.d008652 i)).2 : ℝ) -
            ((_root_.GD.N0115.d006635 (T.d008652 j)).2 : ℝ)|
          ≤
        |x.2 - ((_root_.GD.N0115.d006635 (T.d008652 i)).2 : ℝ)| +
          |x.2 - ((_root_.GD.N0115.d006635 (T.d008652 j)).2 : ℝ)| := by
      calc
        |((_root_.GD.N0115.d006635 (T.d008652 i)).2 : ℝ) -
            ((_root_.GD.N0115.d006635 (T.d008652 j)).2 : ℝ)|
            =
          |-(x.2 - ((_root_.GD.N0115.d006635 (T.d008652 i)).2 : ℝ)) +
            (x.2 - ((_root_.GD.N0115.d006635 (T.d008652 j)).2 : ℝ))| := by
              congr 1
              ring
        _ ≤ _ := by
          simpa only [abs_neg] using
            abs_add_le
              (-(x.2 - ((_root_.GD.N0115.d006635 (T.d008652 i)).2 : ℝ)))
              (x.2 - ((_root_.GD.N0115.d006635 (T.d008652 j)).2 : ℝ))
    linarith [hi.2, hj.2, hstepPos]






theorem d008798
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 (_root_.GD.N0131.d008766 D) D k)
    (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (gradientBound carrierBound inversePower : ℚ)
    (hgradient :
      _root_.GD.N0111.d006160
          (D.alpha : ℝ) (D.beta : ℝ)
          (D.d006524 : ℝ) 1 0
        +
      _root_.GD.N0111.d006160
          (D.alpha : ℝ) (D.beta : ℝ)
          (D.d006524 : ℝ) 0 1
        ≤ (gradientBound : ℝ))
    (hcarrier :
      _root_.GD.N0111.d006160
          (D.alpha : ℝ) (D.beta : ℝ)
          (D.d006524 : ℝ) 0 0
        ≤ (carrierBound : ℝ))
    (hinverse :
      _root_.GD.N0111.d006153
          (_root_.GD.N0111.d006159 (D.alpha : ℝ) (D.beta : ℝ))
          (D.d006524 : ℝ) 0
        ≤ (inversePower : ℝ)) :
    _root_.GD.N0113.d008651.d008706 T
      (_root_.GD.N0131.d008765 D)
      (_root_.GD.N0131.d008768 D e)
      (_root_.GD.N0131.d008767 D e)
      gradientBound carrierBound inversePower where
  measurable_rho := _root_.GD.N0131.d008771 D
  measurable_carrier := _root_.GD.N0131.d008773 D e
  measurable_power := _root_.GD.N0131.d008772 D e
  tents_pairwise_disjoint := _root_.GD.N0131.d008797 T
  density_bounds := _root_.GD.N0131.d008782 T
  carrier_lipschitz :=
    _root_.GD.N0131.d008791 T he0 he1 hgradient
  carrier_abs :=
    _root_.GD.N0131.d008790 T he0 he1 hcarrier
  power_bounds :=
    _root_.GD.N0131.d008789 T he0 he1 hinverse






theorem d008799
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 (_root_.GD.N0131.d008766 D) D k)
    (gradientBound carrierBound inversePower : ℚ)
    (hgradient :
      _root_.GD.N0111.d006160
          (D.alpha : ℝ) (D.beta : ℝ)
          (D.d006524 : ℝ) 1 0
        +
      _root_.GD.N0111.d006160
          (D.alpha : ℝ) (D.beta : ℝ)
          (D.d006524 : ℝ) 0 1
        ≤ (gradientBound : ℝ))
    (hcarrier :
      _root_.GD.N0111.d006160
          (D.alpha : ℝ) (D.beta : ℝ)
          (D.d006524 : ℝ) 0 0
        ≤ (carrierBound : ℝ))
    (hinverse :
      _root_.GD.N0111.d006153
          (_root_.GD.N0111.d006159 (D.alpha : ℝ) (D.beta : ℝ))
          (D.d006524 : ℝ) 0
        ≤ (inversePower : ℝ)) :
    ∀ e ∈ Icc (0 : ℝ) 1,
      _root_.GD.N0113.d008651.d008706 T
        (_root_.GD.N0131.d008765 D)
        (_root_.GD.N0131.d008768 D e)
        (_root_.GD.N0131.d008767 D e)
        gradientBound carrierBound inversePower := by
  intro e he
  exact _root_.GD.N0131.d008798 T e he.1 he.2
    gradientBound carrierBound inversePower
    hgradient hcarrier hinverse

end

end GD.N0131
