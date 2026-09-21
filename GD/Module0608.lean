import GD.Module0606











open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0128

noncomputable section

open _root_.GD.N0118
open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0135
open _root_.GD.N0115
open _root_.GD.N0132
open _root_.GD.N0146
open _root_.GD.N0113
open _root_.GD.N0113.d008651
open _root_.GD.N0131

def d008801
    (D : _root_.GD.N0134.d006518) (k : ℕ)
    (i : Fin (_root_.GD.N0146.d008622 D k).length) : ℚ × ℚ :=
  _root_.GD.N0115.d006635 ((_root_.GD.N0146.d008622 D k).get i)

theorem d008802
    (D : _root_.GD.N0134.d006518) (k : ℕ)
    (i : Fin (_root_.GD.N0146.d008622 D k).length) :
    _root_.GD.N0128.d008801 D k i ∈ _root_.GD.N0115.d006636 D k ∨
      _root_.GD.N0128.d008801 D k i ∈ _root_.GD.N0115.d006637 D k := by
  let a : _root_.GD.N0135.d006593 := (_root_.GD.N0146.d008622 D k).get i
  have hi : a ∈ _root_.GD.N0146.d008622 D k := by
    exact List.get_mem _ _
  change _root_.GD.N0115.d006635 a ∈ _root_.GD.N0115.d006636 D k ∨
    _root_.GD.N0115.d006635 a ∈ _root_.GD.N0115.d006637 D k
  by_cases hdelta : _root_.GD.N0135.d006594 D = 0
  · simp only [_root_.GD.N0146.d008622, hdelta, if_pos] at hi
    exact Or.inr (List.mem_map_of_mem hi)
  · simp only [_root_.GD.N0146.d008622, hdelta, if_neg] at hi
    exact Or.inl (List.mem_map_of_mem hi)

theorem d008803
    (D : _root_.GD.N0134.d006518) (k : ℕ)
    (i : Fin (_root_.GD.N0146.d008622 D k).length) :
    0 < (_root_.GD.N0128.d008801 D k i).1 ∧
      (_root_.GD.N0128.d008801 D k i).1 < 1 ∧
      0 < (_root_.GD.N0128.d008801 D k i).2 := by
  apply _root_.GD.N0115.d006644 D k
      (_root_.GD.N0128.d008801 D k i) (_root_.GD.N0128.d008801 D k i)
      (_root_.GD.N0128.d008802 D k i)
  have hw := _root_.GD.N0115.d006639 D k
  simp [_root_.GD.N0115.d006631, hw]

theorem d008804
    (D : _root_.GD.N0134.d006518) (k : ℕ)
    (i : Fin (_root_.GD.N0146.d008622 D k).length) :
    0 <
      _root_.GD.N0131.d008765 D
        (_root_.GD.N0131.d008759 (_root_.GD.N0128.d008801 D k i)) := by
  have h := _root_.GD.N0128.d008803 D k i
  unfold _root_.GD.N0131.d008765 _root_.GD.N0131.d008759
  exact mul_pos
    (mul_pos
      (Real.rpow_pos_of_pos
        (by
          change (0 : ℝ) < ((_root_.GD.N0128.d008801 D k i).1 : ℝ)
          exact_mod_cast h.1) _)
      (Real.rpow_pos_of_pos
        (by
          have : (0 : ℝ) <
              1 - ((_root_.GD.N0128.d008801 D k i).1 : ℝ) := by
            exact_mod_cast (sub_pos.mpr h.2.1)
          exact this) _))
    (Real.rpow_pos_of_pos
      (by
        change (0 : ℝ) < ((_root_.GD.N0128.d008801 D k i).2 : ℝ)
        exact_mod_cast h.2.2) _)

theorem d008805
    (D : _root_.GD.N0134.d006518) (k : ℕ)
    (i : Fin (_root_.GD.N0146.d008622 D k).length) :
    ContinuousAt (_root_.GD.N0131.d008765 D)
      (_root_.GD.N0131.d008759 (_root_.GD.N0128.d008801 D k i)) := by
  have h := _root_.GD.N0128.d008803 D k i
  exact _root_.GD.N0131.d008774 D
    (by
      change (0 : ℝ) < ((_root_.GD.N0128.d008801 D k i).1 : ℝ)
      exact_mod_cast h.1)
    (by
      change ((_root_.GD.N0128.d008801 D k i).1 : ℝ) < 1
      exact_mod_cast h.2.1)
    (by
      change (0 : ℝ) < ((_root_.GD.N0128.d008801 D k i).2 : ℝ)
      exact_mod_cast h.2.2)






theorem d008806
    (f : ℝ × ℝ → ℝ) (center : ℚ × ℚ)
    (hcont : ContinuousAt f (_root_.GD.N0131.d008759 center))
    (hpos : 0 < f (_root_.GD.N0131.d008759 center))
    (eta wMax : ℚ) (heta : 0 < eta) (hwMax : 0 < wMax) :
    ∃ B : _root_.GD.N0115.d006632
        (fun p : ℚ × ℚ => f (_root_.GD.N0131.d008759 p)),
      B.center = center ∧ B.width ≤ wMax ∧
        _root_.GD.N0115.d006629 B.lower B.upper < eta := by
  let r : ℝ := f (_root_.GD.N0131.d008759 center)
  let delta : ℝ := min (r / 4) ((eta : ℝ) * r / 8)
  have hr : 0 < r := hpos
  have hetaR : (0 : ℝ) < (eta : ℝ) := by exact_mod_cast heta
  have hdelta : 0 < delta := by
    exact lt_min (div_pos hr (by norm_num))
      (div_pos (mul_pos hetaR hr) (by norm_num))
  obtain ⟨lower : ℚ, hlowerL, hlowerU⟩ :
      ∃ q : ℚ, r - delta < (q : ℝ) ∧ (q : ℝ) < r :=
    exists_rat_btwn (sub_lt_self r hdelta)
  obtain ⟨upper : ℚ, hupperL, hupperU⟩ :
      ∃ q : ℚ, r < (q : ℝ) ∧ (q : ℝ) < r + delta :=
    exists_rat_btwn (lt_add_of_pos_right r hdelta)
  have hdeltaR : delta ≤ r / 4 := min_le_left _ _
  have hdeltaEta : delta ≤ (eta : ℝ) * r / 8 :=
    min_le_right _ _
  have hlowerPosR : (0 : ℝ) < (lower : ℝ) := by
    nlinarith
  have hsumPos :
      (0 : ℝ) < (lower : ℝ) + (upper : ℝ) := by
    nlinarith
  have hrelativeR :
      (((upper - lower) / (lower + upper) : ℚ) : ℝ) <
        (eta : ℝ) := by
    push_cast
    rw [div_lt_iff₀ hsumPos]
    have hdiff :
        (upper : ℝ) - (lower : ℝ) < 2 * delta := by
      linarith
    have hsum : 3 * r / 2 <
        (lower : ℝ) + (upper : ℝ) := by
      nlinarith
    nlinarith [mul_pos hetaR (sub_pos.mpr hsum)]
  have hrelative :
      _root_.GD.N0115.d006629 lower upper < eta := by
    unfold _root_.GD.N0115.d006629
    have hrelativeR' :
        ((((upper - lower) / (lower + upper) : ℚ) : ℝ)) <
          (eta : ℝ) := by
      simpa [add_comm] using hrelativeR
    have hrelativeQ :
        (upper - lower) / (lower + upper) < eta := by
      exact_mod_cast hrelativeR'
    simpa [add_comm] using hrelativeQ
  have hpre :
      f ⁻¹' Ioo (lower : ℝ) (upper : ℝ) ∈
        𝓝 (_root_.GD.N0131.d008759 center) :=
    hcont.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds ⟨hlowerU, hupperL⟩)
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    Metric.mem_nhds_iff.mp hpre
  have hcap :
      0 < min (wMax : ℝ) epsilon :=
    lt_min (by exact_mod_cast hwMax) hepsilon
  obtain ⟨width : ℚ, hwidthPosR, hwidthCap⟩ :
      ∃ q : ℚ, (0 : ℝ) < (q : ℝ) ∧
        (q : ℝ) < min (wMax : ℝ) epsilon :=
    exists_rat_btwn hcap
  have hwidthPos : 0 < width := by exact_mod_cast hwidthPosR
  have hwidthMax : width ≤ wMax := by
    exact_mod_cast (hwidthCap.trans_le (min_le_left _ _)).le
  let B : _root_.GD.N0115.d006632
      (fun p : ℚ × ℚ => f (_root_.GD.N0131.d008759 p)) :=
    { center := center
      width := width
      width_pos := hwidthPos
      lower := lower
      upper := upper
      lower_pos := by exact_mod_cast hlowerPosR
      bounds := by
        intro p hp
        have hp₁R :
            |((p.1 : ℝ) - (center.1 : ℝ))| <
              (width : ℝ) := by
          exact_mod_cast hp.1
        have hp₂R :
            |((p.2 : ℝ) - (center.2 : ℝ))| <
              (width : ℝ) := by
          exact_mod_cast hp.2
        have hwidthEpsilon :
            (width : ℝ) < epsilon :=
          hwidthCap.trans_le (min_le_right _ _)
        have hdist :
            dist (_root_.GD.N0131.d008759 p) (_root_.GD.N0131.d008759 center) <
              epsilon := by
          rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
          apply max_lt
          · simpa [_root_.GD.N0131.d008759] using hp₁R.trans hwidthEpsilon
          · simpa [_root_.GD.N0131.d008759] using hp₂R.trans hwidthEpsilon
        have hf :=
          hball (Metric.mem_ball.mpr hdist)
        exact ⟨hf.1.le, hf.2.le⟩ }
  exact ⟨B, rfl, hwidthMax, hrelative⟩






theorem d008807
    (D : _root_.GD.N0134.d006518) (k : ℕ)
    (eta wMax : ℚ) (heta : 0 < eta) (hwMax : 0 < wMax) :
    ∃ T : _root_.GD.N0113.d008651 (_root_.GD.N0131.d008766 D) D k,
      T.width ≤ wMax ∧
        ∀ i : Fin (_root_.GD.N0146.d008622 D k).length,
          T.d008654 i < eta := by
  let cap : ℚ := min (_root_.GD.N0115.d006638 D k) wMax
  have hcap : 0 < cap :=
    lt_min (_root_.GD.N0115.d006639 D k) hwMax
  have hlocal :
      ∀ i : Fin (_root_.GD.N0146.d008622 D k).length,
        ∃ B : _root_.GD.N0115.d006632 (_root_.GD.N0131.d008766 D),
          B.center = _root_.GD.N0128.d008801 D k i ∧
            B.width ≤ cap ∧
            _root_.GD.N0115.d006629 B.lower B.upper < eta := by
    intro i
    change
      ∃ B : _root_.GD.N0115.d006632
          (fun p : ℚ × ℚ => _root_.GD.N0131.d008765 D (_root_.GD.N0131.d008759 p)),
        B.center = _root_.GD.N0128.d008801 D k i ∧
          B.width ≤ cap ∧
          _root_.GD.N0115.d006629 B.lower B.upper < eta
    exact _root_.GD.N0128.d008806
      (_root_.GD.N0131.d008765 D) (_root_.GD.N0128.d008801 D k i)
      (_root_.GD.N0128.d008805 D k i)
      (_root_.GD.N0128.d008804 D k i)
      eta cap heta hcap
  let localBox :
      ∀ i : Fin (_root_.GD.N0146.d008622 D k).length,
        _root_.GD.N0115.d006632 (_root_.GD.N0131.d008766 D) :=
    fun i => Classical.choose (hlocal i)
  have localSpec :
      ∀ i : Fin (_root_.GD.N0146.d008622 D k).length,
        (localBox i).center = _root_.GD.N0128.d008801 D k i ∧
          (localBox i).width ≤ cap ∧
          _root_.GD.N0115.d006629 (localBox i).lower
            (localBox i).upper < eta :=
    fun i => Classical.choose_spec (hlocal i)
  let widthCandidate :
      Option (Fin (_root_.GD.N0146.d008622 D k).length) → ℚ
    | none => cap
    | some i => (localBox i).width
  have widthCandidate_pos :
      ∀ z, 0 < widthCandidate z := by
    intro z
    cases z with
    | none => exact hcap
    | some i => exact (localBox i).width_pos
  let widths : Finset ℚ :=
    Finset.univ.image widthCandidate
  have widths_nonempty : widths.Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  let width : ℚ := widths.min' widths_nonempty
  have width_mem : width ∈ widths := by
    exact Finset.min'_mem _ _
  have width_pos : 0 < width := by
    rcases Finset.mem_image.mp width_mem with
      ⟨z, hz, hzw⟩
    rw [← hzw]
    exact widthCandidate_pos z
  have width_le_cap : width ≤ cap := by
    apply Finset.min'_le
    apply Finset.mem_image.mpr
    exact ⟨none, Finset.mem_univ _, rfl⟩
  have width_le_local :
      ∀ i, width ≤ (localBox i).width := by
    intro i
    apply Finset.min'_le
    apply Finset.mem_image.mpr
    exact ⟨some i, Finset.mem_univ _, rfl⟩
  let boxes :
      ∀ i : Fin (_root_.GD.N0146.d008622 D k).length,
        _root_.GD.N0115.d006632 (_root_.GD.N0131.d008766 D) :=
    fun i =>
      { center := _root_.GD.N0128.d008801 D k i
        width := width
        width_pos := width_pos
        lower := (localBox i).lower
        upper := (localBox i).upper
        lower_pos := (localBox i).lower_pos
        bounds := by
          intro p hp
          apply (localBox i).bounds p
          rw [localSpec i |>.1]
          unfold _root_.GD.N0115.d006631 at hp ⊢
          exact
            ⟨hp.1.trans_le (width_le_local i),
              hp.2.trans_le (width_le_local i)⟩ }
  let T : _root_.GD.N0113.d008651 (_root_.GD.N0131.d008766 D) D k :=
    { width := width
      width_pos := width_pos
      width_le_generated :=
        width_le_cap.trans (min_le_left _ _)
      boxes := boxes
      center_exact := by
        intro i
        rfl
      width_exact := by
        intro i
        rfl }
  refine ⟨T, ?_, ?_⟩
  · exact width_le_cap.trans (min_le_right _ _)
  · intro i
    simpa [T, _root_.GD.N0113.d008651.d008654, boxes] using
      (localSpec i).2.2

end

end GD.N0128
