import GD.Module1161





















namespace GD
namespace N0232
namespace N0720
namespace N1408

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0719.N0946

variable {m n : ℕ}

abbrev d018756 :=
  _root_.GD.N0232.N0719.N0946.d009229



noncomputable def d018757
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1408.d018756) : ℝ :=
  ‖(_root_.GD.N0232.N0720.N1159.d014645 m n s g
      (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1‖ ^ 2


noncomputable def d018758
    (weight : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : ℝ :=
  weight * _root_.GD.N0232.N0720.N1408.d018757 s _root_.GD.N0232.N0720.N1482.d015130 +
    (1 - weight) * _root_.GD.N0232.N0720.N1408.d018757 s _root_.GD.N0232.N0720.N1482.d015131



theorem d018759
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1408.d018756) :
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1408.d018757 s g := by
  have h := _root_.GD.N0232.N0720.N1159.d014650 m n s g
  rw [← sub_nonneg]
  simpa only [_root_.GD.N0232.N0720.N1159.d014647, _root_.GD.N0232.N0720.N1408.d018757] using h



theorem d018760
    (weight : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1408.d018758 weight s -
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 =
      weight * _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 +
        (1 - weight) *
          _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 := by
  unfold _root_.GD.N0232.N0720.N1408.d018758 _root_.GD.N0232.N0720.N1408.d018757
    _root_.GD.N0232.N0720.N1159.d014647
  ring




theorem d018761
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1408.d018758 weight s ≤
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ↔
      _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 := by
  let d₂ := _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130
  let d₃ := _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131
  have hd₂ : 0 ≤ d₂ := _root_.GD.N0232.N0720.N1159.d014650 m n s _root_.GD.N0232.N0720.N1482.d015130
  have hd₃ : 0 ≤ d₃ :=
    _root_.GD.N0232.N0720.N1159.d014650 m n s _root_.GD.N0232.N0720.N1482.d015131
  have hright : 0 < 1 - weight := sub_pos.mpr hweight1
  constructor
  · intro hle
    have hsumle : weight * d₂ + (1 - weight) * d₃ ≤ 0 := by
      have hgap := _root_.GD.N0232.N0720.N1408.d018760 weight s
      change _root_.GD.N0232.N0720.N1408.d018758 weight s -
          ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 =
        weight * d₂ + (1 - weight) * d₃ at hgap
      linarith
    have hp₂ : 0 ≤ weight * d₂ := mul_nonneg hweight0.le hd₂
    have hp₃ : 0 ≤ (1 - weight) * d₃ := mul_nonneg hright.le hd₃
    have hsum : weight * d₂ + (1 - weight) * d₃ = 0 :=
      le_antisymm hsumle (add_nonneg hp₂ hp₃)
    have hparts := (add_eq_zero_iff_of_nonneg hp₂ hp₃).1 hsum
    have hd₂zero : d₂ = 0 :=
      (mul_eq_zero.mp hparts.1).resolve_left (ne_of_gt hweight0)
    have hd₃zero : d₃ = 0 :=
      (mul_eq_zero.mp hparts.2).resolve_left (ne_of_gt hright)
    unfold _root_.GD.N0232.N0720.N1482.d015169
    simpa only [d₂, d₃, hd₂zero, hd₃zero, add_zero]
  · intro hmaster
    have hsum : d₂ + d₃ = 0 := by
      simpa only [_root_.GD.N0232.N0720.N1482.d015169, d₂, d₃] using hmaster
    have hparts := (add_eq_zero_iff_of_nonneg hd₂ hd₃).1 hsum
    have hgap := _root_.GD.N0232.N0720.N1408.d018760 weight s
    change _root_.GD.N0232.N0720.N1408.d018758 weight s -
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 =
      weight * d₂ + (1 - weight) * d₃ at hgap
    rw [hparts.1, hparts.2] at hgap
    linarith




theorem d018762
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1408.d018758 (1 / 2 : ℝ) s ≤
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ↔
      _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 := by
  exact _root_.GD.N0232.N0720.N1408.d018761
    (1 / 2 : ℝ) (by norm_num) (by norm_num) s





theorem d018763
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    2 * (_root_.GD.N0232.N0720.N1408.d018758 (1 / 2 : ℝ) s -
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) =
      _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s := by
  rw [_root_.GD.N0232.N0720.N1408.d018760]
  unfold _root_.GD.N0232.N0720.N1482.d015169
  ring





theorem d018764
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1408.d018758 (1 / 2 : ℝ) s ≤
            ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1482.d015173
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, hmaster⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1408.d018762 s).2 hmaster⟩
  · rintro ⟨s, hstrict, havg⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1408.d018762 s).1 havg⟩



theorem d018765
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (weight : ℝ) (hweight0 : 0 < weight) (hweight1 : weight < 1) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1408.d018758 weight s ≤
            ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1482.d015173
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, hmaster⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1408.d018761
        weight hweight0 hweight1 s).2 hmaster⟩
  · rintro ⟨s, hstrict, havg⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1408.d018761
        weight hweight0 hweight1 s).1 havg⟩




theorem d018766
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) →
          ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 <
            _root_.GD.N0232.N0720.N1408.d018758 (1 / 2 : ℝ) s := by
  constructor
  · intro hno s hstrict
    exact lt_of_not_ge (fun hle =>
      hno ((_root_.GD.N0232.N0720.N1408.d018764
        (m := m) (n := n) hm hn).2 ⟨s, hstrict, hle⟩))
  · intro hall hendpoint
    obtain ⟨s, hstrict, hle⟩ :=
      (_root_.GD.N0232.N0720.N1408.d018764
        (m := m) (n := n) hm hn).1 hendpoint
    exact (not_le_of_gt (hall s hstrict)) hle

end

end N1408
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1408.d018759
#print axioms _root_.GD.N0232.N0720.N1408.d018760
#print axioms _root_.GD.N0232.N0720.N1408.d018761
#print axioms _root_.GD.N0232.N0720.N1408.d018762
#print axioms _root_.GD.N0232.N0720.N1408.d018763
#print axioms _root_.GD.N0232.N0720.N1408.d018764
#print axioms _root_.GD.N0232.N0720.N1408.d018765
#print axioms _root_.GD.N0232.N0720.N1408.d018766
