import GD.Module0975
import GD.Module0994

















open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1099

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1102
open _root_.GD.N0232.N0720.N1110
open _root_.GD.N0232.N0720.N1100
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)

abbrev d015756 :=
  _root_.GD.N0232.N0719.N0946.d009229




theorem d015757
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1477.d015749 m n s := by
  unfold _root_.GD.N0232.N0720.N1477.d015749
  positivity



theorem d015758
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (j : ℕ) :
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value‖ ≤ ‖(seed 0).value‖ := by
  have hpBelow : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed 0).value
      (_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value) :=
    _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1159.d014634 m n (seed j).value).1
      (_root_.GD.N0232.N0720.N1102.d015434 m n seed hdesc (Nat.zero_le j))
  have href := hpBelow _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  have hsq : ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value‖ ^ 2 ≤
      ‖(seed 0).value‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖(seed 0).value‖)).mp href
  nlinarith [norm_nonneg (_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value),
    norm_nonneg (seed 0).value]



theorem d015759
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0720.N1099.d015756)
    (hg : g = _root_.GD.N0232.N0720.N1482.d015130 ∨ g = _root_.GD.N0232.N0720.N1482.d015131)
    (henergy : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1477.d015749 m n (seed j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1477.d015744 m n (seed j) g‖)
      atTop (nhds 0) := by
  have hupper : ∀ j,
      ‖_root_.GD.N0232.N0720.N1477.d015744 m n (seed j) g‖ ^ 2 ≤
        _root_.GD.N0232.N0720.N1477.d015749 m n (seed j) := by
    intro j
    rcases hg with rfl | rfl
    · exact le_add_of_nonneg_right
        (sq_nonneg ‖_root_.GD.N0232.N0720.N1477.d015744 m n (seed j)
          _root_.GD.N0232.N0720.N1482.d015131‖)
    · exact le_add_of_nonneg_left
        (sq_nonneg ‖_root_.GD.N0232.N0720.N1477.d015744 m n (seed j)
          _root_.GD.N0232.N0720.N1482.d015130‖)
  have hsquare : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1477.d015744 m n (seed j) g‖ ^ 2)
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun j ↦ sq_nonneg ‖_root_.GD.N0232.N0720.N1477.d015744 m n (seed j) g‖)
      hupper henergy
  have hsqrt := hsquare.sqrt
  simpa [Real.sqrt_sq_eq_abs] using hsqrt



theorem d015760
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (henergy : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1477.d015749 m n (seed j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1477.d015750 m n (seed j))
      atTop (nhds 0) := by
  let B : ℝ := ‖(seed 0).value‖
  let disp₂ : ℕ → ℝ := fun j ↦
    ‖_root_.GD.N0232.N0720.N1477.d015744 m n (seed j) _root_.GD.N0232.N0720.N1482.d015130‖
  let disp₃ : ℕ → ℝ := fun j ↦
    ‖_root_.GD.N0232.N0720.N1477.d015744 m n (seed j) _root_.GD.N0232.N0720.N1482.d015131‖
  have hdisp₂ : Tendsto disp₂ atTop (nhds 0) := by
    exact _root_.GD.N0232.N0720.N1099.d015759
      m n seed _root_.GD.N0232.N0720.N1482.d015130 (Or.inl rfl) henergy
  have hdisp₃ : Tendsto disp₃ atTop (nhds 0) := by
    exact _root_.GD.N0232.N0720.N1099.d015759
      m n seed _root_.GD.N0232.N0720.N1482.d015131 (Or.inr rfl) henergy
  have hupper : ∀ j,
      _root_.GD.N0232.N0720.N1477.d015750 m n (seed j) ≤
        2 * B * (disp₂ j + disp₃ j) := by
    intro j
    have hnorm := _root_.GD.N0232.N0720.N1099.d015758
      m n seed hdesc j
    have hpair₂ : _root_.GD.N0232.N0720.N1477.d015745 m n (seed j)
          _root_.GD.N0232.N0720.N1482.d015130 ≤ B * disp₂ j := by
      unfold _root_.GD.N0232.N0720.N1477.d015745 B disp₂
      exact (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
    have hpair₃ : _root_.GD.N0232.N0720.N1477.d015745 m n (seed j)
          _root_.GD.N0232.N0720.N1482.d015131 ≤ B * disp₃ j := by
      unfold _root_.GD.N0232.N0720.N1477.d015745 B disp₃
      exact (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
    unfold _root_.GD.N0232.N0720.N1477.d015750
    nlinarith
  have hbound : Tendsto (fun j ↦ 2 * B * (disp₂ j + disp₃ j))
      atTop (nhds 0) := by
    simpa only [zero_add, mul_zero] using
      (hdisp₂.add hdisp₃).const_mul (2 * B)
  exact squeeze_zero
    (fun j ↦ _root_.GD.N0232.N0720.N1477.d015752 m n (seed j))
    hupper hbound




theorem d015761
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (henergy : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1477.d015749 m n (seed j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (seed j))
      atTop (nhds 0) := by
  have hslack :=
    _root_.GD.N0232.N0720.N1099.d015760
      m n seed hdesc henergy
  simpa only [_root_.GD.N0232.N0720.N1477.d015751,
    add_zero] using henergy.add hslack





theorem d015762
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (henergy : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1477.d015749 m n (seed j))
      atTop (nhds 0))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  exact _root_.GD.N0232.N0720.N1100.d015493
    m n hm hn seed hdesc
      (_root_.GD.N0232.N0720.N1099.d015761
        m n seed hdesc henergy)
      hstrict





theorem d015763
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n,
        (∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value) ∧
        Tendsto
          (fun j ↦ _root_.GD.N0232.N0720.N1477.d015749 m n (seed j))
          atTop (nhds 0) ∧
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  constructor
  · intro hendpoint
    obtain ⟨s, hstrict, hzero⟩ :=
      (_root_.GD.N0232.N0720.N1482.d015173
        (m := m) (n := n) hm hn).1 hendpoint
    have henergyZero : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 :=
      (_root_.GD.N0232.N0720.N1477.d015755
        m n s).1 hzero
    refine ⟨fun _ ↦ s, ?_, ?_, hstrict⟩
    · intro j
      exact _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
    · simpa only [henergyZero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ))
          atTop (nhds 0))
  · rintro ⟨seed, hdesc, henergy, hstrict⟩
    exact _root_.GD.N0232.N0720.N1099.d015762
      m n hm hn seed hdesc henergy hstrict




theorem d015764
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ¬ ∃ seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n,
        (∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value) ∧
        Tendsto
          (fun j ↦ _root_.GD.N0232.N0720.N1477.d015749 m n (seed j))
          atTop (nhds 0) ∧
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
          (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  rw [_root_.GD.N0232.N0720.N1099.d015763
    m n hm hn]

end
end N1099
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1099.d015757
#print axioms _root_.GD.N0232.N0720.N1099.d015758
#print axioms _root_.GD.N0232.N0720.N1099.d015759
#print axioms _root_.GD.N0232.N0720.N1099.d015760
#print axioms _root_.GD.N0232.N0720.N1099.d015761
#print axioms _root_.GD.N0232.N0720.N1099.d015762
#print axioms _root_.GD.N0232.N0720.N1099.d015763
#print axioms _root_.GD.N0232.N0720.N1099.d015764
