import GD.Module1161
import GD.Module0971



































open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1047

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0107

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)





theorem d018643 :
    ¬ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  intro hterminal
  have hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
    fun θ => (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn θ).le
  have heq := hterminal _ hdom
  have hlt := _root_.GD.N0232.N0720.N1080.d014186 m n hm hn _root_.GD.N0232.N0720.N1080.d014169
  rw [heq] at hlt
  exact lt_irrefl _ hlt

include hm hn in


theorem d018644 :
    ¬ (∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e →
        (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
          _root_.GD.N0232.N0720.N1080.d014197 m n θ e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) →
        ∀ θ : _root_.GD.N0232.N0720.N1080.d014168, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] _root_.GD.N0232.N0720.N1080.d014175 m n) := by
  intro hterminal
  have hstrict := _root_.GD.N0232.N0720.N1080.d014201 m n hm hn
  have hae := hterminal _ (_root_.GD.N0232.N0720.N1080.d014195 m n hm hn)
    (fun θ => (hstrict θ).le) _root_.GD.N0232.N0720.N1080.d014169
  have hlt := hstrict _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n _root_.GD.N0232.N0720.N1080.d014169 hae] at hlt
  exact lt_irrefl _ hlt





theorem d018645 :
    _root_.GD.N0232.N0720.N1159.d014652 m n (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  have href : MemLp (_root_.GD.N0232.N0720.N1080.d014175 m n) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
      _root_.GD.N0232.N0720.N1080.d014177 m n hm hn _root_.GD.N0232.N0720.N1080.d014169
  have hclassReference :
      _root_.GD.N0232.N0720.N1080.d014175 m n =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
    have hcoe :
        (fun ω => (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ω) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1080.d014175 m n := by
      simpa [_root_.GD.N0232.N0720.N1080.d014180] using href.coeFn_toLp
    exact hcoe.symm.trans
      (_root_.GD.N0232.N0720.N1214.d014267 m n (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)).symm
  refine ⟨_root_.GD.N0232.N0720.N1080.d014175 m n, ?_, ?_, ?_⟩
  · simpa [_root_.GD.N0232.N0720.N1080.d014175] using
      _root_.GD.N0117.d014146 m n
  · intro θ
    exact (_root_.GD.N0232.N0720.N1080.d014173 m n θ).ae_le hclassReference
  · intro g ω
    simpa [_root_.GD.N0232.N0720.N1214.d014259] using
      _root_.GD.N0232.N0720.N1215.d014291 m n hm hn g ω

theorem d018646 :
    _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  intro θ
  rw [_root_.GD.N0232.N0720.N1080.d014184 m n hm hn θ]
  exact ENNReal.ofReal_ne_top

theorem d018647 :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
  _root_.GD.N0232.N0720.N1159.d014653 m n _
    (_root_.GD.N0232.N0720.N1047.d018645 m n hm hn)


def d018648 : _root_.GD.N0232.N0720.N1159.d014639 m n where
  value := _root_.GD.N0232.N0720.N1080.d014180 m n hm hn
  finiteRisk := _root_.GD.N0232.N0720.N1047.d018646 m n hm hn
  riskCharacter := _root_.GD.N0232.N0720.N1047.d018647 m n hm hn

@[simp] theorem d018649 :
    (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn).value = _root_.GD.N0232.N0720.N1080.d014180 m n hm hn := rfl





def d018650 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)

theorem d018651 :
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn)
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
  (_root_.GD.N0232.N0720.N1159.d014634 m n (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)).1

theorem d018652 :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) :=
  (_root_.GD.N0232.N0720.N1159.d014634 m n (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)).2.1

theorem d018653 :
    _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) := fun θ =>
  ne_top_of_le_ne_top (_root_.GD.N0232.N0720.N1047.d018646 m n hm hn θ)
    (_root_.GD.N0232.N0720.N1047.d018651 m n hm hn θ)



theorem d018654
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) d (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ‖_root_.GD.N0232.N0720.N1047.d018650 m n hm hn‖ ^ 2 ≤ ‖d‖ ^ 2 := by
  have h := (_root_.GD.N0232.N0720.N1159.d014634 m n (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)).2.2 d hd
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at h
  simp only [zero_sub, norm_neg] at h
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp h



theorem d018655
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ‖_root_.GD.N0232.N0720.N1047.d018650 m n hm hn‖ ^ 2 ≤ ‖p‖ ^ 2 :=
  _root_.GD.N0232.N0720.N1047.d018654 m n hm hn p (fun θ => (hp θ).le)


def d018656 : ℝ :=
  _root_.GD.N0232.N0720.N1201.d015333 m n (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn)

theorem d018657 :
    _root_.GD.N0232.N0720.N1047.d018656 m n hm hn =
      ‖_root_.GD.N0232.N0720.N1080.d014180 m n hm hn‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1047.d018650 m n hm hn‖ ^ 2 := rfl



theorem d018658
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) d (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ‖_root_.GD.N0232.N0720.N1080.d014180 m n hm hn‖ ^ 2 - ‖d‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1047.d018656 m n hm hn := by
  have h := _root_.GD.N0232.N0720.N1047.d018654 m n hm hn d hd
  rw [_root_.GD.N0232.N0720.N1047.d018657]
  linarith

theorem d018659 :
    ‖_root_.GD.N0232.N0720.N1080.d014181 m n hm hn‖ ^ 2 < ‖_root_.GD.N0232.N0720.N1080.d014180 m n hm hn‖ ^ 2 := by
  have h := _root_.GD.N0232.N0720.N1080.d014186 m n hm hn _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at h
  simp only [zero_sub, norm_neg] at h
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (sq_nonneg _)).mp h



theorem d018660 : 0 < _root_.GD.N0232.N0720.N1047.d018656 m n hm hn := by
  have hfloor := _root_.GD.N0232.N0720.N1047.d018658 m n hm hn
    (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)
    (fun θ => (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn θ).le)
  have hlt := _root_.GD.N0232.N0720.N1047.d018659 m n hm hn
  linarith

theorem d018661 :
    ‖_root_.GD.N0232.N0720.N1047.d018650 m n hm hn‖ ^ 2 < ‖_root_.GD.N0232.N0720.N1080.d014180 m n hm hn‖ ^ 2 := by
  have h := _root_.GD.N0232.N0720.N1047.d018660 m n hm hn
  rw [_root_.GD.N0232.N0720.N1047.d018657] at h
  linarith

theorem d018662 :
    _root_.GD.N0232.N0720.N1047.d018650 m n hm hn ≠ _root_.GD.N0232.N0720.N1080.d014180 m n hm hn := by
  intro heq
  have h := _root_.GD.N0232.N0720.N1047.d018661 m n hm hn
  rw [heq] at h
  exact lt_irrefl _ h





def d018663 : ℝ :=
  _root_.GD.N0107.d009045 m n 1 1 *
      _root_.GD.N0120.d008813
        (((m - 1 : ℕ) : ℝ) / 2) (((n - 1 : ℕ) : ℝ) / 2)
        (_root_.GD.N0107.d009046 m n 1 1) *
    _root_.GD.N0232.N0720.d014160 (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn)

theorem d018664 :
    0 < _root_.GD.N0232.N0720.N1047.d018663 m n hm hn := by
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  have hgap : 0 < _root_.GD.N0232.N0720.d014160 (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn) :=
    (Classical.choose_spec
      (_root_.GD.N0232.N0720.d014167 m n hm hn)).2.1
  have hα : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) / 2 := by
    have h1 : (1 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ m - 1 by omega)
    linarith
  have hβ : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) / 2 := by
    have h1 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ n - 1 by omega)
    linarith
  unfold _root_.GD.N0232.N0720.N1047.d018663
  exact mul_pos
    (mul_pos (_root_.GD.N0107.d009049 hm0 hn0 one_pos one_pos)
      (_root_.GD.N0120.d008823 hα hβ
        (_root_.GD.N0107.d009050 hm0 hn0 one_pos one_pos)
        (_root_.GD.N0107.d009051 hm0 hn0 one_pos one_pos)))
    hgap

theorem d018665 :
    ‖_root_.GD.N0232.N0720.N1080.d014180 m n hm hn‖ ^ 2 =
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n 0 1 1)
        (fun ω => _root_.GD.N0107.d012733 m n ω - 0) := by
  have h := _root_.GD.N0232.N0720.N1080.d014184 m n hm hn _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n] at h
  simp only [zero_sub, norm_neg] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _)).mp h

theorem d018666 :
    ‖_root_.GD.N0232.N0720.N1080.d014181 m n hm hn‖ ^ 2 =
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n 0 1 1)
        (fun ω => _root_.GD.N0107.d012734 m n ((_root_.GD.N0232.N0720.N1080.d014174 m n hm hn).step : ℝ)
          (_root_.GD.N0232.N0720.d014159 (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn)) ω - 0) := by
  have h := _root_.GD.N0232.N0720.N1080.d014185 m n hm hn _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n] at h
  simp only [zero_sub, norm_neg] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _)).mp h



theorem d018667 :
    _root_.GD.N0232.N0720.N1047.d018663 m n hm hn ≤
      ‖_root_.GD.N0232.N0720.N1080.d014180 m n hm hn‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1080.d014181 m n hm hn‖ ^ 2 := by
  have hspec := Classical.choose_spec
    (_root_.GD.N0232.N0720.d014167 m n hm hn)
  have hmargin := (hspec.2.2 0 1 1 one_pos one_pos).1
  change _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n 0 1 1)
      (fun ω => _root_.GD.N0107.d012734 m n ((_root_.GD.N0232.N0720.N1080.d014174 m n hm hn).step : ℝ)
        (_root_.GD.N0232.N0720.d014159 (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn)) ω - 0) -
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n 0 1 1)
        (fun ω => _root_.GD.N0107.d012733 m n ω - 0) ≤
      -(_root_.GD.N0107.d009045 m n 1 1 *
        _root_.GD.N0120.d008813
          (((m - 1 : ℕ) : ℝ) / 2) (((n - 1 : ℕ) : ℝ) / 2)
          (_root_.GD.N0107.d009046 m n 1 1) *
        _root_.GD.N0232.N0720.d014160 (_root_.GD.N0232.N0720.N1080.d014174 m n hm hn)) at hmargin
  rw [_root_.GD.N0232.N0720.N1047.d018665 m n hm hn,
    _root_.GD.N0232.N0720.N1047.d018666 m n hm hn]
  unfold _root_.GD.N0232.N0720.N1047.d018663
  linarith



theorem d018668 :
    _root_.GD.N0232.N0720.N1047.d018663 m n hm hn ≤ _root_.GD.N0232.N0720.N1047.d018656 m n hm hn :=
  (_root_.GD.N0232.N0720.N1047.d018667 m n hm hn).trans
    (_root_.GD.N0232.N0720.N1047.d018658 m n hm hn (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn)
      (fun θ => (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn θ).le))





def d018669
    (hchar : _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014639 m n where
  value := _root_.GD.N0232.N0720.N1047.d018650 m n hm hn
  finiteRisk := _root_.GD.N0232.N0720.N1047.d018653 m n hm hn
  riskCharacter := hchar



theorem d018670
    (hchar : _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014652 m n
      (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) :=
  _root_.GD.N0232.N0720.N1409.d018607 hm hn
    (_root_.GD.N0232.N0720.N1047.d018669 m n hm hn hchar)
    (_root_.GD.N0232.N0720.N1047.d018652 m n hm hn)



theorem d018671 :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) ↔
      _root_.GD.N0232.N0720.N1159.d014652 m n
        (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) :=
  ⟨_root_.GD.N0232.N0720.N1047.d018670 m n hm hn,
    _root_.GD.N0232.N0720.N1159.d014653 m n _⟩



theorem d018672 :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn) = 0 ↔
      _root_.GD.N0232.N0720.N1159.d014652 m n
        (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) := by
  rw [_root_.GD.N0232.N0720.N1482.d015171]
  exact _root_.GD.N0232.N0720.N1159.d014656 m n hm hn (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn)

theorem d018673 :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn) = 0 ↔
      _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) := by
  rw [_root_.GD.N0232.N0720.N1047.d018672,
    _root_.GD.N0232.N0720.N1047.d018671]







theorem d018674
    (hchar : _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := m) (n := n) hm hn]
  exact ⟨_root_.GD.N0232.N0720.N1047.d018669 m n hm hn hchar, hstrict,
    _root_.GD.N0232.N0720.N1047.d018652 m n hm hn⟩


theorem d018675
    (hdefect : _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn) = 0)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n :=
  _root_.GD.N0232.N0720.N1047.d018674 m n hm hn
    ((_root_.GD.N0232.N0720.N1047.d018673 m n hm hn).1 hdefect)
    hstrict




theorem d018676
    (hchar : _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn)) :
    ∃ p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      _root_.GD.N0232.N0720.N1159.d014652 m n p ∧
        _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) p (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        p ≠ _root_.GD.N0232.N0720.N1080.d014180 m n hm hn ∧
        _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p :=
  ⟨_root_.GD.N0232.N0720.N1047.d018650 m n hm hn,
    _root_.GD.N0232.N0720.N1047.d018670 m n hm hn hchar,
    _root_.GD.N0232.N0720.N1047.d018651 m n hm hn,
    _root_.GD.N0232.N0720.N1047.d018662 m n hm hn,
    _root_.GD.N0232.N0720.N1047.d018652 m n hm hn⟩

end

end N1047
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1047.d018643
#print axioms _root_.GD.N0232.N0720.N1047.d018644
#print axioms _root_.GD.N0232.N0720.N1047.d018645
#print axioms _root_.GD.N0232.N0720.N1047.d018652
#print axioms _root_.GD.N0232.N0720.N1047.d018658
#print axioms _root_.GD.N0232.N0720.N1047.d018660
#print axioms _root_.GD.N0232.N0720.N1047.d018664
#print axioms _root_.GD.N0232.N0720.N1047.d018668
#print axioms _root_.GD.N0232.N0720.N1047.d018671
#print axioms _root_.GD.N0232.N0720.N1047.d018673
#print axioms _root_.GD.N0232.N0720.N1047.d018674
#print axioms _root_.GD.N0232.N0720.N1047.d018676
