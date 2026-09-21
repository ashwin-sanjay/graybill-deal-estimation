import GD.Module1830
import GD.Module1811
import GD.Module1081
import GD.Module1832

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0096.N0342

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1226 _root_.GD.N0232.N0720.N1220
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0718
open _root_.GD.N0046.N0305

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d030264 (θ : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  min (_root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)).toReal
    ((_root_.GD.N0232.N0720.N1256.d015549 m n).toReal * _root_.GD.N0232.N0720.N1257.d015508 m n θ)

theorem d030265 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    0 ≤ _root_.GD.N0096.N0342.d030264 m n hm hn θ := by
  exact le_min ENNReal.toReal_nonneg
    (mul_nonneg ENNReal.toReal_nonneg (_root_.GD.N0232.N0720.N1257.d015510 m n (by omega) θ).le)

theorem d030266 (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    ENNReal.ofReal (_root_.GD.N0096.N0342.d030264 m n hm hn θ) =
      min (_root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
        (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ)) := by
  have hb : _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ≠ ⊤ := by
    rw [_root_.GD.N0232.N0720.N1080.d014184]
    exact ENNReal.ofReal_ne_top
  rw [_root_.GD.N0096.N0342.d030264, ENNReal.ofReal_min, ENNReal.ofReal_toReal hb,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hV]

theorem d030267 (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤)
    (p : _root_.GD.N0046.N0305.d030201 m n) :
    p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn ↔
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ ENNReal.ofReal (_root_.GD.N0096.N0342.d030264 m n hm hn θ) := by
  simp only [_root_.GD.N0046.N0305.d030202, mem_setOf_eq, _root_.GD.N0096.N0342.d030266 m n hm hn hV, le_min_iff]
  exact forall_congr' fun _ => and_comm

def d030268 (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) : ℝ :=
  _root_.GD.N0096.N0342.d030264 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 +
    ∑ θ ∈ F, w θ * _root_.GD.N0096.N0342.d030264 m n hm hn θ - _root_.GD.N0232.N0720.N1220.d017301 m n F w

theorem d030269 (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty ↔
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) → _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤
          _root_.GD.N0096.N0342.d030264 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 +
            ∑ θ ∈ F, w θ * _root_.GD.N0096.N0342.d030264 m n hm hn θ := by
  have hcap := _root_.GD.N0232.N0720.N1220.d017305 m n hm hn
    (_root_.GD.N0096.N0342.d030264 m n hm hn) (_root_.GD.N0096.N0342.d030265 m n hm hn)
  exact (exists_congr fun p => _root_.GD.N0096.N0342.d030267 m n hm hn hV p).trans hcap

theorem d030270 (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty ↔
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) → 0 ≤ _root_.GD.N0096.N0342.d030268 m n hm hn F w := by
  rw [_root_.GD.N0096.N0342.d030269 m n hm hn hV]
  simp only [_root_.GD.N0096.N0342.d030268, sub_nonneg]

theorem d030271 (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ ↔
      ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ _root_.GD.N0096.N0342.d030268 m n hm hn F w < 0 := by
  classical
  rw [← Set.not_nonempty_iff_eq_empty,
    _root_.GD.N0096.N0342.d030270 m n hm hn hV]
  push Not
  rfl

theorem d030272 (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤)
    {p : _root_.GD.N0046.N0305.d030201 m n} (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) :
    ‖p‖ ^ 2 ≤ _root_.GD.N0096.N0342.d030264 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 := by
  have hb := (_root_.GD.N0096.N0342.d030267 m n hm hn hV p).mp hp _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n] at hb
  simp only [zero_sub, norm_neg] at hb
  exact (ENNReal.ofReal_le_ofReal_iff
    (_root_.GD.N0096.N0342.d030265 m n hm hn _root_.GD.N0232.N0720.N1080.d014169)).mp hb

theorem d030273 (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ)
    {p q : _root_.GD.N0046.N0305.d030201 m n} (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hq : q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) :
    ‖p - q‖ ^ 2 / 4 ≤ _root_.GD.N0096.N0342.d030268 m n hm hn F w := by
  classical
  let z := _root_.GD.N0230.N0718.d001528 p q
  have hz : z ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := _root_.GD.N0046.N0305.d030209 m n hp hq
  have hb := _root_.GD.N0232.N0720.N1220.d017302 m n F w hw z
    (_root_.GD.N0046.N0305.d030204 m n hz)
  have hsum : (∑ θ ∈ F, w θ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ z).toReal) ≤
      ∑ θ ∈ F, w θ * _root_.GD.N0096.N0342.d030264 m n hm hn θ := by
    apply Finset.sum_le_sum
    intro θ hθ
    apply mul_le_mul_of_nonneg_left _ (hw θ hθ)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((_root_.GD.N0096.N0342.d030267 m n hm hn hV z).mp hz θ)).trans_eq
      (ENNReal.toReal_ofReal (_root_.GD.N0096.N0342.d030265 m n hm hn θ))
  have hpE := _root_.GD.N0096.N0342.d030272 m n hm hn hV hp
  have hqE := _root_.GD.N0096.N0342.d030272 m n hm hn hV hq
  have hid := _root_.GD.N0046.N0302.d030041 p q
  change ‖z‖ ^ 2 + ‖p - q‖ ^ 2 / 4 = (‖p‖ ^ 2 + ‖q‖ ^ 2) / 2 at hid
  unfold _root_.GD.N0096.N0342.d030268
  linarith

theorem d030274 (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ)
    {p q r : _root_.GD.N0046.N0305.d030201 m n} (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn)
    (hq : q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hr : r ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) :
    (4 * ‖q - p‖ ^ 2 + 9 * ‖r - p‖ ^ 2) / 52 ≤ _root_.GD.N0096.N0342.d030268 m n hm hn F w := by
  have h₂ := _root_.GD.N0096.N0342.d030273 m n hm hn hV F w hw hq hp
  have h₃ := _root_.GD.N0096.N0342.d030273 m n hm hn hV F w hw hr hp
  linarith

theorem d030275 (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤)
    (hsaturation : ∀ ε : ℝ, 0 < ε →
      ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ _root_.GD.N0096.N0342.d030268 m n hm hn F w < ε) :
    (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton := by
  intro p hp q hq
  by_contra hne
  have hd : 0 < ‖p - q‖ ^ 2 / 4 :=
    div_pos (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))) (by norm_num)
  obtain ⟨F, w, hw, hgap⟩ := hsaturation _ hd
  exact (not_lt_of_ge (_root_.GD.N0096.N0342.d030273 m n hm hn hV F w hw hp hq)) hgap

theorem d030276
    (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤)
    (hfeasible : ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) → 0 ≤ _root_.GD.N0096.N0342.d030268 m n hm hn F w)
    (hsaturation : ∀ ε : ℝ, 0 < ε →
      ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ _root_.GD.N0096.N0342.d030268 m n hm hn F w < ε) :
    ∃! p, p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := by
  obtain ⟨p, hp⟩ :=
    (_root_.GD.N0096.N0342.d030270 m n hm hn hV).mpr hfeasible
  exact ⟨p, hp, fun q hq =>
    _root_.GD.N0096.N0342.d030275 m n hm hn hV hsaturation hq hp⟩

theorem d030277
    (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤)
    {p q : _root_.GD.N0046.N0305.d030201 m n} (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) (hq : q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn)
    (hne : p ≠ q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) → ε ≤ _root_.GD.N0096.N0342.d030268 m n hm hn F w := by
  refine ⟨‖p - q‖ ^ 2 / 4, ?_, fun F w hw =>
    _root_.GD.N0096.N0342.d030273 m n hm hn hV F w hw hp hq⟩
  exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))) (by norm_num)

theorem d030278
    (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤)
    (h : _root_.GD.N0096.N0340.d030229 m n hm hn) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) → ε ≤ _root_.GD.N0096.N0342.d030268 m n hm hn F w := by
  classical
  have hnsub := _root_.GD.N0096.N0340.d030231 m n hm hn h
  have hex : ∃ p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn, ∃ q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn, p ≠ q := by
    by_contra hnot
    push Not at hnot
    exact hnsub (fun p hp q hq => hnot p hp q hq)
  obtain ⟨p, hp, q, hq, hpq⟩ := hex
  exact _root_.GD.N0096.N0342.d030277 m n hm hn hV hp hq hpq

end
end GD.N0096.N0342

#print axioms _root_.GD.N0096.N0342.d030266
#print axioms _root_.GD.N0096.N0342.d030269
#print axioms _root_.GD.N0096.N0342.d030271
#print axioms _root_.GD.N0096.N0342.d030273
#print axioms _root_.GD.N0096.N0342.d030274
#print axioms _root_.GD.N0096.N0342.d030275
#print axioms _root_.GD.N0096.N0342.d030276
#print axioms _root_.GD.N0096.N0342.d030278
