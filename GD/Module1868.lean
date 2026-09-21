import GD.Module1865
import GD.Module1081

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace GD.N0082.N0332

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0230.N0611
open _root_.GD.N0076.N0313
open _root_.GD.N0232.N0720.N1220 (d017301)

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d030615 (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) : ℝ :=
  _root_.GD.N0076.N0313.d030565 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 + ∑ θ ∈ F, w θ * _root_.GD.N0076.N0313.d030565 m n hm hn θ

def d030616 (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1220.d017301 m n F w / _root_.GD.N0082.N0332.d030615 m n hm hn F w

theorem d030617 (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ) : 0 < _root_.GD.N0082.N0332.d030615 m n hm hn F w := by
  apply add_pos_of_pos_of_nonneg (_root_.GD.N0076.N0313.d030566 m n hm hn _root_.GD.N0232.N0720.N1080.d014169)
  exact Finset.sum_nonneg fun θ hθ => mul_nonneg (hw θ hθ) (_root_.GD.N0076.N0313.d030566 m n hm hn θ).le

theorem d030618 (c : ℝ) (hc : 0 ≤ c) :
    (_root_.GD.N0076.N0313.d030570 m n hm hn c).Nonempty ↔
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
        _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤ c * _root_.GD.N0082.N0332.d030615 m n hm hn F w := by
  change (∃ p, ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ ENNReal.ofReal (c * _root_.GD.N0076.N0313.d030565 m n hm hn θ)) ↔ _
  rw [_root_.GD.N0232.N0720.N1220.d017305 m n hm hn
    (fun θ => c * _root_.GD.N0076.N0313.d030565 m n hm hn θ) (fun θ => mul_nonneg hc (_root_.GD.N0076.N0313.d030566 m n hm hn θ).le)]
  simp only [_root_.GD.N0082.N0332.d030615, mul_add, Finset.mul_sum, mul_left_comm]

theorem d030619 (c : ℝ) (hc : 0 ≤ c) :
    _root_.GD.N0076.N0313.d030569 m n hm hn ≤ ENNReal.ofReal c ↔ (_root_.GD.N0076.N0313.d030570 m n hm hn c).Nonempty := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := _root_.GD.N0076.N0313.d030585 m n hm hn
    exact ⟨p, _root_.GD.N0076.N0313.d030582 m n hm hn (ENNReal.toReal_le_of_le_ofReal hc h) hp⟩
  · rintro ⟨p, hp⟩
    apply (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0076.N0313.d030568 m n hm hn)
      (_root_.GD.N0076.N0313.d030572 m n (_root_.GD.N0076.N0313.d030576 m n hm hn hp))).trans
    apply iSup_le
    intro θ
    apply (_root_.GD.N0076.N0313.d030571 m n hm hn c hc θ _).mpr
    rw [_root_.GD.N0232.N0720.N1215.d014286]
    exact hp θ

theorem d030620 (c : ℝ) (hc : 0 ≤ c) :
    _root_.GD.N0076.N0313.d030569 m n hm hn ≤ ENNReal.ofReal c ↔
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
        _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤ c * _root_.GD.N0082.N0332.d030615 m n hm hn F w := by
  rw [_root_.GD.N0082.N0332.d030619 m n hm hn c hc,
    _root_.GD.N0082.N0332.d030618 m n hm hn c hc]

theorem d030621 (c : ℝ) (hc : 0 ≤ c) :
    _root_.GD.N0076.N0313.d030569 m n hm hn ≤ ENNReal.ofReal c ↔
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
        _root_.GD.N0082.N0332.d030616 m n hm hn F w ≤ c := by
  rw [_root_.GD.N0082.N0332.d030620 m n hm hn c hc]
  exact forall_congr' fun F => forall_congr' fun w =>
    forall_congr' fun hw => (div_le_iff₀ (_root_.GD.N0082.N0332.d030617 m n hm hn F w hw)).symm

theorem d030622 (c : ℝ) (hc : 0 ≤ c) :
    ENNReal.ofReal c < _root_.GD.N0076.N0313.d030569 m n hm hn ↔
      ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ c < _root_.GD.N0082.N0332.d030616 m n hm hn F w := by
  classical
  have h := (_root_.GD.N0082.N0332.d030621 m n hm hn c hc).not
  push Not at h
  exact h

def d030623 : ℝ≥0∞ :=
  ⨆ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (_ : ∀ θ ∈ F, 0 ≤ w θ),
    ENNReal.ofReal (_root_.GD.N0082.N0332.d030616 m n hm hn F w)

theorem d030624 :
    _root_.GD.N0076.N0313.d030569 m n hm hn = _root_.GD.N0082.N0332.d030623 m n hm hn := by
  apply le_antisymm
  · by_cases htop : _root_.GD.N0082.N0332.d030623 m n hm hn = ⊤
    · rw [htop]
      exact le_top
    have hcut : _root_.GD.N0076.N0313.d030569 m n hm hn ≤ ENNReal.ofReal (_root_.GD.N0082.N0332.d030623 m n hm hn).toReal := by
      apply (_root_.GD.N0082.N0332.d030621 m n hm hn _ ENNReal.toReal_nonneg).mpr
      intro F w hw
      have hb : ENNReal.ofReal (_root_.GD.N0082.N0332.d030616 m n hm hn F w) ≤ _root_.GD.N0082.N0332.d030623 m n hm hn :=
        le_iSup_of_le F (le_iSup_of_le w (le_iSup_of_le hw le_rfl))
      rw [← ENNReal.ofReal_toReal htop] at hb
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hb
    rwa [ENNReal.ofReal_toReal htop] at hcut
  · have hcut := (_root_.GD.N0082.N0332.d030621 m n hm hn
      (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal ENNReal.toReal_nonneg).mp
      (le_of_eq (ENNReal.ofReal_toReal (_root_.GD.N0076.N0313.d030574 m n hm hn)).symm)
    apply iSup_le
    intro F
    apply iSup_le
    intro w
    apply iSup_le
    intro hw
    exact (ENNReal.ofReal_le_ofReal (hcut F w hw)).trans_eq
      (ENNReal.ofReal_toReal (_root_.GD.N0076.N0313.d030574 m n hm hn))

theorem d030625 (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ) :
    _root_.GD.N0082.N0332.d030616 m n hm hn F w ≤ (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal :=
  (_root_.GD.N0082.N0332.d030621 m n hm hn _ ENNReal.toReal_nonneg).mp
    (le_of_eq (ENNReal.ofReal_toReal (_root_.GD.N0076.N0313.d030574 m n hm hn)).symm) F w hw

theorem d030626 (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ) : _root_.GD.N0082.N0332.d030616 m n hm hn F w ≤ 1 :=
  (_root_.GD.N0082.N0332.d030625 m n hm hn F w hw).trans (_root_.GD.N0076.N0313.d030575 m n hm hn)

def d030627 : Prop :=
  ∀ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n, 1 ≤ _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) d

theorem d030628 : _root_.GD.N0082.N0332.d030627 m n hm hn ↔ _root_.GD.N0076.N0313.d030569 m n hm hn = 1 := by
  constructor
  · intro h
    apply le_antisymm (_root_.GD.N0076.N0313.d030573 m n hm hn)
    exact le_iInf fun d => le_iInf fun hd => h d hd
  · intro h d hd
    rw [← h]
    exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0076.N0313.d030568 m n hm hn) hd

theorem d030629 :
    _root_.GD.N0082.N0332.d030627 m n hm hn ↔ ∀ c : ℝ, 0 ≤ c → c < 1 →
      ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ c < _root_.GD.N0082.N0332.d030616 m n hm hn F w := by
  rw [_root_.GD.N0082.N0332.d030628 m n hm hn]
  constructor
  · intro h c hc hc1
    apply (_root_.GD.N0082.N0332.d030622 m n hm hn c hc).mp
    rw [h]
    exact ENNReal.ofReal_lt_one.mpr hc1
  · intro h
    apply le_antisymm (_root_.GD.N0076.N0313.d030573 m n hm hn)
    by_contra hv
    have hlt : _root_.GD.N0076.N0313.d030569 m n hm hn < 1 := lt_of_not_ge hv
    have hr : (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal < 1 := by
      simpa only [ENNReal.toReal_one] using
        (ENNReal.toReal_lt_toReal (_root_.GD.N0076.N0313.d030574 m n hm hn) (by simp)).mpr hlt
    obtain ⟨F, w, hw, hgap⟩ := h _ ENNReal.toReal_nonneg hr
    exact (not_lt_of_ge (_root_.GD.N0082.N0332.d030625 m n hm hn F w hw)) hgap

end
end GD.N0082.N0332

#print axioms _root_.GD.N0082.N0332.d030618
#print axioms _root_.GD.N0082.N0332.d030619
#print axioms _root_.GD.N0082.N0332.d030620
#print axioms _root_.GD.N0082.N0332.d030621
#print axioms _root_.GD.N0082.N0332.d030622
#print axioms _root_.GD.N0082.N0332.d030624
#print axioms _root_.GD.N0082.N0332.d030625
#print axioms _root_.GD.N0082.N0332.d030626
#print axioms _root_.GD.N0082.N0332.d030628
#print axioms _root_.GD.N0082.N0332.d030629
