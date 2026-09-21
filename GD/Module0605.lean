import GD.Module0604
import GD.Module0602











namespace GD.N0113
namespace d008651

noncomputable section

open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0135
open _root_.GD.N0113
open _root_.GD.N0111
open _root_.GD.N0132
open _root_.GD.N0146
open _root_.GD.N0129

def d008737 (α β : ℝ) : ℝ :=
  (α * β / (α + β)) / 8

def d008738 (α β : ℝ) : ℝ :=
  _root_.GD.N0132.d006442 α β / 4

def d008739
    (α β r v₀ v₁ v₂ vt : ℝ) : ℝ :=
  |v₀| * (_root_.GD.N0113.d008651.d008737 α β * _root_.GD.N0111.d006160 α β r 0 1)
    + |v₁| * (_root_.GD.N0113.d008651.d008737 α β * _root_.GD.N0111.d006160 α β r 1 1)
    + |v₂| * (_root_.GD.N0113.d008651.d008737 α β * _root_.GD.N0111.d006160 α β r 2 1)
    + |vt| * (2 * _root_.GD.N0113.d008651.d008737 α β *
      _root_.GD.N0111.d006160 α β r 0 2)

def d008740
    (α β r v₁ v₂ : ℝ) : ℝ :=
  |v₁| * (_root_.GD.N0111.d006160 α β r 3 0 *
      _root_.GD.N0113.d008651.d008738 α β ^ 2 / 6)
    + |v₂| * (_root_.GD.N0111.d006160 α β r 4 0 *
      _root_.GD.N0113.d008651.d008738 α β ^ 2 / 12)

def d008741
    (α β r v₁ v₃ vst : ℝ) : ℝ :=
  |v₁| * (_root_.GD.N0113.d008651.d008737 α β * _root_.GD.N0111.d006160 α β r 1 1)
    + |v₃| * (_root_.GD.N0113.d008651.d008737 α β * _root_.GD.N0111.d006160 α β r 3 1)
    + |vst| * (2 * _root_.GD.N0113.d008651.d008737 α β *
      _root_.GD.N0111.d006160 α β r 1 2)

def d008742
    (α β r v₁ v₃ vst : ℝ) : ℝ :=
  |v₁| * (_root_.GD.N0111.d006160 α β r 3 0 *
      _root_.GD.N0113.d008651.d008738 α β ^ 2 / 6)
    + |v₃| * ((17 / 60 : ℝ) *
      _root_.GD.N0111.d006160 α β r 5 0 * _root_.GD.N0113.d008651.d008738 α β ^ 2)
    + |vst| * (_root_.GD.N0111.d006160 α β r 3 1 *
      _root_.GD.N0113.d008651.d008738 α β ^ 2 / 6)

theorem d008743
    {α β : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hN : 1 ≤ N) :
    _root_.GD.N0132.d006444 α β N = _root_.GD.N0113.d008651.d008737 α β / (N : ℝ) := by
  have hν : α + β ≠ 0 := ne_of_gt (add_pos hα hβ)
  have hNR : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  unfold _root_.GD.N0132.d006444 _root_.GD.N0113.d008651.d008737
  field_simp [hν, hNR]

theorem d008744
    {α β : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hN : 1 ≤ N) :
    _root_.GD.N0132.d006443 α β N = _root_.GD.N0113.d008651.d008738 α β / (N : ℝ) := by
  have hNR : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  unfold _root_.GD.N0132.d006443 _root_.GD.N0113.d008651.d008738
  field_simp [hNR]

theorem d008745
    {α β r v₀ v₁ v₂ vt : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hN : 1 ≤ N) :
    _root_.GD.N0146.d008631 α β r v₀ v₁ v₂ vt N =
      _root_.GD.N0113.d008651.d008739 α β r v₀ v₁ v₂ vt / (N : ℝ)
        + _root_.GD.N0113.d008651.d008740 α β r v₁ v₂ / (N : ℝ) ^ 2 := by
  have hNR : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  simp only [_root_.GD.N0146.d008631]
  rw [_root_.GD.N0113.d008651.d008743 hα hβ hN,
    _root_.GD.N0113.d008651.d008744 hα hβ hN]
  unfold _root_.GD.N0113.d008651.d008739 _root_.GD.N0113.d008651.d008740
  field_simp [hNR]
  ring

theorem d008746
    {α β r v₁ v₃ vst : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β) (hN : 1 ≤ N) :
    _root_.GD.N0146.d008635 α β r v₁ v₃ vst N =
      _root_.GD.N0113.d008651.d008741 α β r v₁ v₃ vst / (N : ℝ)
        + _root_.GD.N0113.d008651.d008742 α β r v₁ v₃ vst /
          (N : ℝ) ^ 2 := by
  have hNR : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  simp only [_root_.GD.N0146.d008635]
  rw [_root_.GD.N0113.d008651.d008743 hα hβ hN,
    _root_.GD.N0113.d008651.d008744 hα hβ hN]
  unfold _root_.GD.N0113.d008651.d008741 _root_.GD.N0113.d008651.d008742
  field_simp [hNR]
  ring

theorem d008747
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (H : _root_.GD.N0113.d008646 m n hm hn) :
    (H.C₁ : ℝ) / ((2 ^ H.k : ℕ) : ℝ)
        + (H.C₂ : ℝ) / ((2 ^ H.k : ℕ) : ℝ) ^ 2
      ≤ (H.Cstar : ℝ) / 4 := by
  have hs :
      ((H.C₁ / _root_.GD.N0134.d006546 H.k + H.C₂ / (_root_.GD.N0134.d006546 H.k) ^ 2 : ℚ) : ℝ)
        ≤ ((H.Cstar / 4 : ℚ) : ℝ) := by
    exact_mod_cast H.stopping
  simpa [_root_.GD.N0134.d006546] using hs

theorem d008748
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (H : _root_.GD.N0113.d008646 m n hm hn)
    {α β r v₀ v₁ v₂ vt : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hC₁ :
      _root_.GD.N0113.d008651.d008739 α β r v₀ v₁ v₂ vt ≤ (H.C₁ : ℝ))
    (hC₂ :
      _root_.GD.N0113.d008651.d008740 α β r v₁ v₂ ≤ (H.C₂ : ℝ)) :
    _root_.GD.N0146.d008631 α β r v₀ v₁ v₂ vt (2 ^ H.k)
      ≤ (H.Cstar : ℝ) / 4 := by
  have hN : 1 ≤ (2 ^ H.k : ℕ) := by
    have hp : 0 < (2 ^ H.k : ℕ) := pow_pos (by omega) _
    omega
  rw [_root_.GD.N0113.d008651.d008745 hα hβ hN]
  apply le_trans ?_ (_root_.GD.N0113.d008651.d008747 H)
  gcongr

theorem d008749
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (H : _root_.GD.N0113.d008646 m n hm hn)
    {α β r v₁ v₃ vst : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hC₁ :
      _root_.GD.N0113.d008651.d008741 α β r v₁ v₃ vst ≤ (H.C₁ : ℝ))
    (hC₂ :
      _root_.GD.N0113.d008651.d008742 α β r v₁ v₃ vst ≤ (H.C₂ : ℝ)) :
    _root_.GD.N0146.d008635 α β r v₁ v₃ vst (2 ^ H.k)
      ≤ (H.Cstar : ℝ) / 4 := by
  have hN : 1 ≤ (2 ^ H.k : ℕ) := by
    have hp : 0 < (2 ^ H.k : ℕ) := pow_pos (by omega) _
    omega
  rw [_root_.GD.N0113.d008651.d008746 hα hβ hN]
  apply le_trans ?_ (_root_.GD.N0113.d008651.d008747 H)
  gcongr

theorem d008750
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (H : _root_.GD.N0113.d008646 m n hm hn)
    {α β e r v₀ v₁ v₂ vt : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1) (hr : 0 ≤ r)
    (htarget :
      (H.Cstar : ℝ) ≤
        _root_.GD.N0146.d008630 α β e r v₀ v₁ v₂ vt)
    (hC₁ :
      _root_.GD.N0113.d008651.d008739 α β r v₀ v₁ v₂ vt ≤ (H.C₁ : ℝ))
    (hC₂ :
      _root_.GD.N0113.d008651.d008740 α β r v₁ v₂ ≤ (H.C₂ : ℝ)) :
    _root_.GD.N0146.d008629 α β e r v₀ v₁ v₂ vt (2 ^ H.k)
      ≤ -(3 * (H.Cstar : ℝ) / 4) := by
  apply _root_.GD.N0113.d008651.d008735
    hα hβ he₀ he₁ hr
      (by
        have hp : 0 < (2 ^ H.k : ℕ) := pow_pos (by omega) _
        omega)
      htarget
  exact _root_.GD.N0113.d008651.d008748 H hα hβ hC₁ hC₂

theorem d008751
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (H : _root_.GD.N0113.d008646 m n hm hn)
    {α β e r v₁ v₃ vst : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1) (hr : 0 ≤ r)
    (htarget :
      (H.Cstar : ℝ) ≤ _root_.GD.N0146.d008634 α β e r v₁ v₃ vst)
    (hC₁ :
      _root_.GD.N0113.d008651.d008741 α β r v₁ v₃ vst ≤ (H.C₁ : ℝ))
    (hC₂ :
      _root_.GD.N0113.d008651.d008742 α β r v₁ v₃ vst ≤ (H.C₂ : ℝ)) :
    _root_.GD.N0146.d008633 α β e r v₁ v₃ vst (2 ^ H.k)
      ≤ -(3 * (H.Cstar : ℝ) / 4) := by
  apply _root_.GD.N0113.d008651.d008736
    hα hβ he₀ he₁ hr
      (by
        have hp : 0 < (2 ^ H.k : ℕ) := pow_pos (by omega) _
        omega)
      htarget
  exact _root_.GD.N0113.d008651.d008749 H hα hβ hC₁ hC₂

theorem d008752
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (H : _root_.GD.N0113.d008646 m n hm hn)
    (D : _root_.GD.N0134.d006518) (e : ℝ)
    (hΔ : _root_.GD.N0135.d006594 D ≠ 0)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1)
    (htarget :
      (H.Cstar : ℝ) ≤
        (D.d006522 : ℝ) ^ (-(D.d006524 : ℝ)))
    (hC₁ :
      _root_.GD.N0113.d008651.d008739
        (D.alpha : ℝ) (D.beta : ℝ) (D.d006524 : ℝ)
        (_root_.GD.N0135.d006596 D : ℝ) (_root_.GD.N0135.d006597 D : ℝ)
        (_root_.GD.N0135.d006598 D : ℝ) (_root_.GD.N0135.d006599 D : ℝ) ≤ (H.C₁ : ℝ))
    (hC₂ :
      _root_.GD.N0113.d008651.d008740
        (D.alpha : ℝ) (D.beta : ℝ) (D.d006524 : ℝ)
        (_root_.GD.N0135.d006597 D : ℝ) (_root_.GD.N0135.d006598 D : ℝ) ≤ (H.C₂ : ℝ)) :
    _root_.GD.N0146.d008629
        (D.alpha : ℝ) (D.beta : ℝ) e (D.d006524 : ℝ)
        (_root_.GD.N0135.d006596 D : ℝ) (_root_.GD.N0135.d006597 D : ℝ)
        (_root_.GD.N0135.d006598 D : ℝ) (_root_.GD.N0135.d006599 D : ℝ) (2 ^ H.k)
      ≤ -(3 * (H.Cstar : ℝ) / 4) := by
  have hα : (0 : ℝ) < D.alpha := by exact_mod_cast D.alpha_pos
  have hβ : (0 : ℝ) < D.beta := by exact_mod_cast D.beta_pos
  have hr : (0 : ℝ) ≤ D.d006524 := by
    have h01 : (0 : ℚ) ≤ 1 := by norm_num
    have hrQ : (0 : ℚ) ≤ D.d006524 :=
      h01.trans (le_of_lt (_root_.GD.N0135.d006605 D))
    exact_mod_cast hrQ
  apply _root_.GD.N0113.d008651.d008750
    H hα hβ he₀ he₁ hr ?_ hC₁ hC₂
  rw [_root_.GD.N0129.d008694 D e hΔ]
  exact htarget

theorem d008753
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (H : _root_.GD.N0113.d008646 m n hm hn)
    (D : _root_.GD.N0134.d006518) (e : ℝ)
    (hΔ : _root_.GD.N0135.d006594 D = 0)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1)
    (htarget :
      (H.Cstar : ℝ) ≤
        (D.d006522 : ℝ) ^ (-(D.d006524 : ℝ)))
    (hC₁ :
      _root_.GD.N0113.d008651.d008741
        (D.alpha : ℝ) (D.beta : ℝ) (D.d006524 : ℝ)
        (_root_.GD.N0135.d006600 D : ℝ) (_root_.GD.N0135.d006601 D : ℝ)
        (_root_.GD.N0135.d006602 D : ℝ) ≤ (H.C₁ : ℝ))
    (hC₂ :
      _root_.GD.N0113.d008651.d008742
        (D.alpha : ℝ) (D.beta : ℝ) (D.d006524 : ℝ)
        (_root_.GD.N0135.d006600 D : ℝ) (_root_.GD.N0135.d006601 D : ℝ)
        (_root_.GD.N0135.d006602 D : ℝ) ≤ (H.C₂ : ℝ)) :
    _root_.GD.N0146.d008633
        (D.alpha : ℝ) (D.beta : ℝ) e (D.d006524 : ℝ)
        (_root_.GD.N0135.d006600 D : ℝ) (_root_.GD.N0135.d006601 D : ℝ)
        (_root_.GD.N0135.d006602 D : ℝ) (2 ^ H.k)
      ≤ -(3 * (H.Cstar : ℝ) / 4) := by
  have hα : (0 : ℝ) < D.alpha := by exact_mod_cast D.alpha_pos
  have hβ : (0 : ℝ) < D.beta := by exact_mod_cast D.beta_pos
  have hr : (0 : ℝ) ≤ D.d006524 := by
    have h01 : (0 : ℚ) ≤ 1 := by norm_num
    have hrQ : (0 : ℚ) ≤ D.d006524 :=
      h01.trans (le_of_lt (_root_.GD.N0135.d006605 D))
    exact_mod_cast hrQ
  apply _root_.GD.N0113.d008651.d008751
    H hα hβ he₀ he₁ hr ?_ hC₁ hC₂
  rw [_root_.GD.N0129.d008695 D e hΔ]
  exact htarget

theorem d008754
    {rhoQ : (ℚ × ℚ) → ℝ}
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (H : _root_.GD.N0113.d008646 m n hm hn)
    (D : _root_.GD.N0134.d006518)
    (T : _root_.GD.N0113.d008651 rhoQ D H.k)
    (e : ℝ) (hΔ : _root_.GD.N0135.d006594 D ≠ 0)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1)
    (htarget :
      (H.Cstar : ℝ) ≤
        (D.d006522 : ℝ) ^ (-(D.d006524 : ℝ)))
    (hC₁ :
      _root_.GD.N0113.d008651.d008739
        (D.alpha : ℝ) (D.beta : ℝ) (D.d006524 : ℝ)
        (_root_.GD.N0135.d006596 D : ℝ) (_root_.GD.N0135.d006597 D : ℝ)
        (_root_.GD.N0135.d006598 D : ℝ) (_root_.GD.N0135.d006599 D : ℝ) ≤ (H.C₁ : ℝ))
    (hC₂ :
      _root_.GD.N0113.d008651.d008740
        (D.alpha : ℝ) (D.beta : ℝ) (D.d006524 : ℝ)
        (_root_.GD.N0135.d006597 D : ℝ) (_root_.GD.N0135.d006598 D : ℝ) ≤ (H.C₂ : ℝ)) :
    T.d008711 (_root_.GD.N0113.d008651.d008730 D e)
      ≤ -(3 * (H.Cstar : ℝ) / 4) := by
  rw [_root_.GD.N0113.d008651.d008732 T hΔ e]
  exact _root_.GD.N0113.d008651.d008752
    H D e hΔ he₀ he₁ htarget hC₁ hC₂

theorem d008755
    {rhoQ : (ℚ × ℚ) → ℝ}
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (H : _root_.GD.N0113.d008646 m n hm hn)
    (D : _root_.GD.N0134.d006518)
    (T : _root_.GD.N0113.d008651 rhoQ D H.k)
    (e : ℝ) (hΔ : _root_.GD.N0135.d006594 D = 0)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1)
    (htarget :
      (H.Cstar : ℝ) ≤
        (D.d006522 : ℝ) ^ (-(D.d006524 : ℝ)))
    (hC₁ :
      _root_.GD.N0113.d008651.d008741
        (D.alpha : ℝ) (D.beta : ℝ) (D.d006524 : ℝ)
        (_root_.GD.N0135.d006600 D : ℝ) (_root_.GD.N0135.d006601 D : ℝ)
        (_root_.GD.N0135.d006602 D : ℝ) ≤ (H.C₁ : ℝ))
    (hC₂ :
      _root_.GD.N0113.d008651.d008742
        (D.alpha : ℝ) (D.beta : ℝ) (D.d006524 : ℝ)
        (_root_.GD.N0135.d006600 D : ℝ) (_root_.GD.N0135.d006601 D : ℝ)
        (_root_.GD.N0135.d006602 D : ℝ) ≤ (H.C₂ : ℝ)) :
    T.d008711 (_root_.GD.N0113.d008651.d008730 D e)
      ≤ -(3 * (H.Cstar : ℝ) / 4) := by
  rw [_root_.GD.N0113.d008651.d008733 T hΔ e]
  exact _root_.GD.N0113.d008651.d008753
    H D e hΔ he₀ he₁ htarget hC₁ hC₂











theorem d008756
    {rhoQ : (ℚ × ℚ) → ℝ}
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (D : _root_.GD.N0134.d006518) (hΔ : _root_.GD.N0135.d006594 D ≠ 0) :
    ∃ H : _root_.GD.N0113.d008646 m n hm hn,
      ∀ e : ℝ, 0 ≤ e → e ≤ 1 →
        ∀ T : _root_.GD.N0113.d008651 rhoQ D H.k,
          T.d008711 (_root_.GD.N0113.d008651.d008730 D e)
            ≤ -(3 * (H.Cstar : ℝ) / 4) := by
  let J : ℝ := (D.d006522 : ℝ) ^ (-(D.d006524 : ℝ))
  have hradial : (0 : ℝ) < D.d006522 := by
    exact_mod_cast D.d006531
  have hJ : 0 < J := Real.rpow_pos_of_pos hradial _
  obtain ⟨Cstar : ℚ, hCstar0R, hCstarJ⟩ :=
    exists_rat_btwn hJ
  let L : ℝ :=
    _root_.GD.N0113.d008651.d008739
      (D.alpha : ℝ) (D.beta : ℝ) (D.d006524 : ℝ)
      (_root_.GD.N0135.d006596 D : ℝ) (_root_.GD.N0135.d006597 D : ℝ)
      (_root_.GD.N0135.d006598 D : ℝ) (_root_.GD.N0135.d006599 D : ℝ)
  let Q : ℝ :=
    _root_.GD.N0113.d008651.d008740
      (D.alpha : ℝ) (D.beta : ℝ) (D.d006524 : ℝ)
      (_root_.GD.N0135.d006597 D : ℝ) (_root_.GD.N0135.d006598 D : ℝ)
  obtain ⟨C₁ : ℚ, hC₁R⟩ := exists_rat_gt (max L 0)
  obtain ⟨C₂ : ℚ, hC₂R⟩ := exists_rat_gt (max Q 0)
  have hCstar : (0 : ℚ) < Cstar := by exact_mod_cast hCstar0R
  have hC₁ : (0 : ℚ) ≤ C₁ := by
    have : (0 : ℝ) < (C₁ : ℝ) :=
      lt_of_le_of_lt (le_max_right L 0) hC₁R
    exact_mod_cast this.le
  have hC₂ : (0 : ℚ) ≤ C₂ := by
    have : (0 : ℝ) < (C₂ : ℝ) :=
      lt_of_le_of_lt (le_max_right Q 0) hC₂R
    exact_mod_cast this.le
  obtain ⟨k, hk⟩ :=
    _root_.GD.N0134.d006549 C₁ C₂ Cstar hC₁ hC₂ hCstar
  let H : _root_.GD.N0113.d008646 m n hm hn :=
    { C₁ := C₁
      C₂ := C₂
      Cstar := Cstar
      C₁_nonneg := hC₁
      C₂_nonneg := hC₂
      Cstar_pos := hCstar
      k := k
      stopping := hk }
  refine ⟨H, ?_⟩
  intro e he₀ he₁
  intro T
  apply _root_.GD.N0113.d008651.d008754
    H D T e hΔ he₀ he₁
  · exact hCstarJ.le
  · exact (le_max_left L 0).trans hC₁R.le
  · exact (le_max_left Q 0).trans hC₂R.le

theorem d008757
    {rhoQ : (ℚ × ℚ) → ℝ}
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (D : _root_.GD.N0134.d006518) (hΔ : _root_.GD.N0135.d006594 D = 0) :
    ∃ H : _root_.GD.N0113.d008646 m n hm hn,
      ∀ e : ℝ, 0 ≤ e → e ≤ 1 →
        ∀ T : _root_.GD.N0113.d008651 rhoQ D H.k,
          T.d008711 (_root_.GD.N0113.d008651.d008730 D e)
            ≤ -(3 * (H.Cstar : ℝ) / 4) := by
  let J : ℝ := (D.d006522 : ℝ) ^ (-(D.d006524 : ℝ))
  have hradial : (0 : ℝ) < D.d006522 := by
    exact_mod_cast D.d006531
  have hJ : 0 < J := Real.rpow_pos_of_pos hradial _
  obtain ⟨Cstar : ℚ, hCstar0R, hCstarJ⟩ :=
    exists_rat_btwn hJ
  let L : ℝ :=
    _root_.GD.N0113.d008651.d008741
      (D.alpha : ℝ) (D.beta : ℝ) (D.d006524 : ℝ)
      (_root_.GD.N0135.d006600 D : ℝ) (_root_.GD.N0135.d006601 D : ℝ)
      (_root_.GD.N0135.d006602 D : ℝ)
  let Q : ℝ :=
    _root_.GD.N0113.d008651.d008742
      (D.alpha : ℝ) (D.beta : ℝ) (D.d006524 : ℝ)
      (_root_.GD.N0135.d006600 D : ℝ) (_root_.GD.N0135.d006601 D : ℝ)
      (_root_.GD.N0135.d006602 D : ℝ)
  obtain ⟨C₁ : ℚ, hC₁R⟩ := exists_rat_gt (max L 0)
  obtain ⟨C₂ : ℚ, hC₂R⟩ := exists_rat_gt (max Q 0)
  have hCstar : (0 : ℚ) < Cstar := by exact_mod_cast hCstar0R
  have hC₁ : (0 : ℚ) ≤ C₁ := by
    have : (0 : ℝ) < (C₁ : ℝ) :=
      lt_of_le_of_lt (le_max_right L 0) hC₁R
    exact_mod_cast this.le
  have hC₂ : (0 : ℚ) ≤ C₂ := by
    have : (0 : ℝ) < (C₂ : ℝ) :=
      lt_of_le_of_lt (le_max_right Q 0) hC₂R
    exact_mod_cast this.le
  obtain ⟨k, hk⟩ :=
    _root_.GD.N0134.d006549 C₁ C₂ Cstar hC₁ hC₂ hCstar
  let H : _root_.GD.N0113.d008646 m n hm hn :=
    { C₁ := C₁
      C₂ := C₂
      Cstar := Cstar
      C₁_nonneg := hC₁
      C₂_nonneg := hC₂
      Cstar_pos := hCstar
      k := k
      stopping := hk }
  refine ⟨H, ?_⟩
  intro e he₀ he₁
  intro T
  apply _root_.GD.N0113.d008651.d008755
    H D T e hΔ he₀ he₁
  · exact hCstarJ.le
  · exact (le_max_left L 0).trans hC₁R.le
  · exact (le_max_left Q 0).trans hC₂R.le

theorem d008758
    {rhoQ : (ℚ × ℚ) → ℝ}
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (D : _root_.GD.N0134.d006518) :
    ∃ H : _root_.GD.N0113.d008646 m n hm hn,
      ∀ e : ℝ, 0 ≤ e → e ≤ 1 →
        ∀ T : _root_.GD.N0113.d008651 rhoQ D H.k,
          T.d008711 (_root_.GD.N0113.d008651.d008730 D e)
            ≤ -(3 * (H.Cstar : ℝ) / 4) := by
  by_cases hΔ : _root_.GD.N0135.d006594 D = 0
  · exact _root_.GD.N0113.d008651.d008757
      D hΔ
  · exact _root_.GD.N0113.d008651.d008756
      D hΔ

end
end d008651
end GD.N0113
