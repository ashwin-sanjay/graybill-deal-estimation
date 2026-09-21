import GD.Module0603














open Set

namespace GD.N0113
namespace d008651

noncomputable section

open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0135
open _root_.GD.N0146
open _root_.GD.N0132
open _root_.GD.N0130
open _root_.GD.N0110

theorem d008728
    (D : _root_.GD.N0134.d006518) (k : ℕ) :
    (_root_.GD.N0134.d006550 D k : ℝ) =
      _root_.GD.N0132.d006443 (D.alpha : ℝ) (D.beta : ℝ) (2 ^ k) := by
  have hα : (0 : ℝ) < D.alpha := by exact_mod_cast D.alpha_pos
  have hβ : (0 : ℝ) < D.beta := by exact_mod_cast D.beta_pos
  have hν : (D.alpha : ℝ) + D.beta ≠ 0 := by positivity
  have hN : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  simp only [_root_.GD.N0134.d006550, _root_.GD.N0134.d006546, _root_.GD.N0132.d006443, _root_.GD.N0132.d006442, _root_.GD.N0134.d006518.d006523, _root_.GD.N0134.d006518.d006519,
    Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_min, Nat.cast_pow, Nat.cast_ofNat]
  push_cast
  field_simp [hν]
  ring

theorem d008729
    (D : _root_.GD.N0134.d006518) (k : ℕ) :
    (_root_.GD.N0134.d006551 D k : ℝ) =
      _root_.GD.N0132.d006444 (D.alpha : ℝ) (D.beta : ℝ) (2 ^ k) := by
  have hα : (0 : ℝ) < D.alpha := by exact_mod_cast D.alpha_pos
  have hβ : (0 : ℝ) < D.beta := by exact_mod_cast D.beta_pos
  have hν : (D.alpha : ℝ) + D.beta ≠ 0 := by positivity
  have hN : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  simp only [_root_.GD.N0134.d006551, _root_.GD.N0134.d006546, _root_.GD.N0132.d006444, _root_.GD.N0134.d006518.d006522, _root_.GD.N0134.d006518.d006519,
    Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow,
    Nat.cast_pow, Nat.cast_ofNat]
  push_cast
  field_simp [hν]

def d008730
    (D : _root_.GD.N0134.d006518) (e : ℝ) (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0132.d006445 (D.alpha : ℝ) (D.beta : ℝ) e
    (D.d006524 : ℝ) (p.1 - (D.d006520 : ℝ)) p.2

theorem d008731
    {rhoQ : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (carrier : ℝ × ℝ → ℝ) :
    T.d008711 carrier =
      ((_root_.GD.N0146.d008622 D k).map fun a =>
        (a.weight : ℝ) * carrier ((a.ell : ℝ), (a.f : ℝ))).sum := by
  unfold _root_.GD.N0113.d008651.d008711 _root_.GD.N0113.d008651.d008699 _root_.GD.N0113.d008651.d008698 _root_.GD.N0113.d008651.d008652
  rw [← List.sum_ofFn]
  congr 1
  calc
    List.ofFn
        (fun i =>
          (((_root_.GD.N0146.d008622 D k).get i).weight : ℝ) *
            carrier
              ((((_root_.GD.N0146.d008622 D k).get i).ell : ℝ),
                (((_root_.GD.N0146.d008622 D k).get i).f : ℝ))) =
      (List.ofFn (_root_.GD.N0146.d008622 D k).get).map
        (fun a =>
          (a.weight : ℝ) *
            carrier ((a.ell : ℝ), (a.f : ℝ))) := by
        simpa only [Function.comp_apply] using
          (List.ofFn_comp' (_root_.GD.N0146.d008622 D k).get
            (fun a =>
              (a.weight : ℝ) *
                carrier ((a.ell : ℝ), (a.f : ℝ))))
    _ = (_root_.GD.N0146.d008622 D k).map
        (fun a =>
          (a.weight : ℝ) *
            carrier ((a.ell : ℝ), (a.f : ℝ))) := by
      rw [List.ofFn_get]

theorem d008732
    {rhoQ : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (hdelta : _root_.GD.N0135.d006594 D ≠ 0) (e : ℝ) :
    T.d008711 (_root_.GD.N0113.d008651.d008730 D e) =
      _root_.GD.N0146.d008629
        (D.alpha : ℝ) (D.beta : ℝ) e (D.d006524 : ℝ)
        (_root_.GD.N0135.d006596 D : ℝ) (_root_.GD.N0135.d006597 D : ℝ)
        (_root_.GD.N0135.d006598 D : ℝ) (_root_.GD.N0135.d006599 D : ℝ) (2 ^ k) := by
  simp only [_root_.GD.N0146.d008629]
  rw [← _root_.GD.N0113.d008651.d008728 D k,
    ← _root_.GD.N0113.d008651.d008729 D k]
  rw [_root_.GD.N0113.d008651.d008731]
  simp only [_root_.GD.N0146.d008622, if_neg hdelta, _root_.GD.N0135.d006607,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [_root_.GD.N0113.d008651.d008730, _root_.GD.N0110.d006121, _root_.GD.N0110.d006122,
    _root_.GD.N0130.d006472, _root_.GD.N0110.d006130]
  rw [← _root_.GD.N0113.d008651.d008729 D k]
  simp only [_root_.GD.N0132.d006446, _root_.GD.N0132.d006445,
    _root_.GD.N0111.d006148]
  simp only [_root_.GD.N0136.d006564,
    _root_.GD.N0136.d006565,
    _root_.GD.N0136.d006566,
    _root_.GD.N0136.d006567,
    Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_neg, Rat.cast_pow, Rat.cast_ofNat]
  push_cast
  ring

theorem d008733
    {rhoQ : (ℚ × ℚ) → ℝ}
    {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (hdelta : _root_.GD.N0135.d006594 D = 0) (e : ℝ) :
    T.d008711 (_root_.GD.N0113.d008651.d008730 D e) =
      _root_.GD.N0146.d008633
        (D.alpha : ℝ) (D.beta : ℝ) e (D.d006524 : ℝ)
        (_root_.GD.N0135.d006600 D : ℝ) (_root_.GD.N0135.d006601 D : ℝ)
        (_root_.GD.N0135.d006602 D : ℝ) (2 ^ k) := by
  simp only [_root_.GD.N0146.d008633]
  rw [← _root_.GD.N0113.d008651.d008728 D k,
    ← _root_.GD.N0113.d008651.d008729 D k]
  rw [_root_.GD.N0113.d008651.d008731]
  simp only [_root_.GD.N0146.d008622, if_pos hdelta, _root_.GD.N0135.d006608,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [_root_.GD.N0113.d008651.d008730, _root_.GD.N0110.d006121, _root_.GD.N0110.d006123,
    _root_.GD.N0130.d006472, _root_.GD.N0110.d006130]
  rw [← _root_.GD.N0113.d008651.d008729 D k]
  simp only [_root_.GD.N0132.d006445,
    _root_.GD.N0136.d006573,
    _root_.GD.N0136.d006574,
    _root_.GD.N0136.d006575,
    _root_.GD.N0136.d006576,
    _root_.GD.N0136.d006577,
    _root_.GD.N0136.d006578,
    Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_neg, Rat.cast_pow, Rat.cast_ofNat]
  push_cast
  ring

theorem d008734
    {action target error C : ℝ}
    (herror : |action + target| ≤ error)
    (htarget : C ≤ target)
    (hbudget : error ≤ C / 4) :
    action ≤ -(3 * C / 4) := by
  have hupper : action + target ≤ error :=
    (le_abs_self (action + target)).trans herror
  linarith

theorem d008735
    {α β e r v₀ v₁ v₂ vt C : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N)
    (htarget :
      C ≤ _root_.GD.N0146.d008630 α β e r v₀ v₁ v₂ vt)
    (hbudget :
      _root_.GD.N0146.d008631 α β r v₀ v₁ v₂ vt N ≤ C / 4) :
    _root_.GD.N0146.d008629 α β e r v₀ v₁ v₂ vt N
      ≤ -(3 * C / 4) :=
  _root_.GD.N0113.d008651.d008734
    (_root_.GD.N0146.d008632
      hα hβ he₀ he₁ hr hN) htarget hbudget

theorem d008736
    {α β e r v₁ v₃ vst C : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he₀ : 0 ≤ e) (he₁ : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N)
    (htarget :
      C ≤ _root_.GD.N0146.d008634 α β e r v₁ v₃ vst)
    (hbudget :
      _root_.GD.N0146.d008635 α β r v₁ v₃ vst N ≤ C / 4) :
    _root_.GD.N0146.d008633 α β e r v₁ v₃ vst N
      ≤ -(3 * C / 4) :=
  _root_.GD.N0113.d008651.d008734
    (_root_.GD.N0146.d008636
      hα hβ he₀ he₁ hr hN) htarget hbudget

end
end d008651
end GD.N0113
