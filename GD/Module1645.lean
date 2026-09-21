import GD.Module1637
import GD.Module0553

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0079.N0324

noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N1012 _root_.GD.N0074 _root_.GD.N0079.N0323

variable (k : ℕ) (sizes : Fin k → ℕ)

def d028039 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0074.d023612 k sizes) : ℝ≥0∞ :=
  _root_.GD.N0232.N0719.N0859.d010821 k sizes θ d.val

def d028040 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0074.d023614 k sizes) : ℝ≥0∞ :=
  _root_.GD.N0079.N0324.d028039 k sizes θ d.val

def d028041 (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0079.N0323.d008229 (_root_.GD.N0079.N0324.d028039 k sizes) (_root_.GD.N0079.N0324.d028040 k sizes) where
  embed := Subtype.val
  project := _root_.GD.N0074.d023620 k sizes hsizes
  retract := _root_.GD.N0074.d023622 k sizes hsizes
  preserve _ _ := rfl
  improve θ d := _root_.GD.N0232.N0719.N1012.d011407 k sizes hsizes θ d.val

theorem d028042 (hsizes : ∀ i, 2 ≤ sizes i) (B : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) :
    (∃ d : _root_.GD.N0074.d023612 k sizes, ∀ θ, _root_.GD.N0079.N0324.d028039 k sizes θ d ≤ B θ) ↔
      (∃ s : _root_.GD.N0074.d023614 k sizes, ∀ θ, _root_.GD.N0079.N0324.d028040 k sizes θ s ≤ B θ) :=
  (_root_.GD.N0079.N0324.d028041 k sizes hsizes).d008238 B

theorem d028043 (hsizes : ∀ i, 2 ≤ sizes i)
    {W : Type*} [CompleteLattice W]
    (Φ : (_root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) → W) (hΦ : Monotone Φ) :
    (⨅ d : _root_.GD.N0074.d023612 k sizes, Φ (fun θ => _root_.GD.N0079.N0324.d028039 k sizes θ d)) =
      ⨅ s : _root_.GD.N0074.d023614 k sizes, Φ (fun θ => _root_.GD.N0079.N0324.d028040 k sizes θ s) :=
  (_root_.GD.N0079.N0324.d028041 k sizes hsizes).d008240 Φ hΦ

theorem d028044 (hsizes : ∀ i, 2 ≤ sizes i)
    {W : Type*} [Preorder W]
    (Φ : (_root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) → W) (hΦ : Monotone Φ) :
    (∃ d : _root_.GD.N0074.d023612 k sizes, ∀ e : _root_.GD.N0074.d023612 k sizes,
      Φ (fun θ => _root_.GD.N0079.N0324.d028039 k sizes θ d) ≤ Φ (fun θ => _root_.GD.N0079.N0324.d028039 k sizes θ e)) ↔
      (∃ s : _root_.GD.N0074.d023614 k sizes, ∀ t : _root_.GD.N0074.d023614 k sizes,
      Φ (fun θ => _root_.GD.N0079.N0324.d028040 k sizes θ s) ≤ Φ (fun θ => _root_.GD.N0079.N0324.d028040 k sizes θ t)) :=
  (_root_.GD.N0079.N0324.d028041 k sizes hsizes).d008241 Φ hΦ

theorem d028045 (hsizes : ∀ i, 2 ≤ sizes i) :
    (⨅ d : _root_.GD.N0074.d023612 k sizes, ⨆ θ, _root_.GD.N0079.N0324.d028039 k sizes θ d) =
      ⨅ s : _root_.GD.N0074.d023614 k sizes, ⨆ θ, _root_.GD.N0079.N0324.d028040 k sizes θ s :=
  _root_.GD.N0079.N0324.d028043 k sizes hsizes (fun r => ⨆ θ, r θ)
    (fun _ _ h => iSup_mono h)

theorem d028046 (hsizes : ∀ i, 2 ≤ sizes i) (s : _root_.GD.N0074.d023614 k sizes) :
    _root_.GD.N0079.N0323.d008227 (_root_.GD.N0079.N0324.d028039 k sizes) s.val ↔ _root_.GD.N0079.N0323.d008227 (_root_.GD.N0079.N0324.d028040 k sizes) s :=
  (_root_.GD.N0079.N0324.d028041 k sizes hsizes).d008235 s

end
end GD.N0079.N0324

#print axioms _root_.GD.N0079.N0324.d028041
#print axioms _root_.GD.N0079.N0324.d028042
#print axioms _root_.GD.N0079.N0324.d028043
#print axioms _root_.GD.N0079.N0324.d028044
#print axioms _root_.GD.N0079.N0324.d028045
#print axioms _root_.GD.N0079.N0324.d028046
