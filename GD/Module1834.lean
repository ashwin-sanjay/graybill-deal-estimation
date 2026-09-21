import GD.Module1833
import GD.Module1643

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0024.N0270

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1295 _root_.GD.N0232.N0720.N1446
open _root_.GD.N0232.N0720.N1047
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1425
open _root_.GD.N0046.N0305

theorem d030251
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n (_root_.GD.N0232.N0720.N1446.d019024 θ) (_root_.GD.N0232.N0720.N1080.d014175 m n) =
      _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) := by
  rw [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn,
    _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
  exact _root_.GD.N0232.N0720.N1446.d019039 m n (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn) θ

theorem d030252
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v)
    (hK : (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ,
      Measurable g ∧ (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ θ,
        _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
          ENNReal.ofReal (v * _root_.GD.N0232.N0720.N1257.d015508 m n θ) ∧
        _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
          _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) := by
  obtain ⟨e, he, hequiv, heb⟩ :=
    _root_.GD.N0024.N0269.d030250 m n hm hn v hv hvalue hK
  let B : _root_.GD.N0232.N0720.N1080.d014168 → ℝ≥0∞ := fun θ =>
    min (ENNReal.ofReal (v * _root_.GD.N0232.N0720.N1257.d015508 m n θ))
      (_root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n))
  have hefinite : e ∈ _root_.GD.N0232.N0720.N1256.d015551 m n :=
    ⟨he, fun θ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (heb θ).1⟩
  have hBfinite (θ : _root_.GD.N0232.N0720.N1080.d014168) : B θ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  have hBreflection (θ : _root_.GD.N0232.N0720.N1080.d014168) : B (_root_.GD.N0232.N0720.N1446.d019024 θ) = B θ := by
    dsimp only [B]
    rw [_root_.GD.N0024.N0270.d030251 m n hm hn]
    rfl
  obtain ⟨g, hg, hgb, hgrisk⟩ :=
    _root_.GD.N0024.N0271.d028029 m n hm hn
      e hefinite ((_root_.GD.N0232.N0720.N1295.d019240 m n e).mpr hequiv)
      B hBfinite hBreflection (fun θ => le_min (heb θ).1 (heb θ).2)
  exact ⟨g, hg, hgb, fun θ => ⟨(hgrisk θ).trans (min_le_left _ _),
    (hgrisk θ).trans (min_le_right _ _)⟩⟩

end
end GD.N0024.N0270

#print axioms _root_.GD.N0024.N0270.d030251
#print axioms _root_.GD.N0024.N0270.d030252
