import GD.Module1646
import GD.Module1649
import GD.Module1891

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GD.N0078

noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0074
open _root_.GD.N0079.N0319
open _root_.GD.N0079.N0322
open _root_.GD.N0079.N0323
open _root_.GD.N0076.N0314
open _root_.GD.N0078.N0316

def d030771 : Prop :=
  (∀ (k : ℕ) (sizes : Fin k → ℕ), (∀ i, 2 ≤ sizes i) →
    ∀ B : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞, B (_root_.GD.N0232.N0719.N0859.d010810 k) ≠ ∞ →
    (_root_.GD.N0078.N0316.d028047 k sizes B ↔ _root_.GD.N0078.N0316.d028048 k sizes B) ∧
    (_root_.GD.N0078.N0316.d028047 k sizes B ↔ _root_.GD.N0078.N0316.d028049 k sizes B)) ∧
  (∀ (k : ℕ) (sizes : Fin k → ℕ), (∀ i, 2 ≤ sizes i) →
    ∀ d : _root_.GD.N0074.d023612 k sizes,
    (_root_.GD.N0079.N0319.d027977 k sizes d.val ↔ _root_.GD.N0079.N0319.d027994 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027977 k sizes d.val ↔ _root_.GD.N0079.N0322.d028031 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027977 k sizes d.val ↔ _root_.GD.N0079.N0319.d027989 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027977 k sizes d.val → _root_.GD.N0079.N0319.d027973 k sizes d.val)) ∧
  (∀ (k : ℕ) (sizes : Fin k → ℕ), (∀ i, 2 ≤ sizes i) →
    ∀ d : _root_.GD.N0074.d023612 k sizes,
    (_root_.GD.N0079.N0319.d027978 k sizes d.val ↔ _root_.GD.N0079.N0319.d027995 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027978 k sizes d.val ↔ _root_.GD.N0079.N0322.d028032 k sizes d.val) ∧
    (_root_.GD.N0079.N0319.d027978 k sizes d.val ↔ _root_.GD.N0079.N0319.d027990 k sizes d.val))

theorem d030772 : _root_.GD.N0078.d030771 :=
  ⟨_root_.GD.N0078.N0316.d028054, _root_.GD.N0078.N0316.d028055, _root_.GD.N0078.N0316.d028056⟩

def d030773 : Prop :=
  (∀ (Θ D S : Type) (R : Θ → D → ℝ≥0∞) (r : Θ → S → ℝ≥0∞)
      (F : _root_.GD.N0079.N0323.d008229 R r) (s : S),
    _root_.GD.N0079.N0323.d008228 R (F.embed s) ↔ _root_.GD.N0079.N0323.d008228 r s ∧
      ∀ d, _root_.GD.N0079.N0323.d008225 R d (F.embed s) → F.project d = s → d = F.embed s) ∧
  (∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y]
      (μ : Measure X) (ν : Measure Y) (κ : Kernel X Y) (c : ℝ),
    κ ∘ₘ μ = ν ↔ ∀ d : Y → ℝ, Measurable d →
      _root_.GD.N0076.N0314.d028069 μ κ c d = _root_.GD.N0076.N0312.d022661 ν c d) ∧
  (∀ θ : _root_.GD.N0232.N0719.N0859.d010809 2,
    (_root_.GD.N0232.N0719.N0859.d010812 2 (fun _ => 3) θ).map _root_.GD.N0076.N0314.d028076 = _root_.GD.N0232.N0719.N0859.d010812 2 (fun _ => 2) θ) ∧
  (¬ ∃ f : _root_.GD.N0232.N0719.N0900.d009094 2 (fun _ => 2) → ℝ,
    _root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 3) = f ∘ _root_.GD.N0076.N0314.d028076)

theorem d030774 : _root_.GD.N0078.d030773 :=
  ⟨fun _ _ _ _ _ => _root_.GD.N0076.N0314.d028063,
    fun _ _ _ _ => _root_.GD.N0076.N0314.d028071,
    _root_.GD.N0076.N0314.d028079, _root_.GD.N0076.N0314.d028084⟩

theorem d030775 :
    _root_.GD.N0078.d030771 ∧ _root_.GD.N0078.d030773 ∧
    _root_.GD.N0078.N0317.d030766 3 3 (by omega) (by omega) :=
  ⟨_root_.GD.N0078.d030772, _root_.GD.N0078.d030774,
    _root_.GD.N0078.N0317.d030769⟩

end
end GD.N0078

#print axioms _root_.GD.N0078.d030772
#print axioms _root_.GD.N0078.d030774
#print axioms _root_.GD.N0078.d030775
