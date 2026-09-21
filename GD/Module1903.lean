import GD.Module1902
import GD.Module1212

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0009
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0230.N0637
open _root_.GD.N0082.N0335
open _root_.GD.N0149.N0432
open _root_.GD.N0232.N0720.N1089 _root_.GD.N0010

def d030861 (H : ℝ → ℝ) : ℝ → ℝ := fun u => _root_.GD.N0230.N0637.d000240 (H u)

theorem d030862 (H : ℝ → ℝ) (hH : Measurable H) :
    Measurable (_root_.GD.N0009.d030861 H) :=
  _root_.GD.N0230.N0660.d000890.measurable.comp hH

theorem d030863 (H : ℝ → ℝ) (u : ℝ) :
    _root_.GD.N0009.d030861 H u ∈ Icc (0 : ℝ) 1 := _root_.GD.N0230.N0637.d000243 (H u)



theorem d030864 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (H : ℝ → ℝ) (hH : Measurable H) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0082.N0335.d030724 m n (_root_.GD.N0009.d030861 H)) ≤
      _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0082.N0335.d030724 m n H) := by
  by_cases ht : _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0082.N0335.d030724 m n H) = ⊤
  · rw [ht]
    exact le_top
  exact _root_.GD.N0232.N0720.N1398.d019600
    m n hm hn θ (hH.comp measurable_fst) ht

theorem d030865 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (H : ℝ → ℝ) (hH : Measurable H) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 m n θ (_root_.GD.N0082.N0335.d030724 m n (_root_.GD.N0009.d030861 H)) ≤
      _root_.GD.N0232.N0720.N1256.d015547 m n θ (_root_.GD.N0082.N0335.d030724 m n H) :=
  ENNReal.div_le_div_right (_root_.GD.N0009.d030864 m n hm hn H hH θ)
    (ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ))

theorem d030866 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (H : ℝ → ℝ) (hH : Measurable H) :
    _root_.GD.N0232.N0720.N1256.d015548 m n (_root_.GD.N0082.N0335.d030724 m n (_root_.GD.N0009.d030861 H)) ≤
      _root_.GD.N0232.N0720.N1256.d015548 m n (_root_.GD.N0082.N0335.d030724 m n H) :=
  iSup_mono (_root_.GD.N0009.d030865 m n hm hn H hH)



theorem d030867 (H : ℝ → ℝ) (hH : Measurable H) :
    ENNReal.ofReal (1 + Real.pi / 4) ≤ _root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H) :=
  (_root_.GD.N0010.d030850 (_root_.GD.N0009.d030861 H) (_root_.GD.N0009.d030862 H hH)
    (_root_.GD.N0009.d030863 H)).trans
    (_root_.GD.N0009.d030866 3 3 (by omega) (by omega) H hH)

theorem d030868 :
    IsLeast ((fun H : ℝ → ℝ => _root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H)) ''
      {H | Measurable H}) (ENNReal.ofReal (1 + Real.pi / 4)) := by
  constructor
  · exact ⟨_root_.GD.N0232.N0720.N1089.d003092, _root_.GD.N0149.N0432.d008282, _root_.GD.N0010.d030853⟩
  · rintro x ⟨H, hH, rfl⟩
    exact _root_.GD.N0009.d030867 H hH

theorem d030869 (H : ℝ → ℝ) (hH : Measurable H)
    (hdom : ∀ θ : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤
      _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1256.d015547 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤ ENNReal.ofReal C) :
    2 ≤ C :=
  _root_.GD.N0010.d030859 (_root_.GD.N0009.d030861 H) (_root_.GD.N0009.d030862 H hH)
    (_root_.GD.N0009.d030863 H)
    (fun θ => (_root_.GD.N0009.d030864 3 3 (by omega) (by omega) H hH θ).trans (hdom θ))
    C hC
    (fun θ => (_root_.GD.N0009.d030865 3 3 (by omega) (by omega) H hH θ).trans (hcap θ))



theorem d030870 :
    ¬ ∃ H : ℝ → ℝ, Measurable H ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤
        _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ) ∧
      _root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H) ≤ _root_.GD.N0232.N0720.N1256.d015549 3 3 := by
  rintro ⟨H, hH, hdom, hmin⟩
  exact _root_.GD.N0010.d030860
    ⟨_root_.GD.N0009.d030861 H, _root_.GD.N0009.d030862 H hH, _root_.GD.N0009.d030863 H,
      (fun θ => (_root_.GD.N0009.d030864 3 3 (by omega) (by omega) H hH θ).trans (hdom θ)),
      (_root_.GD.N0009.d030866 3 3 (by omega) (by omega) H hH).trans hmin⟩

end
end GD.N0009

#print axioms _root_.GD.N0009.d030862
#print axioms _root_.GD.N0009.d030863
#print axioms _root_.GD.N0009.d030864
#print axioms _root_.GD.N0009.d030865
#print axioms _root_.GD.N0009.d030866
#print axioms _root_.GD.N0009.d030867
#print axioms _root_.GD.N0009.d030868
#print axioms _root_.GD.N0009.d030869
#print axioms _root_.GD.N0009.d030870
