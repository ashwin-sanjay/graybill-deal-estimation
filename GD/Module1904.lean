import GD.Module1903
import GD.Module1656

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0214.N0529
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1256
open _root_.GD.N0082.N0335



theorem d030871 (H : ℝ → ℝ) (hH : Measurable H)
    (hdom : ∀ θ : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤
      _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ) :
    2 ≤ _root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H) := by
  by_cases ht : _root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H) = ⊤
  · rw [ht]
    exact le_top
  let C := (_root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H)).toReal
  have hC : ENNReal.ofReal C = _root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H) :=
    ENNReal.ofReal_toReal ht
  have hcap (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1256.d015547 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤
      ENNReal.ofReal C := by
    rw [hC]
    exact le_iSup (fun θ => _root_.GD.N0232.N0720.N1256.d015547 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H)) θ
  have hfloor := _root_.GD.N0009.d030869
    H hH hdom C ENNReal.toReal_nonneg hcap
  rw [← hC]
  simpa using ENNReal.ofReal_le_ofReal hfloor

theorem d030872
    (H : ℝ → ℝ) (hH : Measurable H)
    (hdom : ∀ θ : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤
      _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ) :
    _root_.GD.N0232.N0720.N1256.d015549 3 3 < _root_.GD.N0232.N0720.N1256.d015548 3 3 (_root_.GD.N0082.N0335.d030724 3 3 H) :=
  _root_.GD.N0010.d030856.trans_le
    (_root_.GD.N0214.N0529.d030871 H hH hdom)



theorem d030873 :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 3 3, _root_.GD.N0098.d028160 3 3 d ∧
      _root_.GD.N0232.N0720.N1256.d015548 3 3 d = _root_.GD.N0232.N0720.N1256.d015549 3 3 ∧
      _root_.GD.N0232.N0720.N1256.d015548 3 3 d ≤ ENNReal.ofReal (1 + Real.pi / 4) := by
  obtain ⟨d, hd, ht, hv⟩ := _root_.GD.N0098.d028161
    3 3 (by omega) (by omega)
  exact ⟨d, hd, ht, hv, hv.le.trans
    _root_.GD.N0010.d030855⟩

end
end GD.N0214.N0529

#print axioms _root_.GD.N0214.N0529.d030871
#print axioms _root_.GD.N0214.N0529.d030872
#print axioms _root_.GD.N0214.N0529.d030873
