import GD.Module1083
import GD.Module1024
















open MeasureTheory

namespace GD
namespace N0232
namespace N0720
namespace N1494

noncomputable section

open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1485


def d017426 (k : ℕ) :
    Measure _root_.GD.N0232.N0720.N1486.d015856 :=
  _root_.GD.N0232.N0720.N1485.d017373
    _root_.GD.N0232.N0720.N1493.d016104 k

noncomputable instance d017427 (k : ℕ) :
    IsFiniteMeasure (_root_.GD.N0232.N0720.N1494.d017426 k) := by
  unfold _root_.GD.N0232.N0720.N1494.d017426
  infer_instance



theorem d017428 :
    _root_.GD.N0232.N0720.N1111.d016605 _root_.GD.N0232.N0720.N1494.d017426 := by
  exact
    _root_.GD.N0232.N0720.N1485.d017378
      _root_.GD.N0232.N0720.N1493.d016104








theorem d017429
    (prior : ℕ → Measure _root_.GD.N0232.N0720.N1486.d015856)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hdom : ∀ N, ∃ K, ∀ k ≥ K,
      _root_.GD.N0232.N0720.N1494.d017426 N ≤ prior k) :
    _root_.GD.N0232.N0720.N1111.d016605 prior := by
  intro theta U hU
  obtain ⟨a, ha, N, hN⟩ :=
    _root_.GD.N0232.N0720.N1494.d017428
      theta U hU
  obtain ⟨K, hK⟩ := hdom N
  refine ⟨a, ha, K, ?_⟩
  intro k hk
  letI : IsFiniteMeasure (prior k) := hpriorFinite k
  have hmeasure :
      _root_.GD.N0232.N0720.N1494.d017426 N U ≤ prior k U :=
    hK k hk U
  exact (hN N le_rfl).trans
    ((ENNReal.toReal_le_toReal
      (measure_ne_top (_root_.GD.N0232.N0720.N1494.d017426 N) U)
      (measure_ne_top (prior k) U)).2 hmeasure)

end


end N1494
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1494.d017428
#print axioms _root_.GD.N0232.N0720.N1494.d017429
