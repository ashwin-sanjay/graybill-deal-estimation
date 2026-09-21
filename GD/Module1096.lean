import GD.Module1094

















open MeasureTheory

namespace GD
namespace N0232
namespace N0720
namespace N1187

noncomputable section

open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1166
open _root_.GD.N0232.N0720.N1168
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1183
open _root_.GD.N0232.N0720.N1185
open _root_.GD.N0232.N0720.N1190
open _root_.GD.N0232.N0720.N1486

abbrev d017602 :=
  _root_.GD.N0232.N0720.N1173.d015933



theorem d017603
    (k : ℕ) :
    _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 _root_.GD.N0232.N0720.N1166.d017433 k
          _root_.GD.N0232.N0720.N1185.d017526 -
        _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 _root_.GD.N0232.N0720.N1166.d017433 k
          (_root_.GD.N0232.N0720.N1166.d017479 k) =
      _root_.GD.N0232.N0720.N1185.d017514
        _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1190.d017536
          (_root_.GD.N0232.N0720.N1166.d017432 k) := by
  have h :=
    _root_.GD.N0232.N0720.N1183.d017569.d017571
      _root_.GD.N0232.N0720.N1166.d017432
      _root_.GD.N0232.N0720.N1168.d017581 k
  rw [_root_.GD.N0232.N0720.N1168.d017575,
    _root_.GD.N0232.N0720.N1168.d017580
      _root_.GD.N0232.N0720.N1168.d017581.legal] at h
  exact h

end

end N1187
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1187.d017603
