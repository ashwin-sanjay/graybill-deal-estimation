import GD.Module0911
import GD.Module0217






















namespace GD
namespace N0232
namespace N0720
namespace N1084

noncomputable section

open _root_.GD.N0107 _root_.GD.N0137
open _root_.GD.N0232.N0720.N1437


def d014252
    (m n : ℕ) (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0107.d009085 omega.1 / m


def d014253
    (m n : ℕ) (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0107.d009085 omega.2 / n



def d014254
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (r s : ℝ) : ℝ :=
  r + (U.step : ℝ) * U.emitted.table.d008659 (r, s)



theorem d014255
    (m n : ℕ) (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009091 m n
        (_root_.GD.N0107.d009085 omega.1)
        (_root_.GD.N0107.d009085 omega.2) =
      _root_.GD.N0232.N0720.N1437.d002996 (_root_.GD.N0232.N0720.N1084.d014252 m n omega)
        (_root_.GD.N0232.N0720.N1084.d014253 m n omega) := by
  rfl



theorem d014256
    (m n : ℕ) (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009093 m n omega =
      _root_.GD.N0232.N0720.N1437.d002997
        (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)
        (_root_.GD.N0232.N0720.N1084.d014252 m n omega) (_root_.GD.N0232.N0720.N1084.d014253 m n omega) := by
  rfl


theorem d014257
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0720.d014159 U omega =
      U.emitted.table.d008659
        (_root_.GD.N0232.N0720.N1437.d002996 (_root_.GD.N0232.N0720.N1084.d014252 m n omega)
            (_root_.GD.N0232.N0720.N1084.d014253 m n omega),
          _root_.GD.N0232.N0720.N1437.d002997
            (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)
            (_root_.GD.N0232.N0720.N1084.d014252 m n omega) (_root_.GD.N0232.N0720.N1084.d014253 m n omega)) := by
  rfl



theorem d014258
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d012734 m n (U.step : ℝ) (_root_.GD.N0232.N0720.d014159 U) omega =
      _root_.GD.N0232.N0720.N1437.d002998 (_root_.GD.N0232.N0720.N1084.d014254 U)
        (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)
        (_root_.GD.N0232.N0720.N1084.d014252 m n omega) (_root_.GD.N0232.N0720.N1084.d014253 m n omega) := by
  unfold _root_.GD.N0107.d012734 _root_.GD.N0107.d012733 _root_.GD.N0232.N0720.N1437.d002998
    _root_.GD.N0232.N0720.N1084.d014254
  rw [_root_.GD.N0232.N0720.N1084.d014255 m n omega,
    _root_.GD.N0232.N0720.N1084.d014257 U omega]
  unfold _root_.GD.N0107.d009090
  ring

end

end N1084
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1084.d014255
#print axioms _root_.GD.N0232.N0720.N1084.d014256
#print axioms _root_.GD.N0232.N0720.N1084.d014257
#print axioms _root_.GD.N0232.N0720.N1084.d014258
