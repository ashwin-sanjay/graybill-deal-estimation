import GD.Module1128
import GD.Module0218


















open MeasureTheory

namespace GD
namespace N0232
namespace N0720
namespace N1459

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0107
open _root_.GD.N0137
open _root_.GD.N0232.N0720.N1154
open _root_.GD.N0232.N0720.N1460
open _root_.GD.N0232.N0720.N1467



def d018930
    (m n : ℕ) (d : ℝ → ℝ → ℝ → ℝ → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  d ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 0)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 1)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1)



def d018931
    (m n : ℕ) (d : ℝ → ℝ → ℝ → ℝ → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1460.d003027 (_root_.GD.N0232.N0720.N1460.d003029 d)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 0)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 1)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1)



theorem d018932
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      0 < (_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0 ∧
        0 < (_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1 := by
  have hm0 : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hm)
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  have hm1 : (0 : ℝ) < (m - 1 : ℕ) := by
    exact_mod_cast (Nat.sub_pos_of_lt (lt_of_lt_of_le (by omega : 1 < 2) hm))
  have hn1 : (0 : ℝ) < (n - 1 : ℕ) := by
    exact_mod_cast (Nat.sub_pos_of_lt (lt_of_lt_of_le (by omega : 1 < 2) hn))
  filter_upwards [_root_.GD.N0232.N0720.N1154.d018176 m n hm hn] with
      omega homega
  constructor
  · rw [_root_.GD.N0232.N0720.N1467.d012547]
    unfold _root_.GD.N0107.d009085
    exact div_pos (div_pos homega.1 hm1) hm0
  · rw [_root_.GD.N0232.N0720.N1467.d012548]
    unfold _root_.GD.N0107.d009085
    exact div_pos (div_pos homega.2 hn1) hn0


theorem d018933
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      0 < (_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0 +
        (_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1 := by
  filter_upwards [_root_.GD.N0232.N0720.N1459.d018932 m n hm hn] with
      omega homega
  exact add_pos homega.1 homega.2




theorem d018934
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hd : _root_.GD.N0232.N0720.N1437.d003000 d) :
    _root_.GD.N0232.N0720.N1459.d018930 m n d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1459.d018931 m n d := by
  filter_upwards [_root_.GD.N0232.N0720.N1459.d018933 m n hm hn] with
      omega homega
  simpa only [_root_.GD.N0232.N0720.N1459.d018930, _root_.GD.N0232.N0720.N1459.d018931] using
    _root_.GD.N0232.N0720.N1460.d003038 d hd homega



theorem d018935
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : ℝ → ℝ → ℝ → ℝ → ℝ)
    (hd : _root_.GD.N0232.N0720.N1437.d003000 d)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1459.d018930 m n d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
      _root_.GD.N0232.N0720.N1459.d018931 m n d := by
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq
    (_root_.GD.N0232.N0720.N1459.d018934
      m n hm hn d hd)

end
end N1459
end N0720
end N0232
end GD
