import GD.Module1124
import GD.Module0217
import GD.Module1180

set_option warningAsError true


















open MeasureTheory

namespace GD.N0232.N0720.N1505

noncomputable section

open _root_.GD.N0232.N0720.N1029
open _root_.GD.N0232.N0720.N1077
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1437
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1475
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0644
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229






def d018982 (m n : ℕ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1437.d002996
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1)



def d018983
    (m n : ℕ) (gamma : ℝ → ℝ) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 0 -
      (_root_.GD.N0232.N0720.N1467.d012542 m n omega).mean 1) *
    gamma (_root_.GD.N0232.N0720.N1505.d018982 m n omega)

theorem d018984 (m n : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1505.d018982 m n) := by
  unfold _root_.GD.N0232.N0720.N1505.d018982 _root_.GD.N0232.N0720.N1437.d002996
  fun_prop

theorem d018985
    (m n : ℕ) (gamma : ℝ → ℝ) (hgamma : Measurable gamma) :
    Measurable (_root_.GD.N0232.N0720.N1505.d018983 m n gamma) := by
  unfold _root_.GD.N0232.N0720.N1505.d018983
  apply Measurable.mul
  · fun_prop
  · exact hgamma.comp (_root_.GD.N0232.N0720.N1505.d018984 m n)



theorem d018986
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1505.d018982 m n (g • omega) =
      _root_.GD.N0232.N0720.N1505.d018982 m n omega := by
  rw [_root_.GD.N0232.N0720.N1505.d018982, _root_.GD.N0232.N0720.N1475.d018975 m n hm hn]
  simp only [_root_.GD.N0232.N0719.N1010.d011416,
    _root_.GD.N0232.N0719.N0900.d009101]
  exact _root_.GD.N0232.N0720.N1437.d003001 g.d009239
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 0)
    ((_root_.GD.N0232.N0720.N1467.d012542 m n omega).meanVariance 1) g.d009241



theorem d018987
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (gamma : ℝ → ℝ) (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1505.d018983 m n gamma (g • omega) =
      g.d009239 * _root_.GD.N0232.N0720.N1505.d018983 m n gamma omega := by
  unfold _root_.GD.N0232.N0720.N1505.d018983
  rw [_root_.GD.N0232.N0720.N1505.d018986 m n hm hn g omega,
    _root_.GD.N0232.N0720.N1475.d018975 m n hm hn]
  simp only [_root_.GD.N0232.N0719.N1010.d011416,
    _root_.GD.N0232.N0719.N0900.d009101]
  ring






def d018988
    (m n : ℕ) (c : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∃ raw : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
    Measurable raw ∧
    (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      raw =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1214.d014265 m n c) ∧
    ∀ (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n),
      raw (g • omega) = g.d009239 * raw omega




structure d018989 (m n : ℕ) where
  gamma : ℝ → ℝ
  measurable_gamma : Measurable gamma
  memLp : MemLp (_root_.GD.N0232.N0720.N1505.d018983 m n gamma) 2
    (_root_.GD.N0232.N0720.N1080.d014172 m n)


def d018989.d018990
    {m n : ℕ} (c : _root_.GD.N0232.N0720.N1505.d018989 m n) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1505.d018983 m n c.gamma) c.memLp



theorem d018989.d018991
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (c : _root_.GD.N0232.N0720.N1505.d018989 m n) :
    _root_.GD.N0232.N0720.N1505.d018988 m n c.d018990 := by
  refine ⟨_root_.GD.N0232.N0720.N1505.d018983 m n c.gamma,
    _root_.GD.N0232.N0720.N1505.d018985 m n c.gamma c.measurable_gamma,
    ?_, _root_.GD.N0232.N0720.N1505.d018987 m n hm hn c.gamma⟩
  have href : _root_.GD.N0232.N0720.N1505.d018983 m n c.gamma =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun omega ↦ c.d018990 omega := c.memLp.coeFn_toLp.symm
  intro theta
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
    (href.trans (_root_.GD.N0232.N0720.N1214.d014267 m n c.d018990).symm)






theorem d018992
    (m n : ℕ) (p c : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1214.d014265 m n (p + c) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
      fun omega ↦ _root_.GD.N0232.N0720.N1214.d014265 m n p omega + _root_.GD.N0232.N0720.N1214.d014265 m n c omega := by
  have href : _root_.GD.N0232.N0720.N1214.d014265 m n (p + c) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun omega ↦ _root_.GD.N0232.N0720.N1214.d014265 m n p omega + _root_.GD.N0232.N0720.N1214.d014265 m n c omega := by
    filter_upwards [_root_.GD.N0232.N0720.N1214.d014267 m n (p + c),
      _root_.GD.N0232.N0720.N1214.d014267 m n p,
      _root_.GD.N0232.N0720.N1214.d014267 m n c,
      Lp.coeFn_add p c] with omega hsum hp hc hadd
    rw [hsum, hadd, Pi.add_apply, hp, hc]
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq href



theorem d018993
    (m n : ℕ) (p c : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014652 m n p)
    (hc : _root_.GD.N0232.N0720.N1505.d018988 m n c) :
    _root_.GD.N0232.N0720.N1159.d014652 m n (p + c) := by
  obtain ⟨rp, hrpMeasurable, hrpClass, hrpEquivariant⟩ := hp
  obtain ⟨rc, hrcMeasurable, hrcClass, hrcHomogeneous⟩ := hc
  refine ⟨fun omega ↦ rp omega + rc omega,
    hrpMeasurable.add hrcMeasurable, ?_, ?_⟩
  · intro theta
    have hcanonical := _root_.GD.N0232.N0720.N1505.d018992 m n p c theta
    filter_upwards [hrpClass theta, hrcClass theta, hcanonical] with
        omega hpOmega hcOmega hcanonicalOmega
    rw [hpOmega, hcOmega]
    exact hcanonicalOmega.symm
  · intro g omega
    change rp (g • omega) + rc (g • omega) =
      g • (rp omega + rc omega)
    rw [hrpEquivariant g omega, hrcHomogeneous g omega]
    simp only [_root_.GD.N0232.N0719.N0946.d009229.d009244]
    ring



theorem d018994
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014652 m n p)
    (c : _root_.GD.N0232.N0720.N1505.d018989 m n) :
    _root_.GD.N0232.N0720.N1159.d014638 m n (p + c.d018990) := by
  apply _root_.GD.N0232.N0720.N1159.d014653
  exact _root_.GD.N0232.N0720.N1505.d018993
    m n p c.d018990 hp
      (c.d018991 m n hm hn)





theorem d018995
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014652 m n
      (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) := by
  let q := _root_.GD.N0232.N0720.N1029.d015364 m n hm hn
  have hqmem := _root_.GD.N0232.N0720.N1029.d015366 m n hm hn
  have hqFinite := _root_.GD.N0232.N0720.N1029.d015371 m n hm hn
  apply (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn q hqFinite).1
  intro g
  rw [← _root_.GD.N0232.N0720.N1077.d018051
    m n hm hn g q hqmem hqFinite]
  exact _root_.GD.N0232.N0720.N1029.d015367 m n hm hn g





theorem d018996
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1505.d018989 m n) :
    _root_.GD.N0232.N0720.N1159.d014638 m n
      (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn + c.d018990) := by
  exact _root_.GD.N0232.N0720.N1505.d018994
    m n (lt_of_lt_of_le (by omega) hm) (lt_of_lt_of_le (by omega) hn)
      (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn)
      (_root_.GD.N0232.N0720.N1505.d018995
        m n hm hn) c

end

end GD.N0232.N0720.N1505

#print axioms _root_.GD.N0232.N0720.N1505.d018986
#print axioms _root_.GD.N0232.N0720.N1505.d018987
#print axioms _root_.GD.N0232.N0720.N1505.d018993
#print axioms _root_.GD.N0232.N0720.N1505.d018996
