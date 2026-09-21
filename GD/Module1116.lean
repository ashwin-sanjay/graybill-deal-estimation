import GD.Module1115




















open Set

namespace GD
namespace N0232
namespace N0720
namespace N1219

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1217
open _root_.GD.N0232.N0720.N1069
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0107

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)




def d017942
    (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) : _root_.GD.N0232.N0720.N1080.d014168 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  have hzLeft : 0 < 1 - z := sub_pos.mpr hz.2
  refine
    { location := 0
      scale₁ := Real.sqrt ((m : ℝ) * (1 - z))
      scale₂ := Real.sqrt ((n : ℝ) * z)
      scale₁_pos := Real.sqrt_pos.2 (mul_pos hmR hzLeft)
      scale₂_pos := Real.sqrt_pos.2 (mul_pos hnR hz.1) }

@[simp] theorem d017943
    (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz).location = 0 := rfl

@[simp] theorem d017944
    (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz).scale₁ =
      Real.sqrt ((m : ℝ) * (1 - z)) := rfl

@[simp] theorem d017945
    (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz).scale₂ =
      Real.sqrt ((n : ℝ) * z) := rfl



theorem d017946
    (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0107.d009043 m
        (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz).scale₁ = 1 - z := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hzLeft : 0 ≤ 1 - z := (sub_pos.mpr hz.2).le
  unfold _root_.GD.N0107.d009043
  rw [_root_.GD.N0232.N0720.N1219.d017944,
    Real.sq_sqrt (mul_nonneg hmR.le hzLeft)]
  field_simp [hmR.ne']



theorem d017947
    (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0107.d009044 n
        (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz).scale₂ = z := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  unfold _root_.GD.N0107.d009044
  rw [_root_.GD.N0232.N0720.N1219.d017945,
    Real.sq_sqrt (mul_nonneg hnR.le hz.1.le)]
  field_simp [hnR.ne']


theorem d017948
    (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0107.d009045 m n
        (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz).scale₁
        (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz).scale₂ = 1 := by
  unfold _root_.GD.N0107.d009045
  rw [_root_.GD.N0232.N0720.N1219.d017946 m n hm hn z hz,
    _root_.GD.N0232.N0720.N1219.d017947 m n hm hn z hz]
  ring


theorem d017949
    (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1069.d014352 m n
        (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) = z := by
  unfold _root_.GD.N0232.N0720.N1069.d014352 _root_.GD.N0107.d009046
  rw [_root_.GD.N0232.N0720.N1219.d017947 m n hm hn z hz,
    _root_.GD.N0232.N0720.N1219.d017948 m n hm hn z hz]
  simp






theorem d017950
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q) :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) q p ↔
      ∀ (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1),
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) p ≤
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) q := by
  constructor
  · intro hbelow z hz
    exact hbelow (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz)
  · intro hsection theta
    let z := _root_.GD.N0232.N0720.N1069.d014352 m n theta
    have hz : z ∈ Ioo (0 : ℝ) 1 :=
      ⟨_root_.GD.N0232.N0720.N1069.d014353 m n hm hn theta,
        _root_.GD.N0232.N0720.N1069.d014354 m n hm hn theta⟩
    have hfrac :
        _root_.GD.N0232.N0720.N1069.d014352 m n theta =
          _root_.GD.N0232.N0720.N1069.d014352 m n
            (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) := by
      calc
        _root_.GD.N0232.N0720.N1069.d014352 m n theta = z := rfl
        _ = _root_.GD.N0232.N0720.N1069.d014352 m n
            (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) :=
          (_root_.GD.N0232.N0720.N1219.d017949
            m n hm hn z hz).symm
    exact
      (_root_.GD.N0232.N0720.N1217.d017938
        m n hm hn hfrac p q hp hq).2 (hsection z hz)



theorem d017951
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value p ↔
      ∀ (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1),
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) p ≤
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) s.value := by
  exact _root_.GD.N0232.N0720.N1219.d017950
    m n hm hn p s.value hp s.riskCharacter




theorem d017952
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value ↔
      ∀ (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1),
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) p ≤
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) s.value := by
  change _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value p ↔ _
  exact _root_.GD.N0232.N0720.N1219.d017951
    m n hm hn p hp s



theorem d017953
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p q ↔
      ∀ (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1),
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) p <
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) q := by
  constructor
  · intro hstrict z hz
    exact hstrict (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz)
  · intro hsection theta
    let z := _root_.GD.N0232.N0720.N1069.d014352 m n theta
    have hz : z ∈ Ioo (0 : ℝ) 1 :=
      ⟨_root_.GD.N0232.N0720.N1069.d014353 m n hm hn theta,
        _root_.GD.N0232.N0720.N1069.d014354 m n hm hn theta⟩
    have hfrac :
        _root_.GD.N0232.N0720.N1069.d014352 m n theta =
          _root_.GD.N0232.N0720.N1069.d014352 m n
            (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) := by
      calc
        _root_.GD.N0232.N0720.N1069.d014352 m n theta = z := rfl
        _ = _root_.GD.N0232.N0720.N1069.d014352 m n
            (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) :=
          (_root_.GD.N0232.N0720.N1219.d017949
            m n hm hn z hz).symm
    exact
      (_root_.GD.N0232.N0720.N1217.d017939
        m n hm hn hfrac p q hp hq).2 (hsection z hz)



theorem d017954
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p s.value ↔
      ∀ (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1),
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) p <
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) s.value := by
  exact _root_.GD.N0232.N0720.N1219.d017953
    m n hm hn p s.value hp s.riskCharacter

end

end N1219
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1219.d017949
#print axioms _root_.GD.N0232.N0720.N1219.d017950
#print axioms _root_.GD.N0232.N0720.N1219.d017952
#print axioms _root_.GD.N0232.N0720.N1219.d017953
