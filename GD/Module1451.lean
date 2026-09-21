import GD.Module1377
import GD.Module0453

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open Set
open scoped BigOperators

namespace GD.N0061
noncomputable section

open _root_.GD.N0059 _root_.GD.N0057 _root_.GD.N0025

def d022974 (i : Fin 7) : ℝ := (_root_.GD.N0059.d006976 i : ℝ) / _root_.GD.N0059.d006973
def d022975 (i : Fin 7) : ℝ := (_root_.GD.N0059.d006977 i : ℝ) / 100
def d022976 (c : _root_.GD.N0059.d006978) : ℝ := (c.uLo : ℝ) / _root_.GD.N0059.d006974
def d022977 (c : _root_.GD.N0059.d006978) : ℝ := (c.uHi : ℝ) / _root_.GD.N0059.d006974
def d022978 (c : _root_.GD.N0059.d006978) : ℝ := (c.zLo : ℝ) / _root_.GD.N0059.d006975
def d022979 (c : _root_.GD.N0059.d006978) : ℝ := (c.zHi : ℝ) / _root_.GD.N0059.d006975
def d022980 (c : _root_.GD.N0059.d006978) : ℝ := (c.d006980 : ℝ) / (2 * _root_.GD.N0059.d006974)
def d022981 (c : _root_.GD.N0059.d006978) : ℝ := (c.d006981 : ℝ) / (2 * _root_.GD.N0059.d006975)
def d022982 (c : _root_.GD.N0059.d006978) (i : Fin 7) : ℝ := (c.root i : ℝ) / _root_.GD.N0059.d006972
def d022983 (c : _root_.GD.N0059.d006978) (j : Fin 4) : ℝ := (c.d006982 j : ℝ) / _root_.GD.N0059.d006974
def d022984 (c : _root_.GD.N0059.d006978) (j : Fin 4) : ℝ := ((c.d006983 j : ℝ) / _root_.GD.N0059.d006975) ^ 3

theorem d022985 (i : Fin 7) : 0 < _root_.GD.N0059.d006976 i ∧
    _root_.GD.N0059.d006976 i < _root_.GD.N0059.d006973 := by
  fin_cases i <;> norm_num [_root_.GD.N0059.d006976, _root_.GD.N0059.d006973]

theorem d022986 (i : Fin 7) : _root_.GD.N0061.d022974 i ∈ Ioo (0 : ℝ) 1 := by
  have h := _root_.GD.N0061.d022985 i
  constructor
  · exact div_pos (by exact_mod_cast h.1) (by norm_num [_root_.GD.N0059.d006973])
  · exact (div_lt_one (by norm_num [_root_.GD.N0059.d006973] : (0 : ℝ) < _root_.GD.N0059.d006973)).mpr
      (by exact_mod_cast h.2)

theorem d022987 (c : _root_.GD.N0059.d006978) (hc : c.d006994) : c.d006980 ≤ 2 * _root_.GD.N0059.d006974 := by
  have h1 := hc.2.2.1
  have h2 := hc.2.2.2.1
  unfold _root_.GD.N0059.d006978.d006980
  omega

theorem d022988 (c : _root_.GD.N0059.d006978) (hc : c.d006994) : 0 < c.d006981 := by
  have h := hc.2.2.2.2.1
  unfold _root_.GD.N0059.d006978.d006981
  omega

theorem d022989 (c : _root_.GD.N0059.d006978) (hc : c.d006994) (i : Fin 7) :
    _root_.GD.N0057.d022147 (_root_.GD.N0061.d022974 i) (_root_.GD.N0061.d022980 c) (_root_.GD.N0061.d022981 c) =
      (c.d006985 i : ℝ) / c.d006984 i := by
  have hn := _root_.GD.N0061.d022985 i
  have hU := _root_.GD.N0061.d022987 c hc
  have hn0 : (0 : ℝ) < (_root_.GD.N0059.d006976 i : ℝ) := by exact_mod_cast hn.1
  have hNn : (0 : ℝ) < (_root_.GD.N0059.d006973 : ℝ) - (_root_.GD.N0059.d006976 i : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hn.2)
  change (0 : ℝ) < 1024 - (_root_.GD.N0059.d006976 i : ℝ) at hNn
  unfold _root_.GD.N0057.d022147 _root_.GD.N0062.d022142 _root_.GD.N0061.d022974 _root_.GD.N0061.d022980 _root_.GD.N0061.d022981
    _root_.GD.N0059.d006978.d006985 _root_.GD.N0059.d006978.d006984
  push_cast [Nat.cast_sub hU, Nat.cast_sub hn.2.le]
  norm_num [_root_.GD.N0059.d006973, _root_.GD.N0059.d006974, _root_.GD.N0059.d006975]
  field_simp [hn0.ne', hNn.ne']
  ring

theorem d022990 (c : _root_.GD.N0059.d006978) (hc : c.d006994) (i : Fin 7)
    (hQN : 0 < c.d006985 i) (j : Fin 4) :
    _root_.GD.N0057.d022151 (_root_.GD.N0061.d022974 i) (_root_.GD.N0061.d022980 c) (_root_.GD.N0061.d022981 c) (_root_.GD.N0061.d022983 c j) (_root_.GD.N0061.d022984 c j) =
      (c.d006986 i j : ℝ) /
        (6 * (c.d006981 : ℝ) * (c.d006985 i : ℝ)) := by
  have hn := _root_.GD.N0061.d022985 i
  have hn0 : (0 : ℝ) < (_root_.GD.N0059.d006976 i : ℝ) := by exact_mod_cast hn.1
  have hNn : (0 : ℝ) < (_root_.GD.N0059.d006973 : ℝ) - (_root_.GD.N0059.d006976 i : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hn.2)
  change (0 : ℝ) < 1024 - (_root_.GD.N0059.d006976 i : ℝ) at hNn
  have hZ : (0 : ℝ) < (c.d006981 : ℝ) := by exact_mod_cast _root_.GD.N0061.d022988 c hc
  have hQ : (0 : ℝ) < (c.d006985 i : ℝ) := by exact_mod_cast hQN
  unfold _root_.GD.N0057.d022151
  rw [_root_.GD.N0061.d022989 c hc i]
  unfold _root_.GD.N0061.d022974 _root_.GD.N0061.d022980 _root_.GD.N0061.d022981 _root_.GD.N0061.d022983 _root_.GD.N0061.d022984 _root_.GD.N0059.d006978.d006986
    _root_.GD.N0059.d006978.d006984
  push_cast [Nat.cast_sub hn.2.le]
  norm_num [_root_.GD.N0059.d006973, _root_.GD.N0059.d006974, _root_.GD.N0059.d006975]
  field_simp [hn0.ne', hNn.ne', hZ.ne', hQ.ne']
  ring

theorem d022991 (c : _root_.GD.N0059.d006978) (hc : c.d006994) (i : Fin 7)
    (hQN : 0 < c.d006985 i) (hR : 0 < c.root i) :
    0 < c.d006987 i := by
  have hn := _root_.GD.N0061.d022985 i
  have hZ := _root_.GD.N0061.d022988 c hc
  have hnpos := hn.1
  have hd : 0 < _root_.GD.N0059.d006973 - _root_.GD.N0059.d006976 i := Nat.sub_pos_of_lt hn.2
  unfold _root_.GD.N0059.d006978.d006987
  positivity

theorem d022992 (c : _root_.GD.N0059.d006978) (hc : c.d006994) (i : Fin 7)
    (hQN : 0 < c.d006985 i) (hQD : 0 < c.d006984 i)
    (hR : 0 < c.root i) (j : Fin 4) :
    _root_.GD.N0057.d022148 (_root_.GD.N0061.d022974 i) (_root_.GD.N0061.d022975 i)
        (_root_.GD.N0057.d022147 (_root_.GD.N0061.d022974 i) (_root_.GD.N0061.d022980 c) (_root_.GD.N0061.d022981 c)) (_root_.GD.N0061.d022982 c i) *
      _root_.GD.N0057.d022151 (_root_.GD.N0061.d022974 i) (_root_.GD.N0061.d022980 c) (_root_.GD.N0061.d022981 c) (_root_.GD.N0061.d022983 c j) (_root_.GD.N0061.d022984 c j) =
      (c.d006988 i : ℝ) * (c.d006986 i j : ℝ) /
        ((_root_.GD.N0059.d006971 : ℝ) * (c.d006987 i : ℝ)) := by
  have hn := _root_.GD.N0061.d022985 i
  have hn0 : (0 : ℝ) < (_root_.GD.N0059.d006976 i : ℝ) := by exact_mod_cast hn.1
  have hNn : (0 : ℝ) < (_root_.GD.N0059.d006973 : ℝ) - (_root_.GD.N0059.d006976 i : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hn.2)
  change (0 : ℝ) < 1024 - (_root_.GD.N0059.d006976 i : ℝ) at hNn
  have hZ : (0 : ℝ) < (c.d006981 : ℝ) := by exact_mod_cast _root_.GD.N0061.d022988 c hc
  have hQ : (0 : ℝ) < (c.d006985 i : ℝ) := by exact_mod_cast hQN
  have hD : (0 : ℝ) < (c.d006984 i : ℝ) := by exact_mod_cast hQD
  have hRR : (0 : ℝ) < (c.root i : ℝ) := by exact_mod_cast hR
  rw [_root_.GD.N0061.d022990 c hc i hQN j, _root_.GD.N0061.d022989 c hc i]
  unfold _root_.GD.N0057.d022148 _root_.GD.N0061.d022974 _root_.GD.N0061.d022975 _root_.GD.N0061.d022982 _root_.GD.N0059.d006978.d006988
    _root_.GD.N0059.d006978.d006987
  push_cast [Nat.cast_sub hn.2.le]
  norm_num [_root_.GD.N0059.d006973, _root_.GD.N0059.d006972, _root_.GD.N0059.d006971]
  field_simp [hn0.ne', hNn.ne', hZ.ne', hQ.ne', hD.ne', hRR.ne']
  ring


theorem d022993 (c : _root_.GD.N0059.d006978) (hc : c.d006994) (i : Fin 7)
    (hactive : c.root i ≠ 0) :
    0 < _root_.GD.N0057.d022147 (_root_.GD.N0061.d022974 i) (_root_.GD.N0061.d022980 c) (_root_.GD.N0061.d022981 c) ∧ 0 < _root_.GD.N0061.d022982 c i ∧
      _root_.GD.N0057.d022147 (_root_.GD.N0061.d022974 i) (_root_.GD.N0061.d022980 c) (_root_.GD.N0061.d022981 c) ≤ (_root_.GD.N0061.d022982 c i) ^ 2 ∧
      ∀ j, 0 ≤ _root_.GD.N0057.d022151 (_root_.GD.N0061.d022974 i) (_root_.GD.N0061.d022980 c) (_root_.GD.N0061.d022981 c)
          (_root_.GD.N0061.d022983 c j) (_root_.GD.N0061.d022984 c j) ∧
        (c.density j i : ℝ) / _root_.GD.N0059.d006971 ≤
          _root_.GD.N0057.d022148 (_root_.GD.N0061.d022974 i) (_root_.GD.N0061.d022975 i)
              (_root_.GD.N0057.d022147 (_root_.GD.N0061.d022974 i) (_root_.GD.N0061.d022980 c) (_root_.GD.N0061.d022981 c)) (_root_.GD.N0061.d022982 c i) *
            _root_.GD.N0057.d022151 (_root_.GD.N0061.d022974 i) (_root_.GD.N0061.d022980 c) (_root_.GD.N0061.d022981 c) (_root_.GD.N0061.d022983 c j) (_root_.GD.N0061.d022984 c j) := by
  have hvalid := hc.2.2.2.2.2.2.1 i
  rw [_root_.GD.N0059.d006978.d006989, if_neg hactive] at hvalid
  rcases hvalid with ⟨hR, hQN, hQD, hroot, hcorner⟩
  have hQ : (0 : ℝ) < (c.d006985 i : ℝ) := by exact_mod_cast hQN
  have hD : (0 : ℝ) < (c.d006984 i : ℝ) := by exact_mod_cast hQD
  have hZ : (0 : ℝ) < (c.d006981 : ℝ) := by exact_mod_cast _root_.GD.N0061.d022988 c hc
  have hRD : (0 : ℝ) < (_root_.GD.N0059.d006972 : ℝ) := by norm_num [_root_.GD.N0059.d006972]
  have hDD : (0 : ℝ) < (_root_.GD.N0059.d006971 : ℝ) := by norm_num [_root_.GD.N0059.d006971]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [_root_.GD.N0061.d022989 c hc i]
    exact div_pos hQ hD
  · exact div_pos (by exact_mod_cast hR) hRD
  · rw [_root_.GD.N0061.d022989 c hc i, _root_.GD.N0061.d022982, div_pow]
    exact (div_le_div_iff₀ hD (pow_pos hRD 2)).mpr (by exact_mod_cast hroot)
  · intro j
    have hden : (0 : ℝ) < (c.d006987 i : ℝ) :=
      by exact_mod_cast _root_.GD.N0061.d022991 c hc i hQN hR
    constructor
    · rw [_root_.GD.N0061.d022990 c hc i hQN j]
      exact div_nonneg (by exact_mod_cast (hcorner j).1) (by positivity)
    · rw [_root_.GD.N0061.d022992 c hc i hQN hQD hR j]
      have hnum : (c.density j i : ℝ) * (c.d006987 i : ℝ) ≤
          (c.d006988 i : ℝ) * (c.d006986 i j : ℝ) := by
        exact_mod_cast (hcorner j).2
      rw [show (c.d006988 i : ℝ) * (c.d006986 i j : ℝ) /
          ((_root_.GD.N0059.d006971 : ℝ) * (c.d006987 i : ℝ)) =
          ((c.d006988 i : ℝ) * (c.d006986 i j : ℝ) /
            (c.d006987 i : ℝ)) / _root_.GD.N0059.d006971 by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring]
      apply div_le_div_of_nonneg_right _ hDD.le
      exact (le_div_iff₀ hden).mpr hnum

theorem d022994 (c : _root_.GD.N0059.d006978) (k : _root_.GD.N0025.d005225) :
    _root_.GD.N0061.d022983 c (_root_.GD.N0057.d022152 k) = _root_.GD.N0025.d005226 (_root_.GD.N0061.d022976 c) (_root_.GD.N0061.d022977 c) k.1 := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.GD.N0061.d022983, _root_.GD.N0059.d006978.d006982, _root_.GD.N0057.d022152, _root_.GD.N0025.d005226, _root_.GD.N0061.d022976, _root_.GD.N0061.d022977]

theorem d022995 (c : _root_.GD.N0059.d006978) (k : _root_.GD.N0025.d005225) :
    _root_.GD.N0061.d022984 c (_root_.GD.N0057.d022152 k) = _root_.GD.N0025.d005226 ((_root_.GD.N0061.d022978 c) ^ 3) ((_root_.GD.N0061.d022979 c) ^ 3) k.2 := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.GD.N0061.d022984, _root_.GD.N0059.d006978.d006983, _root_.GD.N0057.d022152, _root_.GD.N0025.d005226, _root_.GD.N0061.d022978, _root_.GD.N0061.d022979]


theorem d022996 (c : _root_.GD.N0059.d006978) (hc : c.d006994) (i : Fin 7)
    (x : ℝ × ℝ) (hx : x ∈ _root_.GD.N0025.d005230 (_root_.GD.N0061.d022976 c) (_root_.GD.N0061.d022977 c) (_root_.GD.N0061.d022978 c) (_root_.GD.N0061.d022979 c)) :
    (∑ k, _root_.GD.N0025.d005231 (_root_.GD.N0061.d022976 c) (_root_.GD.N0061.d022977 c) (_root_.GD.N0061.d022978 c) (_root_.GD.N0061.d022979 c) k x *
      ((c.density (_root_.GD.N0057.d022152 k) i : ℝ) / _root_.GD.N0059.d006971)) ≤
      _root_.GD.N0057.d022150 (_root_.GD.N0061.d022974 i) (_root_.GD.N0061.d022975 i) x.1 x.2 := by
  have ht := _root_.GD.N0061.d022986 i
  have hp : 0 ≤ _root_.GD.N0061.d022975 i := by unfold _root_.GD.N0061.d022975; positivity
  have ha : 0 ≤ _root_.GD.N0061.d022976 c := by unfold _root_.GD.N0061.d022976; positivity
  have hb : _root_.GD.N0061.d022977 c ≤ 1 := by
    apply (div_le_one (by norm_num [_root_.GD.N0059.d006974] : (0 : ℝ) < _root_.GD.N0059.d006974)).mpr
    exact_mod_cast hc.2.2.2.1
  by_cases hactive : c.root i = 0
  · have hz := hc.2.2.2.2.2.2.1 i
    rw [_root_.GD.N0059.d006978.d006989, if_pos hactive] at hz
    apply _root_.GD.N0057.d022164 ht hp ha hb _ _ x hx
    intro k
    simp only [hz, Nat.cast_zero, zero_div]
  · have h := _root_.GD.N0061.d022993 c hc i hactive
    have hab : _root_.GD.N0061.d022976 c < _root_.GD.N0061.d022977 c :=
      div_lt_div_of_pos_right (by exact_mod_cast hc.2.2.1) (by norm_num [_root_.GD.N0059.d006974])
    have hcz : 0 ≤ _root_.GD.N0061.d022978 c := by unfold _root_.GD.N0061.d022978; positivity
    have hcd : _root_.GD.N0061.d022978 c < _root_.GD.N0061.d022979 c :=
      div_lt_div_of_pos_right (by exact_mod_cast hc.2.2.2.2.2.1)
        (by norm_num [_root_.GD.N0059.d006975])
    have hzm : 0 < _root_.GD.N0061.d022981 c :=
      div_pos (by exact_mod_cast _root_.GD.N0061.d022988 c hc) (by norm_num [_root_.GD.N0059.d006975])
    apply _root_.GD.N0057.d022163 ht hp ha hab hb hcz hcd hzm h.1 h.2.1 h.2.2.1
      (fun k => (c.density (_root_.GD.N0057.d022152 k) i : ℝ) / _root_.GD.N0059.d006971) _ _ x hx
    · intro k
      simpa only [_root_.GD.N0061.d022994, _root_.GD.N0061.d022995] using (h.2.2.2 (_root_.GD.N0057.d022152 k)).1
    · intro k
      simpa only [_root_.GD.N0061.d022994, _root_.GD.N0061.d022995] using (h.2.2.2 (_root_.GD.N0057.d022152 k)).2

end
end GD.N0061

#print axioms _root_.GD.N0061.d022989
#print axioms _root_.GD.N0061.d022990
#print axioms _root_.GD.N0061.d022992
#print axioms _root_.GD.N0061.d022993
#print axioms _root_.GD.N0061.d022996
