import GD.Module1185
import GD.Module1178
















namespace GD
namespace N0232
namespace N0720
namespace N1042

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1043
open _root_.GD.N0232.N0720.N1048
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1468





theorem d019083
    (n : ℕ) (d e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n)) :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 n n) (_root_.GD.N0232.N0720.N1043.d019067 n d) (_root_.GD.N0232.N0720.N1043.d019067 n e) ↔
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 n n) d e := by
  constructor
  · intro h theta
    have h' := h (_root_.GD.N0232.N0720.N1043.d019058 theta)
    rw [_root_.GD.N0232.N0720.N1043.d019072, _root_.GD.N0232.N0720.N1043.d019072,
      _root_.GD.N0232.N0720.N1043.d019062] at h'
    exact h'
  · intro h theta
    rw [_root_.GD.N0232.N0720.N1043.d019072, _root_.GD.N0232.N0720.N1043.d019072]
    exact h (_root_.GD.N0232.N0720.N1043.d019058 theta)





theorem d019084
    (n : ℕ) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n)) :
    _root_.GD.N0232.N0720.N1043.d019067 n (_root_.GD.N0232.N0720.N1159.d014633 n n d) =
      _root_.GD.N0232.N0720.N1159.d014633 n n (_root_.GD.N0232.N0720.N1043.d019067 n d) := by
  apply _root_.GD.N0232.N0720.N1048.d019044
    n n (_root_.GD.N0232.N0720.N1043.d019067 n d) _
  · exact (_root_.GD.N0232.N0720.N1042.d019083 n d
      (_root_.GD.N0232.N0720.N1159.d014633 n n d)).2
      (_root_.GD.N0232.N0720.N1159.d014634 n n d).1
  · have hback : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 n n) d
        (_root_.GD.N0232.N0720.N1043.d019067 n
          (_root_.GD.N0232.N0720.N1159.d014633 n n (_root_.GD.N0232.N0720.N1043.d019067 n d))) := by
      intro theta
      rw [_root_.GD.N0232.N0720.N1043.d019072]
      have h :=
        (_root_.GD.N0232.N0720.N1159.d014634 n n (_root_.GD.N0232.N0720.N1043.d019067 n d)).1
          (_root_.GD.N0232.N0720.N1043.d019058 theta)
      rw [_root_.GD.N0232.N0720.N1043.d019072, _root_.GD.N0232.N0720.N1043.d019062] at h
      exact h
    have hmin := (_root_.GD.N0232.N0720.N1159.d014634 n n d).2.2 _ hback
    rw [_root_.GD.N0232.N0720.N1080.d014190 n n, _root_.GD.N0232.N0720.N1080.d014190 n n] at hmin
    simp only [zero_sub, norm_neg, _root_.GD.N0232.N0720.N1043.d019071] at hmin
    have hsq :
        ‖_root_.GD.N0232.N0720.N1159.d014633 n n d‖ ^ 2 ≤
          ‖_root_.GD.N0232.N0720.N1159.d014633 n n (_root_.GD.N0232.N0720.N1043.d019067 n d)‖ ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff
        (sq_nonneg _)).mp hmin
    rw [_root_.GD.N0232.N0720.N1043.d019071]
    nlinarith [norm_nonneg (_root_.GD.N0232.N0720.N1159.d014633 n n d),
      norm_nonneg (_root_.GD.N0232.N0720.N1159.d014633 n n (_root_.GD.N0232.N0720.N1043.d019067 n d))]





theorem d019085
    (n : ℕ) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n))
    (hfixed : _root_.GD.N0232.N0720.N1043.d019067 n d = d) :
    _root_.GD.N0232.N0720.N1043.d019067 n (_root_.GD.N0232.N0720.N1159.d014633 n n d) =
      _root_.GD.N0232.N0720.N1159.d014633 n n d := by
  rw [_root_.GD.N0232.N0720.N1042.d019084, hfixed]


theorem d019086
    (n : ℕ) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n)) :
    _root_.GD.N0232.N0720.N1159.d014633 n n (_root_.GD.N0232.N0720.N1043.d019067 n d) = _root_.GD.N0232.N0720.N1043.d019067 n d ↔
      _root_.GD.N0232.N0720.N1159.d014633 n n d = d := by
  rw [← _root_.GD.N0232.N0720.N1042.d019084]
  constructor
  · intro h
    have h' := congrArg (_root_.GD.N0232.N0720.N1043.d019067 n) h
    simpa only [_root_.GD.N0232.N0720.N1043.d019068] using h'
  · intro h
    rw [h]



theorem d019087
    (n : ℕ) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n)) :
    (∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n),
        _root_.GD.N0232.N0720.N1468.d018953 n n e (_root_.GD.N0232.N0720.N1043.d019067 n d)) ↔
      (∃ e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n),
        _root_.GD.N0232.N0720.N1468.d018953 n n e d) := by
  constructor
  · rintro ⟨e, heWeak, theta, heStrict⟩
    refine ⟨_root_.GD.N0232.N0720.N1043.d019067 n e, ?_, _root_.GD.N0232.N0720.N1043.d019058 theta, ?_⟩
    · intro eta
      rw [_root_.GD.N0232.N0720.N1043.d019072]
      have h := heWeak (_root_.GD.N0232.N0720.N1043.d019058 eta)
      rw [_root_.GD.N0232.N0720.N1043.d019072, _root_.GD.N0232.N0720.N1043.d019062] at h
      exact h
    · rw [_root_.GD.N0232.N0720.N1043.d019072, _root_.GD.N0232.N0720.N1043.d019062]
      simpa only [_root_.GD.N0232.N0720.N1043.d019072] using heStrict
  · rintro ⟨e, heWeak, theta, heStrict⟩
    refine ⟨_root_.GD.N0232.N0720.N1043.d019067 n e, ?_, _root_.GD.N0232.N0720.N1043.d019058 theta, ?_⟩
    · intro eta
      rw [_root_.GD.N0232.N0720.N1043.d019072, _root_.GD.N0232.N0720.N1043.d019072]
      exact heWeak (_root_.GD.N0232.N0720.N1043.d019058 eta)
    · rw [_root_.GD.N0232.N0720.N1043.d019072, _root_.GD.N0232.N0720.N1043.d019072,
        _root_.GD.N0232.N0720.N1043.d019062]
      exact heStrict

end

end N1042
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1042.d019083
#print axioms _root_.GD.N0232.N0720.N1042.d019084
#print axioms _root_.GD.N0232.N0720.N1042.d019085
#print axioms _root_.GD.N0232.N0720.N1042.d019086
#print axioms _root_.GD.N0232.N0720.N1042.d019087
