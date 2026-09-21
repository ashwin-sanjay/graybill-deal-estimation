import GD.Module1139
import GD.Module1121





















namespace GD
namespace N0232
namespace N0720
namespace N1058

noncomputable section

open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1135
open _root_.GD.N0232.N0720.N1136
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1080




def d018348
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal -
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)).toReal




theorem d018349
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    ∃ theta : _root_.GD.N0232.N0720.N1080.d014168,
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal <
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)).toReal := by
  obtain ⟨theta, htheta⟩ :=
    _root_.GD.N0232.N0720.N1136.d018011
      m n s candidate 0 (by norm_num) (by norm_num)
  refine ⟨theta, ?_⟩
  simp only [zero_mul] at htheta
  linarith



theorem d018350
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    ∃ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1058.d018348 m n s candidate theta < 0 := by
  obtain ⟨theta, htheta⟩ :=
    _root_.GD.N0232.N0720.N1058.d018349 m n s candidate
  refine ⟨theta, ?_⟩
  unfold _root_.GD.N0232.N0720.N1058.d018348
  linarith



theorem d018351
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    ¬ ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)).toReal ≤
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal := by
  intro hstationary
  obtain ⟨theta, htheta⟩ :=
    _root_.GD.N0232.N0720.N1058.d018349 m n s candidate
  exact (not_lt_of_ge (hstationary theta)) htheta



theorem d018352
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    ¬ ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)).toReal ≤
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal := by
  rintro ⟨candidate, hstationary⟩
  exact _root_.GD.N0232.N0720.N1058.d018351
    m n s candidate hstationary




theorem d018353
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    0 < _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value ∧
      ∃ theta : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1058.d018348 m n s candidate theta < 0 := by
  exact ⟨_root_.GD.N0232.N0720.N1135.d018323 s candidate,
    _root_.GD.N0232.N0720.N1058.d018350 m n s candidate⟩

end

end N1058
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1058.d018349
#print axioms _root_.GD.N0232.N0720.N1058.d018350
#print axioms _root_.GD.N0232.N0720.N1058.d018352
#print axioms _root_.GD.N0232.N0720.N1058.d018353
