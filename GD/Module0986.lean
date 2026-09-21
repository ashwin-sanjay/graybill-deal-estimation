import GD.Module0969







































open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1288

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482

variable (m n : ℕ)





theorem d015622
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) (eta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n eta (_root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk) =
      _root_.GD.N0232.N0720.N1080.d014182 m n eta s.value := by
  have heta : _root_.GD.N0232.N0720.N1215.d014272 g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta) = eta := by simp
  calc
    _root_.GD.N0232.N0720.N1080.d014182 m n eta (_root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk) =
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta))
          (_root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk) := by
      rw [heta]
    _ = ENNReal.ofReal (g.d009239 ^ 2) *
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta) s.value :=
      _root_.GD.N0232.N0720.N1159.d014643 m n g _ s.value s.finiteRisk
    _ = _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta)) s.value :=
      (s.riskCharacter g _).symm
    _ = _root_.GD.N0232.N0720.N1080.d014182 m n eta s.value := by rw [heta]



theorem d015623
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk ∈
      _root_.GD.N0232.N0720.N1159.d014630 m n s.value := by
  intro eta
  exact le_of_eq (_root_.GD.N0232.N0720.N1288.d015622 m n s g eta)


theorem d015624
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    ‖_root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk‖ ^ 2 =
      ‖s.value‖ ^ 2 := by
  have href := _root_.GD.N0232.N0720.N1288.d015622 m n s g _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).mp href





theorem d015625
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    ‖_root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk -
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  have htax := _root_.GD.N0232.N0720.N1159.d014648 m n s.value
    (_root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk)
    (_root_.GD.N0232.N0720.N1288.d015623 m n s g)
  rw [_root_.GD.N0232.N0720.N1288.d015624 m n s g] at htax
  simpa only [_root_.GD.N0232.N0720.N1201.d015333] using htax


theorem d015626
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    ‖s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  have hmem : s.value ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value := fun _ => le_rfl
  simpa only [_root_.GD.N0232.N0720.N1201.d015333] using
    _root_.GD.N0232.N0720.N1159.d014648 m n s.value s.value hmem



theorem d015627
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g h : _root_.GD.N0232.N0720.N1482.d015118) :
    ‖_root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk -
        _root_.GD.N0232.N0720.N1159.d014642 m n h s.value s.finiteRisk‖ ^ 2 ≤
      4 * _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  set P := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  set x := _root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk
  set z := _root_.GD.N0232.N0720.N1159.d014642 m n h s.value s.finiteRisk
  have hx : ‖x - P‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1201.d015333 m n s :=
    _root_.GD.N0232.N0720.N1288.d015625 m n s g
  have hz : ‖z - P‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1201.d015333 m n s :=
    _root_.GD.N0232.N0720.N1288.d015625 m n s h
  have htri : ‖x - z‖ ≤ ‖x - P‖ + ‖P - z‖ :=
    norm_sub_le_norm_sub_add_norm_sub x P z
  rw [norm_sub_rev P z] at htri
  have hsq : ‖x - z‖ * ‖x - z‖ ≤
      (‖x - P‖ + ‖z - P‖) * (‖x - P‖ + ‖z - P‖) :=
    mul_le_mul htri htri (norm_nonneg _) (by positivity)
  nlinarith [hsq, mul_self_nonneg (‖x - P‖ - ‖z - P‖), hx, hz]




theorem d015628
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    ‖_root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk - s.value‖ ^ 2 ≤
      4 * _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  set P := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  set x := _root_.GD.N0232.N0720.N1159.d014642 m n g s.value s.finiteRisk
  have hx : ‖x - P‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1201.d015333 m n s :=
    _root_.GD.N0232.N0720.N1288.d015625 m n s g
  have hs : ‖s.value - P‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1201.d015333 m n s :=
    _root_.GD.N0232.N0720.N1288.d015626 m n s
  have htri : ‖x - s.value‖ ≤ ‖x - P‖ + ‖P - s.value‖ :=
    norm_sub_le_norm_sub_add_norm_sub x P s.value
  rw [norm_sub_rev P s.value] at htri
  have hsq : ‖x - s.value‖ * ‖x - s.value‖ ≤
      (‖x - P‖ + ‖s.value - P‖) * (‖x - P‖ + ‖s.value - P‖) :=
    mul_le_mul htri htri (norm_nonneg _) (by positivity)
  nlinarith [hsq, mul_self_nonneg (‖x - P‖ - ‖s.value - P‖), hx, hs]





theorem d015629
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    ‖(_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1‖ ^ 2 =
      g.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal := by
  set P := _root_.GD.N0232.N0720.N1159.d014633 m n s.value with hPdef
  have hP : _root_.GD.N0232.N0720.N1159.d014637 m n P :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s P
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hval :
      (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 =
        _root_.GD.N0232.N0720.N1159.d014642 m n g P hP := rfl
  have heta :
      _root_.GD.N0232.N0720.N1215.d014272 g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) =
        _root_.GD.N0232.N0720.N1080.d014169 := by simp
  have hrisk :
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1159.d014642 m n g P hP) =
        ENNReal.ofReal (g.d009239 ^ 2) *
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P := by
    calc
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1159.d014642 m n g P hP) =
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169))
            (_root_.GD.N0232.N0720.N1159.d014642 m n g P hP) := by rw [heta]
      _ = ENNReal.ofReal (g.d009239 ^ 2) *
            _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P :=
        _root_.GD.N0232.N0720.N1159.d014643 m n g _ P hP
  have hnorm :
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1159.d014642 m n g P hP) =
        ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014642 m n g P hP‖ ^ 2) := by
    rw [_root_.GD.N0232.N0720.N1080.d014190 m n]
    simp only [zero_sub, norm_neg]
  have hreal := congrArg ENNReal.toReal (hnorm.symm.trans hrisk)
  rw [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _)] at hreal
  rw [hval]
  exact hreal




theorem d015630
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g =
      g.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal -
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1159.d014647
  rw [_root_.GD.N0232.N0720.N1288.d015629]




theorem d015631
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
      g.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal := by
  have hnonneg := _root_.GD.N0232.N0720.N1159.d014650 m n s g
  rw [_root_.GD.N0232.N0720.N1288.d015630] at hnonneg
  linarith



theorem d015632
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 ↔
      g.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal =
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1288.d015630, sub_eq_zero]





theorem d015633
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1482.d015130.d009239 ^ 2 *
            (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
              (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal =
            ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ∧
          _root_.GD.N0232.N0720.N1482.d015131.d009239 ^ 2 *
            (_root_.GD.N0232.N0720.N1080.d014182 m n
              (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015131⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
              (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal =
            ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1482.d015172
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, htwo, hthree⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1288.d015632 m n s _).1 htwo,
      (_root_.GD.N0232.N0720.N1288.d015632 m n s _).1 hthree⟩
  · rintro ⟨s, hstrict, htwo, hthree⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1288.d015632 m n s _).2 htwo,
      (_root_.GD.N0232.N0720.N1288.d015632 m n s _).2 hthree⟩






noncomputable def d015634 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014639 m n where
  value := _root_.GD.N0232.N0720.N1080.d014181 m n hm hn
  finiteRisk := _root_.GD.N0232.N0720.N1159.d014640 m n
    (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)
    (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn)
  riskCharacter := _root_.GD.N0232.N0720.N1215.d014296 m n hm hn



theorem d015635
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1080.d014191 m n hm hn =
      _root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn).value := rfl




theorem d015636
    (hm : 2 ≤ m) (hn : 2 ≤ n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 ≤
      g.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)).toReal :=
  _root_.GD.N0232.N0720.N1288.d015631 m n
    (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn) g







theorem d015637
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (htwo : _root_.GD.N0232.N0720.N1482.d015130.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)).toReal ≤
        ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2)
    (hthree : _root_.GD.N0232.N0720.N1482.d015131.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n
          (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015131⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)).toReal ≤
        ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  rw [_root_.GD.N0232.N0720.N1288.d015633
    m n hm hn]
  refine ⟨_root_.GD.N0232.N0720.N1288.d015634 m n hm hn,
    _root_.GD.N0232.N0720.N1080.d014186 m n hm hn, ?_, ?_⟩
  · exact le_antisymm htwo
      (_root_.GD.N0232.N0720.N1288.d015636
        m n hm hn _root_.GD.N0232.N0720.N1482.d015130)
  · exact le_antisymm hthree
      (_root_.GD.N0232.N0720.N1288.d015636
        m n hm hn _root_.GD.N0232.N0720.N1482.d015131)




theorem d015638
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (htwo : _root_.GD.N0232.N0720.N1482.d015130.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)).toReal ≤
        ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2)
    (hthree : _root_.GD.N0232.N0720.N1482.d015131.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n
          (_root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015131⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)).toReal ≤
        ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2) :
    ∀ g : _root_.GD.N0232.N0720.N1482.d015118,
      _root_.GD.N0232.N0720.N1159.d014645 m n (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn) g
          (_root_.GD.N0232.N0720.N1159.d014646 m n (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn)) =
        _root_.GD.N0232.N0720.N1159.d014646 m n (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn) := by
  have htwo' :
      _root_.GD.N0232.N0720.N1159.d014647 m n (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn) _root_.GD.N0232.N0720.N1482.d015130 = 0 :=
    (_root_.GD.N0232.N0720.N1288.d015632 m n
      (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn) _root_.GD.N0232.N0720.N1482.d015130).2
      (le_antisymm htwo
        (_root_.GD.N0232.N0720.N1288.d015636
          m n hm hn _root_.GD.N0232.N0720.N1482.d015130))
  have hthree' :
      _root_.GD.N0232.N0720.N1159.d014647 m n (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn)
        _root_.GD.N0232.N0720.N1482.d015131 = 0 :=
    (_root_.GD.N0232.N0720.N1288.d015632 m n
      (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn) _root_.GD.N0232.N0720.N1482.d015131).2
      (le_antisymm hthree
        (_root_.GD.N0232.N0720.N1288.d015636
          m n hm hn _root_.GD.N0232.N0720.N1482.d015131))
  intro g
  exact (_root_.GD.N0232.N0720.N1159.d014651 m n (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn) g).1
    ((_root_.GD.N0232.N0720.N1482.d015168
      (m := m) (n := n) (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn)).1 ⟨htwo', hthree'⟩ g)

end

end N1288
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1288.d015628
#print axioms _root_.GD.N0232.N0720.N1288.d015627
#print axioms _root_.GD.N0232.N0720.N1288.d015630
#print axioms _root_.GD.N0232.N0720.N1288.d015631
#print axioms _root_.GD.N0232.N0720.N1288.d015633
#print axioms _root_.GD.N0232.N0720.N1288.d015636
#print axioms _root_.GD.N0232.N0720.N1288.d015637
#print axioms _root_.GD.N0232.N0720.N1288.d015638
