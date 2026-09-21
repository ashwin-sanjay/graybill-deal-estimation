import GD.Module0987
import GD.Module1163






































open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1452

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1288
open _root_.GD.N0232.N0720.N1356
open _root_.GD.N0232.N0720.N1047
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)




def d018847 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (θ : _root_.GD.N0232.N0720.N1080.d014168) : ℝ≥0∞ :=
  ⨅ d : _root_.GD.N0232.N0720.N1159.d014630 m n s.value, _root_.GD.N0232.N0720.N1080.d014182 m n θ d.1

theorem d018848
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (θ : _root_.GD.N0232.N0720.N1080.d014168)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    _root_.GD.N0232.N0720.N1452.d018847 m n s θ ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ d :=
  iInf_le (fun d : _root_.GD.N0232.N0720.N1159.d014630 m n s.value => _root_.GD.N0232.N0720.N1080.d014182 m n θ d.1) ⟨d, hd⟩

theorem d018849
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (θ : _root_.GD.N0232.N0720.N1080.d014168) (x : ℝ≥0∞)
    (h : ∀ d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value, x ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ d) :
    x ≤ _root_.GD.N0232.N0720.N1452.d018847 m n s θ :=
  le_iInf fun d => h d.1 d.2






theorem d018850
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1452.d018847 m n s θ ≤
      _root_.GD.N0232.N0720.N1452.d018847 m n s (_root_.GD.N0232.N0720.N1215.d014272 g θ) := by
  apply _root_.GD.N0232.N0720.N1452.d018849
  intro d hd
  have hmem :
      _root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ d
          (_root_.GD.N0232.N0720.N1159.d014644 m n s d hd) ∈
        _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    (_root_.GD.N0232.N0720.N1159.d014645 m n s g⁻¹ ⟨d, hd⟩).2
  have key := _root_.GD.N0232.N0720.N1159.d014643 m n g θ
    (_root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹ d
      (_root_.GD.N0232.N0720.N1159.d014644 m n s d hd))
    (_root_.GD.N0232.N0720.N1482.d015158 (m := m) (n := n) g⁻¹ d
      (_root_.GD.N0232.N0720.N1159.d014644 m n s d hd))
  rw [_root_.GD.N0232.N0720.N1356.d015641 m n s g d hd] at key
  rw [key]
  exact mul_le_mul_left' (_root_.GD.N0232.N0720.N1452.d018848 m n s θ _ hmem) _

theorem d018851 (g : _root_.GD.N0232.N0720.N1482.d015118) :
    g.d009239 ^ 2 * g⁻¹.d009239 ^ 2 = 1 := by
  rw [← mul_pow, ← _root_.GD.N0232.N0719.N0946.d009229.d009243, mul_inv_cancel, _root_.GD.N0232.N0719.N0946.d009229.d009242, one_pow]

theorem d018852 (g : _root_.GD.N0232.N0720.N1482.d015118) :
    g⁻¹.d009239 * g.d009239 = 1 := by
  rw [← _root_.GD.N0232.N0719.N0946.d009229.d009243, inv_mul_cancel, _root_.GD.N0232.N0719.N0946.d009229.d009242]



theorem d018853
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1452.d018847 m n s (_root_.GD.N0232.N0720.N1215.d014272 g θ) =
      ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1452.d018847 m n s θ := by
  apply le_antisymm
  · have h := _root_.GD.N0232.N0720.N1452.d018850 m n s g⁻¹ (_root_.GD.N0232.N0720.N1215.d014272 g θ)
    rw [_root_.GD.N0232.N0720.N1215.d014280] at h
    have hprod :
        ENNReal.ofReal (g.d009239 ^ 2) * ENNReal.ofReal (g⁻¹.d009239 ^ 2) = 1 := by
      rw [← ENNReal.ofReal_mul (sq_nonneg _), _root_.GD.N0232.N0720.N1452.d018851,
        ENNReal.ofReal_one]
    calc _root_.GD.N0232.N0720.N1452.d018847 m n s (_root_.GD.N0232.N0720.N1215.d014272 g θ)
        = (ENNReal.ofReal (g.d009239 ^ 2) * ENNReal.ofReal (g⁻¹.d009239 ^ 2)) *
            _root_.GD.N0232.N0720.N1452.d018847 m n s (_root_.GD.N0232.N0720.N1215.d014272 g θ) := by rw [hprod, one_mul]
      _ = ENNReal.ofReal (g.d009239 ^ 2) *
            (ENNReal.ofReal (g⁻¹.d009239 ^ 2) * _root_.GD.N0232.N0720.N1452.d018847 m n s (_root_.GD.N0232.N0720.N1215.d014272 g θ)) := by
          rw [mul_assoc]
      _ ≤ ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1452.d018847 m n s θ := mul_le_mul_left' h _
  · exact _root_.GD.N0232.N0720.N1452.d018850 m n s g θ





theorem d018854
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
        (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 =
      ENNReal.ofReal (g.d009239 ^ 2 * ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) := by
  have hP : _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s _
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  change _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
      (_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP) = _
  rw [_root_.GD.N0232.N0720.N1159.d014643, _root_.GD.N0232.N0720.N1080.d014190 m n, zero_sub, norm_neg,
    ENNReal.ofReal_mul (sq_nonneg _)]



theorem d018855
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1452.d018847 m n s (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) =
      ENNReal.ofReal (g.d009239 ^ 2 * ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) := by
  apply le_antisymm
  · rw [← _root_.GD.N0232.N0720.N1452.d018854 m n s g]
    exact _root_.GD.N0232.N0720.N1452.d018848 m n s _ _
      (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).2
  · rw [← _root_.GD.N0232.N0720.N1452.d018854 m n s g]
    exact _root_.GD.N0232.N0720.N1452.d018849 m n s _ _ (fun d hd => _root_.GD.N0232.N0720.N1356.d015642 m n s g d hd)



theorem d018856
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1452.d018847 m n s _root_.GD.N0232.N0720.N1080.d014169 =
      ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) := by
  have h := _root_.GD.N0232.N0720.N1452.d018855 m n s 1
  simp only [_root_.GD.N0232.N0720.N1215.d014276, _root_.GD.N0232.N0719.N0946.d009229.d009242, one_pow, one_mul] at h
  exact h


theorem d018857
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1452.d018847 m n s (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) ≠ ⊤ := by
  rw [_root_.GD.N0232.N0720.N1452.d018855]
  exact ENNReal.ofReal_ne_top



theorem d018858
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) d =
        _root_.GD.N0232.N0720.N1452.d018847 m n s (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) ↔
      d = (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 := by
  constructor
  · intro hrisk
    apply _root_.GD.N0232.N0720.N1356.d015643 m n s g d hd
    rw [hrisk]
    exact _root_.GD.N0232.N0720.N1452.d018848 m n s _ _
      (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).2
  · rintro rfl
    rw [_root_.GD.N0232.N0720.N1452.d018854, _root_.GD.N0232.N0720.N1452.d018855]





theorem d018859
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal -
      (_root_.GD.N0232.N0720.N1452.d018847 m n s (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)).toReal =
      g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1159.d014647 m n s g⁻¹ := by
  have h1 := _root_.GD.N0232.N0720.N1288.d015629 m n s g⁻¹
  rw [inv_inv] at h1
  have hba := _root_.GD.N0232.N0720.N1452.d018852 g
  have h2 :
      (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal =
      g.d009239 ^ 2 *
        ‖(_root_.GD.N0232.N0720.N1159.d014645 m n s g⁻¹ (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1‖ ^ 2 := by
    calc (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
            (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal
        = (g⁻¹.d009239 * g.d009239) ^ 2 *
            (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
              (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal := by
          rw [hba, one_pow, one_mul]
      _ = g.d009239 ^ 2 * (g⁻¹.d009239 ^ 2 *
            (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
              (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal) := by ring
      _ = g.d009239 ^ 2 *
            ‖(_root_.GD.N0232.N0720.N1159.d014645 m n s g⁻¹ (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1‖ ^ 2 := by
          rw [h1]
  rw [_root_.GD.N0232.N0720.N1452.d018855, ENNReal.toReal_ofReal (by positivity), h2]
  unfold _root_.GD.N0232.N0720.N1159.d014647
  ring



theorem d018860
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g⁻¹ = 0 ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
        _root_.GD.N0232.N0720.N1452.d018847 m n s (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) := by
  have hP : _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s _
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  rw [← ENNReal.toReal_eq_toReal_iff' (hP _) (_root_.GD.N0232.N0720.N1452.d018857 m n s g)]
  have hreg := _root_.GD.N0232.N0720.N1452.d018859 m n s g
  constructor
  · intro h0
    rw [h0, mul_zero] at hreg
    exact sub_eq_zero.mp hreg
  · intro heq
    rw [heq, sub_self] at hreg
    exact (mul_eq_zero.mp hreg.symm).resolve_left (pow_ne_zero 2 g.d009240.ne')



theorem d018861
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (∀ g : _root_.GD.N0232.N0720.N1482.d015118, _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0) ↔
      ∀ g : _root_.GD.N0232.N0720.N1482.d015118,
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
            (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
          _root_.GD.N0232.N0720.N1452.d018847 m n s (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) := by
  constructor
  · intro hall g
    exact (_root_.GD.N0232.N0720.N1452.d018860 m n s g).1 (hall g⁻¹)
  · intro hall g
    have h := (_root_.GD.N0232.N0720.N1452.d018860 m n s g⁻¹).2 (hall g⁻¹)
    rwa [inv_inv] at h





def d018862 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g h : _root_.GD.N0232.N0720.N1482.d015118) : ℝ :=
  (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
      (_root_.GD.N0232.N0720.N1159.d014642 m n h
        (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1
        (_root_.GD.N0232.N0720.N1159.d014644 m n s _
          (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).2))).toReal -
    (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
      (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1).toReal

theorem d018863 (g h : _root_.GD.N0232.N0720.N1482.d015118) : g * (g⁻¹ * h * g) = h * g := by
  rw [mul_assoc g⁻¹ h g, mul_inv_cancel_left]

theorem d018864 (g k : _root_.GD.N0232.N0720.N1482.d015118) : g⁻¹ * (g * k * g⁻¹) * g = k := by
  simp [mul_assoc]



theorem d018865
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g h : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1452.d018862 m n s g h =
      g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1159.d014647 m n s (g⁻¹ * h * g) := by
  have hP : _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s _
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have e1 :
      _root_.GD.N0232.N0720.N1159.d014642 m n h
          (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1
          (_root_.GD.N0232.N0720.N1159.d014644 m n s _
            (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).2) =
        _root_.GD.N0232.N0720.N1159.d014642 m n g
          (_root_.GD.N0232.N0720.N1159.d014642 m n (g⁻¹ * h * g)
            (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP)
          (_root_.GD.N0232.N0720.N1482.d015158 (m := m) (n := n) _ _ hP) := by
    rw [_root_.GD.N0232.N0720.N1482.d015161 (m := m) (n := n) g (g⁻¹ * h * g)
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP, _root_.GD.N0232.N0720.N1452.d018863]
    exact _root_.GD.N0232.N0720.N1482.d015161 (m := m) (n := n) h g
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP
  have hL :
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014642 m n h
            (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1
            (_root_.GD.N0232.N0720.N1159.d014644 m n s _
              (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).2)) =
        ENNReal.ofReal (g.d009239 ^ 2) *
          ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014642 m n (g⁻¹ * h * g)
            (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP‖ ^ 2) := by
    rw [e1, _root_.GD.N0232.N0720.N1159.d014643, _root_.GD.N0232.N0720.N1080.d014190 m n, zero_sub, norm_neg]
  have hR :
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 =
        ENNReal.ofReal (g.d009239 ^ 2) *
          ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) := by
    change _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
      (_root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP) = _
    rw [_root_.GD.N0232.N0720.N1159.d014643, _root_.GD.N0232.N0720.N1080.d014190 m n, zero_sub, norm_neg]
  have hk_norm :
      ‖(_root_.GD.N0232.N0720.N1159.d014645 m n s (g⁻¹ * h * g) (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1‖ =
        ‖_root_.GD.N0232.N0720.N1159.d014642 m n (g⁻¹ * h * g)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hP‖ := rfl
  unfold _root_.GD.N0232.N0720.N1452.d018862 _root_.GD.N0232.N0720.N1159.d014647
  rw [hL, hR, hk_norm, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (sq_nonneg _)]
  ring

theorem d018866
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g h : _root_.GD.N0232.N0720.N1482.d015118) :
    0 ≤ _root_.GD.N0232.N0720.N1452.d018862 m n s g h := by
  rw [_root_.GD.N0232.N0720.N1452.d018865]
  exact mul_nonneg (sq_nonneg _) (_root_.GD.N0232.N0720.N1159.d014650 m n s _)

theorem d018867
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g h : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1452.d018862 m n s g h = 0 ↔
      _root_.GD.N0232.N0720.N1159.d014647 m n s (g⁻¹ * h * g) = 0 := by
  rw [_root_.GD.N0232.N0720.N1452.d018865, mul_eq_zero,
    or_iff_right (pow_ne_zero 2 g.d009240.ne')]


theorem d018868
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    (∀ h : _root_.GD.N0232.N0720.N1482.d015118, _root_.GD.N0232.N0720.N1452.d018862 m n s g h = 0) ↔
      ∀ k : _root_.GD.N0232.N0720.N1482.d015118, _root_.GD.N0232.N0720.N1159.d014647 m n s k = 0 := by
  constructor
  · intro hall k
    have h := (_root_.GD.N0232.N0720.N1452.d018867 m n s g (g * k * g⁻¹)).1 (hall _)
    rwa [_root_.GD.N0232.N0720.N1452.d018864] at h
  · intro hall h
    exact (_root_.GD.N0232.N0720.N1452.d018867 m n s g h).2 (hall _)



def d018869 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) : ℝ :=
  _root_.GD.N0232.N0720.N1452.d018862 m n s g (g * _root_.GD.N0232.N0720.N1482.d015130 * g⁻¹) +
    _root_.GD.N0232.N0720.N1452.d018862 m n s g (g * _root_.GD.N0232.N0720.N1482.d015131 * g⁻¹)


theorem d018870
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1452.d018869 m n s g =
      g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s := by
  unfold _root_.GD.N0232.N0720.N1452.d018869 _root_.GD.N0232.N0720.N1482.d015169
  rw [_root_.GD.N0232.N0720.N1452.d018865,
    _root_.GD.N0232.N0720.N1452.d018865,
    _root_.GD.N0232.N0720.N1452.d018864, _root_.GD.N0232.N0720.N1452.d018864]
  ring



theorem d018871
    (hm : 2 ≤ m) (hn : 2 ≤ n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1452.d018869 m n s g = 0 := by
  rw [_root_.GD.N0232.N0720.N1482.d015173
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hs, hmd⟩
    exact ⟨s, hs, by
      rw [_root_.GD.N0232.N0720.N1452.d018870, hmd, mul_zero]⟩
  · rintro ⟨s, hs, hmd⟩
    refine ⟨s, hs, ?_⟩
    rw [_root_.GD.N0232.N0720.N1452.d018870, mul_eq_zero] at hmd
    exact hmd.resolve_left (pow_ne_zero 2 g.d009240.ne')




def d018872 (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014168 :=
  ⟨0, 1, θ.scale₂ / θ.scale₁, one_pos, div_pos θ.scale₂_pos θ.scale₁_pos⟩


def d018873 (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1482.d015118 :=
  ⟨θ.location, Real.log θ.scale₁⟩

theorem d018874 (θ : _root_.GD.N0232.N0720.N1080.d014168) : (_root_.GD.N0232.N0720.N1452.d018873 θ).d009239 = θ.scale₁ := by
  simp [_root_.GD.N0232.N0720.N1452.d018873, _root_.GD.N0232.N0719.N0946.d009229.d009239, Real.exp_log θ.scale₁_pos]

theorem d018875 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    θ = _root_.GD.N0232.N0720.N1215.d014272 (_root_.GD.N0232.N0720.N1452.d018873 θ) (_root_.GD.N0232.N0720.N1452.d018872 θ) := by
  have h1 : θ.scale₁ ≠ 0 := θ.scale₁_pos.ne'
  apply _root_.GD.N0232.N0720.N1215.d014277
  · simp [_root_.GD.N0232.N0720.N1215.d014273, _root_.GD.N0232.N0720.N1452.d018872, _root_.GD.N0232.N0720.N1452.d018873]
  · simp [_root_.GD.N0232.N0720.N1215.d014274, _root_.GD.N0232.N0720.N1452.d018872, _root_.GD.N0232.N0720.N1452.d018874]
  · rw [_root_.GD.N0232.N0720.N1215.d014275, _root_.GD.N0232.N0720.N1452.d018874]
    simp only [_root_.GD.N0232.N0720.N1452.d018872]
    field_simp



theorem d018876
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1452.d018847 m n s θ =
      ENNReal.ofReal (θ.scale₁ ^ 2) * _root_.GD.N0232.N0720.N1452.d018847 m n s (_root_.GD.N0232.N0720.N1452.d018872 θ) := by
  conv_lhs => rw [_root_.GD.N0232.N0720.N1452.d018875 θ]
  rw [_root_.GD.N0232.N0720.N1452.d018853, _root_.GD.N0232.N0720.N1452.d018874]




theorem d018877
    (hm : 2 ≤ m) (hn : 2 ≤ n) (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1452.d018847 m n (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn) (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) =
      ENNReal.ofReal (g.d009239 ^ 2 * ‖_root_.GD.N0232.N0720.N1047.d018650 m n hm hn‖ ^ 2) :=
  _root_.GD.N0232.N0720.N1452.d018855 m n (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn) g



theorem d018878
    (hm : 2 ≤ m) (hn : 2 ≤ n) (g : _root_.GD.N0232.N0720.N1482.d015118)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) d (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ENNReal.ofReal (g.d009239 ^ 2 * ‖_root_.GD.N0232.N0720.N1047.d018650 m n hm hn‖ ^ 2) ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) d := by
  rw [← _root_.GD.N0232.N0720.N1452.d018877 m n hm hn g]
  exact _root_.GD.N0232.N0720.N1452.d018848 m n (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn) _ d hd

end

end N1452
end N0720
end N0232
end GD
