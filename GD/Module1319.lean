import GD.Module1308
import GD.Module1317
import GD.Module1318
import GD.Module1314










set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1680
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1672 _root_.GD.N0106.N0428.N0765.N1527
open _root_.GD.N0106.N0428.N0765.N1537 _root_.GD.N0106.N0428.N0765.N1675 _root_.GD.N0106.N0428.N0765.N1584 _root_.GD.N0106.N0428.N0765.N1521
open _root_.GD.N0106.N0428.N0765.N1585
open _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1607

def d021557 (e α β : ℝ) : ℂ :=
  (((1 + e) / 11 : ℝ) : ℂ) * ∫ p, _root_.GD.N0106.N0428.N0765.N1537.d021532 e α β p

theorem d021558 {e α β : ℝ} (he : 0 ≤ e)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1680.d021557 e α β‖ ≤ ((1 + e) / 11) * _root_.GD.N0106.N0428.N0765.N1537.d021534 α β := by
  unfold _root_.GD.N0106.N0428.N0765.N1680.d021557
  rw [norm_mul, Complex.norm_of_nonneg (by positivity : 0 ≤ (1 + e) / 11)]
  exact mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1537.d021552 he hw) (by positivity)


theorem d021559 {e α β : ℝ}
    (he : e ∈ Icc (0 : ℝ) (1 / 50))
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1680.d021557 e α β‖ ≤ (51 / 550) * _root_.GD.N0106.N0428.N0765.N1537.d021534 α β := by
  have hB : 0 ≤ _root_.GD.N0106.N0428.N0765.N1537.d021534 α β :=
    (norm_nonneg _).trans (_root_.GD.N0106.N0428.N0765.N1537.d021552 (e := 0) le_rfl hw)
  exact (_root_.GD.N0106.N0428.N0765.N1680.d021558 he.1 hw).trans
    (mul_le_mul_of_nonneg_right (by linarith [he.2]) hB)

theorem d021560 (α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Tendsto (fun e : ℝ => _root_.GD.N0106.N0428.N0765.N1680.d021557 e α β) (𝓝[>] 0) (𝓝 (_root_.GD.N0106.N0428.N0765.N1680.d021557 0 α β)) := by
  have hc : ContinuousAt (fun e : ℝ => (((1 + e) / 11 : ℝ) : ℂ)) 0 := by fun_prop
  exact (hc.tendsto.mono_left nhdsWithin_le_nhds).mul
    (_root_.GD.N0106.N0428.N0765.N1537.d021556 α β hw)

theorem d021561 (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1537.d021527 0 0 p = (_root_.GD.N0106.N0428.N0765.N1521.d020868 p : ℂ) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1537.d021527, _root_.GD.N0106.N0428.N0765.N1537.d021524, Complex.ofReal_zero, zero_mul, add_zero,
    _root_.GD.N0106.N0428.N0765.N1585.d005530, _root_.GD.N0106.N0428.N0765.N1521.d020868, Complex.ofReal_mul]

theorem d021562 {η : ℝ} (hη : 0 < η) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1529.d020800 η (_root_.GD.N0106.N0428.N0765.N1521.d020862 p) = Real.exp p.2 / (Real.exp p.2 + η) := by
  have hw := (_root_.GD.N0106.N0428.N0765.N1527.d021473 p.1 p.2).2.2
  have hv := (_root_.GD.N0106.N0428.N0765.N1527.d021473 p.1 p.2).2.1
  have hd : _root_.GD.N0106.N0428.N0765.N1521.d020862 p 1 + η * _root_.GD.N0106.N0428.N0765.N1521.d020862 p 2 ≠ 0 :=
    (add_pos hv (mul_pos hη hw)).ne'
  have he : Real.exp p.2 + η ≠ 0 := (add_pos (Real.exp_pos p.2) hη).ne'
  have hr := _root_.GD.N0106.N0428.N0765.N1584.d021367 p
  have hvw : _root_.GD.N0106.N0428.N0765.N1521.d020862 p 1 = Real.exp p.2 * _root_.GD.N0106.N0428.N0765.N1521.d020862 p 2 :=
    (div_eq_iff hw.ne').mp hr
  unfold _root_.GD.N0106.N0428.N0765.N1529.d020800
  field_simp [hd, he]
  nlinarith

theorem d021563 {e : ℝ} (he : 0 < e) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1537.d021530 e 0 p.2 = ((e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020800 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 p) : ℝ) : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1680.d021562 (inv_pos.mpr he)]
  have hd : 1 + e * Real.exp p.2 ≠ 0 := (by positivity : 0 < 1 + e * Real.exp p.2).ne'
  have hd' : Real.exp p.2 + e⁻¹ ≠ 0 := (add_pos (Real.exp_pos p.2) (inv_pos.mpr he)).ne'
  have halg : Real.exp p.2 / (1 + e * Real.exp p.2) =
      e⁻¹ * (Real.exp p.2 / (Real.exp p.2 + e⁻¹)) := by
    field_simp [he.ne', hd, hd'] <;> ring
  unfold _root_.GD.N0106.N0428.N0765.N1537.d021530 _root_.GD.N0106.N0428.N0765.N1537.d021524
  simp only [Complex.ofReal_zero, zero_mul, add_zero, ← Complex.ofReal_exp]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div, halg]

theorem d021564 {e : ℝ} (he : 0 < e) :
    _root_.GD.N0106.N0428.N0765.N1537.d021531 e = e⁻¹ * _root_.GD.N0106.N0428.N0765.N1607.d012678 e⁻¹ := by
  unfold _root_.GD.N0106.N0428.N0765.N1537.d021531 _root_.GD.N0106.N0428.N0765.N1607.d012678
  have hd : 1 + e ≠ 0 := (by positivity : 0 < 1 + e).ne'
  have hd' : 1 + e⁻¹ ≠ 0 := (by positivity : 0 < 1 + e⁻¹).ne'
  field_simp [he.ne', hd, hd'] <;> ring

theorem d021565 {e : ℝ} (he : 0 < e) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1675.d021510 e 0 0 p = ((e⁻¹ * _root_.GD.N0106.N0428.N0765.N1529.d020799 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 p) : ℝ) : ℂ) := by
  have hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 0 0 < Real.pi := by simpa [_root_.GD.N0106.N0428.N0765.N1538.d021192] using Real.pi_pos
  unfold _root_.GD.N0106.N0428.N0765.N1675.d021510
  rw [← _root_.GD.N0106.N0428.N0765.N1672.d021429 he p.1 p.2 0 0 hw,
    _root_.GD.N0106.N0428.N0765.N1527.d021472 he p.1 p.2]

theorem d021566 {e : ℝ} (he : 0 < e) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 p =
      (((e⁻¹)^2 * (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1529.d020802 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 p)) : ℝ) : ℂ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1537.d021532
  rw [_root_.GD.N0106.N0428.N0765.N1680.d021561, _root_.GD.N0106.N0428.N0765.N1680.d021563 he, _root_.GD.N0106.N0428.N0765.N1680.d021565 he, _root_.GD.N0106.N0428.N0765.N1680.d021564 he]
  unfold _root_.GD.N0106.N0428.N0765.N1529.d020802
  push_cast
  ring



theorem d021567 (location : ℝ) {e : ℝ} (he : 0 < e) :
    _root_.GD.N0106.N0428.N0765.N1680.d021557 e 0 0 =
      ((e⁻¹ * (_root_.GD.N0106.N0428.N0765.N1610.d020776 location e⁻¹
          (_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11)) -
        _root_.GD.N0106.N0428.N0765.N1610.d020776 location e⁻¹ _root_.GD.N0106.N0428.N0765.N1611.d012593) : ℝ) : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1521.d020875 location e⁻¹ (inv_pos.mpr he)]
  unfold _root_.GD.N0106.N0428.N0765.N1680.d021557
  have hf := funext (_root_.GD.N0106.N0428.N0765.N1680.d021566 he)
  have hi : (∫ p : ℝ × ℝ, (((e⁻¹)^2 *
      (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1529.d020802 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 p)) : ℝ) : ℂ)) =
      ((∫ p : ℝ × ℝ, (e⁻¹)^2 *
        (_root_.GD.N0106.N0428.N0765.N1521.d020868 p * _root_.GD.N0106.N0428.N0765.N1529.d020802 e⁻¹ (_root_.GD.N0106.N0428.N0765.N1521.d020862 p)) : ℝ) : ℂ) := integral_ofReal
  rw [hf, hi, integral_const_mul, ← Complex.ofReal_mul]
  congr 1
  field_simp [he.ne']
  ring

end
end GD.N0106.N0428.N0765.N1680

#print axioms _root_.GD.N0106.N0428.N0765.N1680.d021559
#print axioms _root_.GD.N0106.N0428.N0765.N1680.d021560
#print axioms _root_.GD.N0106.N0428.N0765.N1680.d021567
