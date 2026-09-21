import GD.Module1417
import GD.Module1508
import GD.Module0943

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0207.N0454

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1332
open _root_.GD.N0232.N0720.N1328 _root_.GD.N0232.N0720.N1309
open _root_.GD.N0232.N0720.N1311
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0107
open _root_.GD.N0207.N0451 _root_.GD.N0207.N0453

private theorem d023517 {e : ℝ} (he : 0 < e) :
    1 / (1 + e) ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · positivity
  · exact (div_lt_one (by positivity)).2 (by linarith)

private theorem d023518 {e : ℝ} (he : 0 < e) :
    (1 / (1 + e)) * (1 - 1 / (1 + e)) = e / (1 + e) ^ 2 := by
  field_simp [(show 1 + e ≠ 0 by positivity)]
  ring

private theorem d023519 {e : ℝ} (he : 0 < e) :
    e / (1 + e) ^ 2 ≤ e := by
  apply div_le_self he.le
  nlinarith [sq_nonneg e]

private theorem d023520 {e : ℝ} (he : 0 < e) :
    (1 / e) / (1 + 1 / e) ^ 2 = e / (1 + e) ^ 2 := by
  field_simp [he.ne', (show 1 + e ≠ 0 by positivity),
    (show 1 + 1 / e ≠ 0 by positivity)]
  ring

theorem d023521
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {C : ℝ}
    (hcap : ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      _root_.GD.N0232.N0720.N1332.d020106 m n
        (fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) t.1 ≤
          C * t.1 * (1 - t.1))
    {e : ℝ} (he : 0 < e) :
    _root_.GD.N0232.N0720.N1309.d013070 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) e ≤
      C * (e / (1 + e) ^ 2) := by
  have h := hcap ⟨1 / (1 + e), _root_.GD.N0207.N0454.d023517 he⟩
  change (∫ x, (_root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 -
      1 / (1 + e)) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 m n (1 / (1 + e))) ≤ _ at h
  rw [_root_.GD.N0232.N0720.N1328.d014766 hm hn he] at h
  simpa only [mul_assoc, _root_.GD.N0207.N0454.d023518 he] using h

theorem d023522
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hsmall : _root_.GD.N0232.N0720.N1436.d013207 m ≤ 1 ∨ _root_.GD.N0232.N0720.N1436.d013208 n ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) :
    ¬ ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      _root_.GD.N0232.N0720.N1332.d020106 m n
        (fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) t.1 ≤
          C * t.1 * (1 - t.1) := by
  intro hcap
  have ha := _root_.GD.N0232.N0720.N1436.d013211 hm
  have hb := _root_.GD.N0232.N0720.N1436.d013212 hn
  rcases hsmall with hsmall | hsmall
  · obtain ⟨e, he, hlarge⟩ := _root_.GD.N0207.N0453.d023516 hb ha hsmall C
    have h := _root_.GD.N0207.N0454.d023521 hm hn hcap (one_div_pos.mpr he)
    rw [← _root_.GD.N0232.N0720.N1311.d013609 hb ha he, _root_.GD.N0207.N0454.d023520 he] at h
    have hu := mul_le_mul_of_nonneg_left (_root_.GD.N0207.N0454.d023519 he) hC
    linarith
  · obtain ⟨e, he, hlarge⟩ := _root_.GD.N0207.N0453.d023516 ha hb hsmall C
    have h := _root_.GD.N0207.N0454.d023521 hm hn hcap he
    have hu := mul_le_mul_of_nonneg_left (_root_.GD.N0207.N0454.d023519 he) hC
    linarith

theorem d023523
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hsmall : m ≤ 3 ∨ n ≤ 3)
    {C : ℝ} (hC : 0 ≤ C) :
    ¬ ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      _root_.GD.N0232.N0720.N1332.d020106 m n
        (fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) t.1 ≤
          C * t.1 * (1 - t.1) := by
  apply _root_.GD.N0207.N0454.d023522 hm hn _ hC
  rcases hsmall with hsmall | hsmall
  · left
    unfold _root_.GD.N0232.N0720.N1436.d013207
    have h : ((m - 1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show m - 1 ≤ 2 by omega)
    linarith
  · right
    unfold _root_.GD.N0232.N0720.N1436.d013208
    have h : ((n - 1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show n - 1 ≤ 2 by omega)
    linarith

theorem d023524
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hsmall : m ≤ 3 ∨ n ≤ 3)
    {C : ℝ} (hC : 0 ≤ C) :
    ¬ ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1328.d014756 m n) ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
  intro hcap
  apply _root_.GD.N0207.N0454.d023523 hm hn hsmall hC
  intro t
  have h := _root_.GD.N0207.N0451.d022704 hm hn
    ((_root_.GD.N0232.N0720.N1328.d014757 _ _).comp measurable_fst)
    (fun x ↦ _root_.GD.N0232.N0720.N1328.d014758 (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn) x.1)
    hC hcap t
  simp only [Function.comp_def] at h
  have hp : 0 ≤ t.1 * (1 - t.1) := mul_nonneg t.2.1.le (sub_nonneg.mpr t.2.2.le)
  nlinarith

theorem d023525
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hsmall : m ≤ 3 ∨ n ≤ 3)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    (hroot : g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n]
      fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1)
    {C : ℝ} (hC : 0 ≤ C) :
    ¬ ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
  intro hcap
  apply _root_.GD.N0207.N0454.d023523 hm hn hsmall hC
  intro t
  have h := _root_.GD.N0207.N0451.d022703 hm hn hg hb hrep hC hcap t
  rw [_root_.GD.N0232.N0720.N1332.d020108 hm hn hroot t] at h
  have hp : 0 ≤ t.1 * (1 - t.1) := mul_nonneg t.2.1.le (sub_nonneg.mpr t.2.2.le)
  nlinarith

theorem d023526
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hsmall : m ≤ 3 ∨ n ≤ 3) :
    _root_.GD.N0232.N0720.N1256.d015548 m n (_root_.GD.N0232.N0720.N1328.d014756 m n) = ⊤ := by
  by_contra hfinite
  let C := (_root_.GD.N0232.N0720.N1256.d015548 m n (_root_.GD.N0232.N0720.N1328.d014756 m n)).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  apply _root_.GD.N0207.N0454.d023524 hm hn hsmall hC
  intro theta
  apply (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) C hC theta _).mp
  rw [show ENNReal.ofReal C = _root_.GD.N0232.N0720.N1256.d015548 m n (_root_.GD.N0232.N0720.N1328.d014756 m n) from
    ENNReal.ofReal_toReal hfinite]
  exact le_iSup (fun theta => _root_.GD.N0232.N0720.N1256.d015547 m n theta (_root_.GD.N0232.N0720.N1328.d014756 m n)) theta

end
end GD.N0207.N0454

#print axioms _root_.GD.N0207.N0454.d023523
#print axioms _root_.GD.N0207.N0454.d023524
#print axioms _root_.GD.N0207.N0454.d023525
#print axioms _root_.GD.N0207.N0454.d023526
