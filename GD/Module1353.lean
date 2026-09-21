import GD.Module1352








set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology

namespace GD.N0106.N0428.N0770.N1698
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0106.N0428.N0770.N1751 _root_.GD.N0106.N0428.N0770.N1753 _root_.GD.N0106.N0428.N0770.N1750 _root_.GD.N0106.N0428.N0770.N1745 _root_.GD.N0106.N0428.N0770.N1697


def d021850 (mu r : ℝ) (p : _root_.GD.N0106.N0428.N0770.N1745.d021821 3) (i : Fin 3) : ℝ :=
  _root_.GD.N0232.N0719.N0900.d009106
    (_root_.GD.N0232.N0719.N0933.d009305 3 (_root_.GD.N0106.N0428.N0770.N1751.d021754 3 mu (_root_.GD.N0106.N0428.N0770.N1697.d021838 r) p)) i


def d021851 (mu r : ℝ) (p : _root_.GD.N0106.N0428.N0770.N1745.d021821 3) : ℝ :=
  _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 2 *
    ((_root_.GD.N0232.N0719.N0933.d009305 3 (_root_.GD.N0106.N0428.N0770.N1751.d021754 3 mu (_root_.GD.N0106.N0428.N0770.N1697.d021838 r) p)).mean 2 - mu)

theorem d021852 {r : ℝ} (hr : 0 < r) :
    ∀ i, 0 < _root_.GD.N0106.N0428.N0770.N1697.d021838 r i := by
  intro i
  fin_cases i <;> simp [_root_.GD.N0106.N0428.N0770.N1697.d021838, hr]



theorem d021853 (mu : ℝ) {r : ℝ} (hr : 0 < r)
    (p : _root_.GD.N0106.N0428.N0770.N1745.d021821 3) (hz : ∀ i, p.2 i ≠ 0) (i : Fin 3) :
    _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p i = _root_.GD.N0106.N0428.N0770.N1750.d008366 (_root_.GD.N0106.N0428.N0770.N1697.d021838 r) i p.2 := by
  exact _root_.GD.N0106.N0428.N0770.N1753.d021764 (_root_.GD.N0106.N0428.N0770.N1697.d021838 r)
    (fun j => mu + _root_.GD.N0106.N0428.N0770.N1697.d021838 r j * p.1 j / Real.sqrt 2) p.2
    (_root_.GD.N0106.N0428.N0770.N1698.d021852 hr) hz i


theorem d021854 (mu : ℝ) {r : ℝ} (hr : 0 < r)
    (p : _root_.GD.N0106.N0428.N0770.N1745.d021821 3) (hz : ∀ i, p.2 i ≠ 0) :
    _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 2 = (2 / p.2 2 ^ 2) * (r⁻¹) ^ 2 := by
  rw [_root_.GD.N0106.N0428.N0770.N1698.d021853 mu hr p hz]
  simp only [_root_.GD.N0106.N0428.N0770.N1750.d008366, _root_.GD.N0106.N0428.N0770.N1702.d008357, _root_.GD.N0106.N0428.N0770.N1697.d021838,
    Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.tail_cons]
  field_simp [hr.ne', hz 2]
  <;> ring


theorem d021855 (mu : ℝ) {r : ℝ} (hr : 0 < r)
    (p : _root_.GD.N0106.N0428.N0770.N1745.d021821 3) (hz : ∀ i, p.2 i ≠ 0) :
    _root_.GD.N0106.N0428.N0770.N1698.d021851 mu r p =
      (2 / p.2 2 ^ 2 * p.1 2 / Real.sqrt 2) * r⁻¹ := by
  unfold _root_.GD.N0106.N0428.N0770.N1698.d021851
  rw [_root_.GD.N0106.N0428.N0770.N1698.d021854 mu hr p hz]
  simp only [_root_.GD.N0232.N0719.N0933.d009305, _root_.GD.N0106.N0428.N0770.N1751.d021754, _root_.GD.N0106.N0428.N0770.N1697.d021838,
    Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.tail_cons]
  field_simp [hr.ne', hz 2,
    (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne']
  <;> ring


theorem d021856 (mu : ℝ) {r : ℝ} (hr : 0 < r)
    (p : _root_.GD.N0106.N0428.N0770.N1745.d021821 3) (hz : ∀ i, p.2 i ≠ 0) :
    _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 0 + _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 1 =
      2 / p.2 0 ^ 2 + 2 / p.2 1 ^ 2 := by
  rw [_root_.GD.N0106.N0428.N0770.N1698.d021853 mu hr p hz, _root_.GD.N0106.N0428.N0770.N1698.d021853 mu hr p hz]
  simp [_root_.GD.N0106.N0428.N0770.N1750.d008366, _root_.GD.N0106.N0428.N0770.N1702.d008357, _root_.GD.N0106.N0428.N0770.N1697.d021838]

theorem d021857 (mu : ℝ) {r : ℝ} (hr : 0 < r)
    (p : _root_.GD.N0106.N0428.N0770.N1745.d021821 3) (hz : ∀ i, p.2 i ≠ 0) :
    0 < _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 0 + _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 1 := by
  rw [_root_.GD.N0106.N0428.N0770.N1698.d021856 mu hr p hz]
  exact add_pos (div_pos (by norm_num) (sq_pos_of_ne_zero (hz 0)))
    (div_pos (by norm_num) (sq_pos_of_ne_zero (hz 1)))


theorem d021858 (mu : ℝ) (p : _root_.GD.N0106.N0428.N0770.N1745.d021821 3)
    (hz : ∀ i, p.2 i ≠ 0) :
    IsBigOWith ‖(2 : ℝ) / p.2 2 ^ 2‖ atTop
      (fun r : ℝ => _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 2) (fun r : ℝ => (r⁻¹) ^ 2) := by
  apply isBigOWith_iff.mpr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [_root_.GD.N0106.N0428.N0770.N1698.d021854 mu hr p hz, norm_mul]

theorem d021859 (mu : ℝ) (p : _root_.GD.N0106.N0428.N0770.N1745.d021821 3)
    (hz : ∀ i, p.2 i ≠ 0) :
    IsBigOWith ‖(2 : ℝ) / p.2 2 ^ 2 * p.1 2 / Real.sqrt 2‖ atTop
      (fun r : ℝ => _root_.GD.N0106.N0428.N0770.N1698.d021851 mu r p) (fun r : ℝ => r⁻¹) := by
  apply isBigOWith_iff.mpr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [_root_.GD.N0106.N0428.N0770.N1698.d021855 mu hr p hz, norm_mul]

theorem d021860 (mu : ℝ) (p : _root_.GD.N0106.N0428.N0770.N1745.d021821 3)
    (hz : ∀ i, p.2 i ≠ 0) :
    (fun r : ℝ => _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 2) =O[atTop] (fun r : ℝ => (r⁻¹) ^ 2) :=
  (_root_.GD.N0106.N0428.N0770.N1698.d021858 mu p hz).isBigO

theorem d021861 (mu : ℝ) (p : _root_.GD.N0106.N0428.N0770.N1745.d021821 3)
    (hz : ∀ i, p.2 i ≠ 0) :
    (fun r : ℝ => _root_.GD.N0106.N0428.N0770.N1698.d021851 mu r p) =O[atTop] (fun r : ℝ => r⁻¹) :=
  (_root_.GD.N0106.N0428.N0770.N1698.d021859 mu p hz).isBigO



theorem d021862 (mu : ℝ) :
    ∀ᵐ p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 3,
      (∀ r : ℝ, 0 < r →
        _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 2 = (2 / p.2 2 ^ 2) * (r⁻¹) ^ 2 ∧
        _root_.GD.N0106.N0428.N0770.N1698.d021851 mu r p =
          (2 / p.2 2 ^ 2 * p.1 2 / Real.sqrt 2) * r⁻¹ ∧
        _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 0 + _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 1 =
          2 / p.2 0 ^ 2 + 2 / p.2 1 ^ 2 ∧
        0 < _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 0 + _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 1) ∧
      ((fun r : ℝ => _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r p 2) =O[atTop]
        (fun r : ℝ => (r⁻¹) ^ 2)) ∧
      ((fun r : ℝ => _root_.GD.N0106.N0428.N0770.N1698.d021851 mu r p) =O[atTop]
        (fun r : ℝ => r⁻¹)) := by
  have hz : ∀ᵐ p ∂_root_.GD.N0106.N0428.N0770.N1745.d021822 3, ∀ i, p.2 i ≠ 0 := by
    exact (Measure.quasiMeasurePreserving_snd
      (μ := _root_.GD.N0106.N0428.N0770.N1751.d021742 3) (ν := _root_.GD.N0106.N0428.N0770.N1751.d021742 3)).ae
        (_root_.GD.N0106.N0428.N0770.N1753.d021767 3)
  filter_upwards [hz] with p hp
  refine ⟨?_, _root_.GD.N0106.N0428.N0770.N1698.d021860 mu p hp, _root_.GD.N0106.N0428.N0770.N1698.d021861 mu p hp⟩
  intro r hr
  exact ⟨_root_.GD.N0106.N0428.N0770.N1698.d021854 mu hr p hp, _root_.GD.N0106.N0428.N0770.N1698.d021855 mu hr p hp,
    _root_.GD.N0106.N0428.N0770.N1698.d021856 mu hr p hp, _root_.GD.N0106.N0428.N0770.N1698.d021857 mu hr p hp⟩


theorem d021863 (mu : ℝ) {r : ℝ} (hr : 0 < r)
    (omega : _root_.GD.N0232.N0719.N0900.d009094 3 (fun _ => 2)) (i : Fin 3) :
    _root_.GD.N0106.N0428.N0770.N1698.d021850 mu r (_root_.GD.N0106.N0428.N0770.N1751.d021744 3 mu (_root_.GD.N0106.N0428.N0770.N1697.d021838 r) omega) i =
      _root_.GD.N0232.N0719.N0900.d009106 (_root_.GD.N0232.N0719.N0900.d009104 3 (fun _ => 2) omega) i := by
  unfold _root_.GD.N0106.N0428.N0770.N1698.d021850
  rw [_root_.GD.N0106.N0428.N0770.N1751.d021756 3 mu (_root_.GD.N0106.N0428.N0770.N1697.d021838 r) (_root_.GD.N0106.N0428.N0770.N1698.d021852 hr),
    _root_.GD.N0232.N0719.N0933.d009307]


theorem d021864 (mu : ℝ) {r : ℝ} (hr : 0 < r)
    (omega : _root_.GD.N0232.N0719.N0900.d009094 3 (fun _ => 2)) :
    _root_.GD.N0106.N0428.N0770.N1698.d021851 mu r (_root_.GD.N0106.N0428.N0770.N1751.d021744 3 mu (_root_.GD.N0106.N0428.N0770.N1697.d021838 r) omega) =
      _root_.GD.N0232.N0719.N0900.d009106 (_root_.GD.N0232.N0719.N0900.d009104 3 (fun _ => 2) omega) 2 *
        ((_root_.GD.N0232.N0719.N0900.d009104 3 (fun _ => 2) omega).mean 2 - mu) := by
  unfold _root_.GD.N0106.N0428.N0770.N1698.d021851
  rw [_root_.GD.N0106.N0428.N0770.N1698.d021863 mu hr,
    _root_.GD.N0106.N0428.N0770.N1751.d021756 3 mu (_root_.GD.N0106.N0428.N0770.N1697.d021838 r) (_root_.GD.N0106.N0428.N0770.N1698.d021852 hr),
    _root_.GD.N0232.N0719.N0933.d009307]

end
end GD.N0106.N0428.N0770.N1698

#print axioms _root_.GD.N0106.N0428.N0770.N1698.d021852
#print axioms _root_.GD.N0106.N0428.N0770.N1698.d021853
#print axioms _root_.GD.N0106.N0428.N0770.N1698.d021854
#print axioms _root_.GD.N0106.N0428.N0770.N1698.d021855
#print axioms _root_.GD.N0106.N0428.N0770.N1698.d021856
#print axioms _root_.GD.N0106.N0428.N0770.N1698.d021857
#print axioms _root_.GD.N0106.N0428.N0770.N1698.d021858
#print axioms _root_.GD.N0106.N0428.N0770.N1698.d021859
#print axioms _root_.GD.N0106.N0428.N0770.N1698.d021860
#print axioms _root_.GD.N0106.N0428.N0770.N1698.d021861
#print axioms _root_.GD.N0106.N0428.N0770.N1698.d021862
#print axioms _root_.GD.N0106.N0428.N0770.N1698.d021863
#print axioms _root_.GD.N0106.N0428.N0770.N1698.d021864
