import GD.Module1396
import GD.Module0558















set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory Filter
open scoped Topology Interval BigOperators

namespace GD.N0201
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1089
open _root_.GD.N0163 _root_.GD.N0180 _root_.GD.N0179
open _root_.GD.N0174 _root_.GD.N0172
open _root_.GD.N0082.N0334
open _root_.GD.N0149.N0432 _root_.GD.N0016


theorem d022502 {u : ℝ} (hu : 0 < u) :
    ContinuousAt (_root_.GD.N0179.d006021 u) 0 := by
  have hr : ContinuousAt (fun x : ℝ => x / (x + 2 * u)) 0 :=
    continuousAt_id.div (continuousAt_id.add continuousAt_const) (by linarith)
  have hs : ContinuousAt (_root_.GD.N0179.d006020 u) 0 := hr.sqrt
  have hc : ContinuousAt (fun x => _root_.GD.N0179.d006019 (_root_.GD.N0179.d006020 u x)) 0 := by
    unfold _root_.GD.N0179.d006019
    fun_prop
  exact hc.div_const (u ^ 2)


theorem d022503 {u : ℝ} (hu : 0 < u) :
    Tendsto (_root_.GD.N0179.d006021 u) atTop (𝓝 (1 / u ^ 2)) := by
  have ht : Tendsto (fun x : ℝ => 8 / x ^ 2) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).const_div_atTop 8
  have hlo : Tendsto (fun x : ℝ => 1 / u ^ 2 - 8 / x ^ 2)
      atTop (𝓝 (1 / u ^ 2)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with x hx
    linarith [_root_.GD.N0179.d006043 hu hx]
  · exact Eventually.of_forall (fun x => _root_.GD.N0179.d006032 u x)

private theorem d022504 {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    0 ≤ _root_.GD.N0179.d006018 u x := by
  have hd : 0 < x + 2 * u := by linarith
  unfold _root_.GD.N0179.d006018
  positivity


theorem d022505 {u : ℝ} (hu : 0 < u) :
    IntegrableOn (_root_.GD.N0179.d006018 u) (Ioi (0 : ℝ)) volume :=
  integrableOn_Ioi_deriv_of_nonneg (_root_.GD.N0201.d022502 hu).continuousWithinAt
    (fun _ hx => _root_.GD.N0179.d006036 hu hx)
    (fun _ hx => _root_.GD.N0201.d022504 hu hx) (_root_.GD.N0201.d022503 hu)

theorem d022506 {u : ℝ} (hu : 0 < u) :
    (∫ x in Ioi (0 : ℝ), _root_.GD.N0179.d006018 u x) = 1 / u ^ 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    (_root_.GD.N0201.d022502 hu).continuousWithinAt
    (fun _ hx => _root_.GD.N0179.d006036 hu hx)
    (fun _ hx => _root_.GD.N0201.d022504 hu hx) (_root_.GD.N0201.d022503 hu)
  simpa only [_root_.GD.N0179.d006033, sub_zero] using h


theorem d022507 (t u s : ℝ) :
    _root_.GD.N0178.d007131 t u s =
      _root_.GD.N0179.d006018 ((1 - u) / (1 - t) + u / t) s / (t ^ 2 * (1 - t) ^ 2) := by
  have hd : s + 2 * ((1 - u) / (1 - t) + u / t) =
      _root_.GD.N0178.d007129 t u s := by
    unfold _root_.GD.N0178.d007129
    ring
  unfold _root_.GD.N0178.d007131 _root_.GD.N0179.d006018
  rw [hd, div_div]
  unfold _root_.GD.N0178.d007130
  congr 1
  ring


theorem d022508 (t : _root_.GD.N0232.N0720.N1441.d013676) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫ s in Ioi (0 : ℝ), _root_.GD.N0178.d007131 t u s) =
      1 / (_root_.GD.N0082.N0334.d008256 t u) ^ 2 := by
  let v : ℝ := (1 - u) / (1 - (t : ℝ)) + u / t
  have ht0 := t.property.1
  have ht1 : 0 < 1 - (t : ℝ) := sub_pos.mpr t.property.2
  have hv : 0 < v := add_pos
    (div_pos (sub_pos.mpr hu.2) ht1) (div_pos hu.1 ht0)
  have he : v * ((t : ℝ) * (1 - t)) = _root_.GD.N0082.N0334.d008256 t u := by
    unfold v _root_.GD.N0082.N0334.d008256
    field_simp [ht0.ne', ht1.ne'] <;> ring
  calc
    _ = (∫ s in Ioi (0 : ℝ), _root_.GD.N0179.d006018 v s) / ((t : ℝ) ^ 2 * (1 - t) ^ 2) := by
      simp_rw [_root_.GD.N0201.d022507]
      exact MeasureTheory.integral_div _ _
    _ = (1 / v ^ 2) / ((t : ℝ) ^ 2 * (1 - t) ^ 2) := by
      rw [_root_.GD.N0201.d022506 hv]
    _ = _ := by
      rw [div_div]
      congr 1
      calc
        v ^ 2 * ((t : ℝ) ^ 2 * (1 - t) ^ 2) = (v * ((t : ℝ) * (1 - t))) ^ 2 := by ring
        _ = _ := by rw [he]


theorem d022509 (t : _root_.GD.N0232.N0720.N1441.d013676) (H : ℝ → ℝ) (hH : Measurable H)
    {B : ℝ} (hB : ∀ u, |H u| ≤ B) :
    _root_.GD.N0180.d022173 t (fun p => H p.1) = _root_.GD.N0082.N0334.d008258 H t := by
  have hm : Measurable (fun p : _root_.GD.N0232.N0720.N1436.d013217 => H p.1) := hH.comp measurable_fst
  have hi := _root_.GD.N0180.d022174 t (fun p => H p.1) hm (fun p => hB p.1)
  change (∫ p in (Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)),
    _root_.GD.N0178.d007131 t p.1 p.2 * (H p.1 - t) ^ 2) = _
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.setIntegral_prod _ hi]
  unfold _root_.GD.N0082.N0334.d008258
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  change (∫ s in Ioi (0 : ℝ), _root_.GD.N0178.d007131 t u s *
    (H u - t) ^ 2) = ((H u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2
  rw [MeasureTheory.integral_mul_const, _root_.GD.N0201.d022508 t hu]
  rw [div_pow]
  ring


def d022510 : _root_.GD.N0172.d022466 :=
  ⟨fun p => _root_.GD.N0232.N0720.N1089.d003092 p.1.1,
    _root_.GD.N0149.N0432.d008282.comp (measurable_fst.comp measurable_subtype_coe),
    fun p => _root_.GD.N0149.N0432.d008281 p.1.1⟩

theorem d022511 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0180.d022173 t (_root_.GD.N0163.d022211 _root_.GD.N0201.d022510.1) = _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 t := by
  calc
    _ = _root_.GD.N0180.d022173 t (fun p => _root_.GD.N0232.N0720.N1089.d003092 p.1) := by
      unfold _root_.GD.N0180.d022173
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with p hp
      rw [show _root_.GD.N0163.d022211 _root_.GD.N0201.d022510.1 p = _root_.GD.N0232.N0720.N1089.d003092 p.1 from
        _root_.GD.N0163.d022212 _root_.GD.N0201.d022510.1 ⟨p, hp⟩]
    _ = _ := _root_.GD.N0201.d022509 t _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0149.N0432.d008282
      (fun u => by
        rw [abs_of_nonneg (_root_.GD.N0149.N0432.d008281 u).1]
        exact (_root_.GD.N0149.N0432.d008281 u).2)


theorem d022512 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0180.d022173 t (_root_.GD.N0163.d022211 _root_.GD.N0201.d022510.1) < Real.pi / 4 := by
  rw [_root_.GD.N0201.d022511]
  exact _root_.GD.N0016.d008320 t t.property


theorem d022513 {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) :
    _root_.GD.N0174.d022397 A T _root_.GD.N0201.d022510.1 ≤ Real.pi / 4 := by
  have hAB : A ≤ A + T := by linarith
  have hi := _root_.GD.N0174.d022409 hA hAB _root_.GD.N0201.d022510.1
    _root_.GD.N0201.d022510.property.1 _root_.GD.N0201.d022510.property.2
  have hpoint : ∀ r ∈ Icc A (A + T),
      (∫ p, _root_.GD.N0174.d022396 _root_.GD.N0201.d022510.1 r p ∂_root_.GD.N0232.N0720.N1436.d013288) ≤
        2 * (Real.pi / 4) := by
    intro r hr
    have hr0 := hA.trans_le hr.1
    rw [_root_.GD.N0174.d022401 hr0 _root_.GD.N0201.d022510.1
      _root_.GD.N0201.d022510.property.1 _root_.GD.N0201.d022510.property.2]
    linarith [_root_.GD.N0201.d022512 (_root_.GD.N0174.d022394 r hr0),
      _root_.GD.N0201.d022512 (_root_.GD.N0174.d022395 r hr0)]
  have hint := intervalIntegral.integral_mono_on hAB hi
    (intervalIntegrable_const (c := 2 * (Real.pi / 4))) hpoint
  have hmul := mul_le_mul_of_nonneg_left hint
    (one_div_nonneg.mpr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hT.le))
  have he : 1 / (2 * T) * (∫ _r in A..(A + T), 2 * (Real.pi / 4)) = Real.pi / 4 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp [hT.ne'] <;> ring
  rw [he] at hmul
  exact hmul


theorem d022514 {A T : ℝ} (hA : 0 < A) (hT : 0 < T) :
    _root_.GD.N0172.d022468 A T ≤ Real.pi / 4 :=
  (_root_.GD.N0172.d022473 hA hT _root_.GD.N0201.d022510).trans
    (_root_.GD.N0201.d022513 hA hT)


theorem d022515 {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676) (hp : ∀ i, 0 < p i)
    (hsum : (∑ i, p i) = 1) : _root_.GD.N0163.d022186 p t < Real.pi / 4 := by
  classical
  have hmin := _root_.GD.N0163.d022215 p t hp _root_.GD.N0201.d022510.1
    _root_.GD.N0201.d022510.property.1 _root_.GD.N0201.d022510.property.2
  rw [_root_.GD.N0163.d022209 p t hp] at hmin
  have hstrict : _root_.GD.N0163.d022185 p t (_root_.GD.N0163.d022211 _root_.GD.N0201.d022510.1) <
      ∑ i, p i * (Real.pi / 4) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun i _ => mul_lt_mul_of_pos_left (_root_.GD.N0201.d022512 (t i)) (hp i))
  rw [← Finset.sum_mul, hsum, one_mul] at hstrict
  exact hmin.trans_lt hstrict

end
end GD.N0201

#print axioms _root_.GD.N0201.d022502
#print axioms _root_.GD.N0201.d022503
#print axioms _root_.GD.N0201.d022505
#print axioms _root_.GD.N0201.d022506
#print axioms _root_.GD.N0201.d022507
#print axioms _root_.GD.N0201.d022508
#print axioms _root_.GD.N0201.d022509
#print axioms _root_.GD.N0201.d022511
#print axioms _root_.GD.N0201.d022512
#print axioms _root_.GD.N0201.d022513
#print axioms _root_.GD.N0201.d022514
#print axioms _root_.GD.N0201.d022515
