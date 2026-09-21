import GD.Module0682
import GD.Module0683
















open MeasureTheory Set

namespace GD.N0232.N0719.N0922

noncomputable section

open _root_.GD.N0232.N0719.N0928 _root_.GD.N0232.N0719.N0929



theorem d009971 :
    ∀ {ε : ℝ} {y t : Fin 3 → ℝ}, _root_.GD.N0232.N0719.N0922.d009928 ε y t →
    (∫ xz in _root_.GD.N0232.N0719.N0922.d009926, _root_.GD.N0232.N0719.N0922.d009964 y t xz) =
      _root_.GD.N0232.N0719.N0929.d009652 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2) -
        y 0 * _root_.GD.N0232.N0719.N0929.d009647 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2) := by
  intro ε y t hE
  let K : ℝ × ℝ → ℝ := fun xz ↦
    _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2)
  let M : ℝ × ℝ → ℝ := fun xz ↦ _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0922.d009922 xz) y
  rw [_root_.GD.N0232.N0719.N0922.d009942,
    _root_.GD.N0232.N0719.N0922.d009941]
  change (∫ xz in _root_.GD.N0232.N0719.N0922.d009926, K xz * (M xz - y 0)) =
    (∫ xz in _root_.GD.N0232.N0719.N0922.d009926, K xz * M xz) -
      y 0 * ∫ xz in _root_.GD.N0232.N0719.N0922.d009926, K xz
  have hresponse : IntegrableOn (fun xz ↦ K xz * (M xz - y 0))
      _root_.GD.N0232.N0719.N0922.d009926 := by
    change IntegrableOn (_root_.GD.N0232.N0719.N0922.d009964 y t) _root_.GD.N0232.N0719.N0922.d009926
    exact _root_.GD.N0232.N0719.N0922.d009968 hE
  have hK : IntegrableOn K _root_.GD.N0232.N0719.N0922.d009926 := by
    simpa [K] using _root_.GD.N0232.N0719.N0922.d009962 hE
  have hyK : IntegrableOn (fun xz ↦ y 0 * K xz) _root_.GD.N0232.N0719.N0922.d009926 :=
    hK.const_mul (y 0)
  have hKM : IntegrableOn (fun xz ↦ K xz * M xz) _root_.GD.N0232.N0719.N0922.d009926 := by
    have hadd := hresponse.add hyK
    have htriangle : MeasurableSet _root_.GD.N0232.N0719.N0922.d009926 := by
      unfold _root_.GD.N0232.N0719.N0922.d009926
      have hfst : Measurable (fun xz : ℝ × ℝ ↦ xz.1) := measurable_fst
      have hsnd : Measurable (fun xz : ℝ × ℝ ↦ xz.2) := measurable_snd
      have hsum : Measurable (fun xz : ℝ × ℝ ↦ xz.1 + xz.2) :=
        hfst.add hsnd
      have hzero : Measurable (fun _ : ℝ × ℝ ↦ (0 : ℝ)) := measurable_const
      have hone : Measurable (fun _ : ℝ × ℝ ↦ (1 : ℝ)) := measurable_const
      simpa only [Set.inter_def, Set.mem_setOf_eq, and_assoc] using
        (((measurableSet_lt hzero hfst).inter
          (measurableSet_lt hzero hsnd)).inter
          (measurableSet_lt hsum hone))
    exact hadd.congr_fun (fun xz _ ↦ by simp only [Pi.add_apply]; ring) htriangle
  rw [show (fun xz ↦ K xz * (M xz - y 0)) =
      fun xz ↦ K xz * M xz - y 0 * K xz by
    funext xz
    ring]
  rw [integral_sub hKM hyK, integral_const_mul]



theorem d009972
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t) :
    _root_.GD.N0232.N0719.N0929.d009653 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2) - y 0 =
      (∫ xz in _root_.GD.N0232.N0719.N0922.d009926, _root_.GD.N0232.N0719.N0922.d009964 y t xz) /
        _root_.GD.N0232.N0719.N0929.d009647 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2) := by
  have hshape : ∀ i, 0 < _root_.GD.N0232.N0719.N0922.d009915 i := by
    intro i
    fin_cases i <;> simp
  have ht : ∀ i, 0 < t i := by
    rcases hE with
      ⟨hε, hε1, ht0l, ht0u, ht1l, ht1u, ht2l, ht2u,
        hy1l, hy1u, hy2l, hy2u⟩
    intro i
    fin_cases i
    · simpa using (lt_of_lt_of_le hε ht0l)
    · simpa using (show (0 : ℝ) < t 1 by linarith)
    · simpa using (show (0 : ℝ) < t 2 by linarith)
  have hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 _root_.GD.N0232.N0719.N0922.d009915 (5 / 2) := by simp
  have hD : _root_.GD.N0232.N0719.N0929.d009647 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2) ≠ 0 :=
    _root_.GD.N0232.N0719.N0929.d009654 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2)
      hshape ht hpower
  unfold _root_.GD.N0232.N0719.N0929.d009653
  rw [_root_.GD.N0232.N0719.N0922.d009971 hE]
  field_simp [hD]



theorem d009973
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t) :
    _root_.GD.N0232.N0719.N0922.d009965 /
        (144 * (256 * _root_.GD.N0232.N0719.N0922.d009948 *
          Real.log ((ε + 1) / ε) ^ 2)) ≤
      _root_.GD.N0232.N0719.N0929.d009653 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2) - y 0 := by
  have hshape : ∀ i, 0 < _root_.GD.N0232.N0719.N0922.d009915 i := by
    intro i
    fin_cases i <;> simp
  have ht : ∀ i, 0 < t i := by
    rcases hE with
      ⟨hε, hε1, ht0l, ht0u, ht1l, ht1u, ht2l, ht2u,
        hy1l, hy1u, hy2l, hy2u⟩
    intro i
    fin_cases i
    · simpa using (lt_of_lt_of_le hε ht0l)
    · simpa using (show (0 : ℝ) < t 1 by linarith)
    · simpa using (show (0 : ℝ) < t 2 by linarith)
  have hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 _root_.GD.N0232.N0719.N0922.d009915 (5 / 2) := by simp
  let D := _root_.GD.N0232.N0719.N0929.d009647 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2)
  let R := ∫ xz in _root_.GD.N0232.N0719.N0922.d009926, _root_.GD.N0232.N0719.N0922.d009964 y t xz
  let L := Real.log ((ε + 1) / ε)
  have hD : 0 < D := by
    exact _root_.GD.N0232.N0719.N0929.d009648 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2)
      hshape ht hpower
  have hDupper : D ≤ 256 * _root_.GD.N0232.N0719.N0922.d009948 * L ^ 2 := by
    unfold D L
    rw [_root_.GD.N0232.N0719.N0922.d009941]
    exact _root_.GD.N0232.N0719.N0922.d009963 hE
  have hratio : 1 < (ε + 1) / ε := by
    rw [one_lt_div hE.1]
    linarith
  have hL : 0 < L := Real.log_pos hratio
  have hupperPos : 0 < 256 * _root_.GD.N0232.N0719.N0922.d009948 * L ^ 2 :=
    mul_pos (mul_pos (by norm_num) _root_.GD.N0232.N0719.N0922.d009949) (sq_pos_of_pos hL)
  have hR : _root_.GD.N0232.N0719.N0922.d009965 / 144 ≤ R := by
    exact _root_.GD.N0232.N0719.N0922.d009970 hE
  have hfloor : 0 ≤ _root_.GD.N0232.N0719.N0922.d009965 / 144 := by
    exact div_nonneg _root_.GD.N0232.N0719.N0922.d009966.le (by norm_num)
  have hdiv :
      (_root_.GD.N0232.N0719.N0922.d009965 / 144) /
          (256 * _root_.GD.N0232.N0719.N0922.d009948 * L ^ 2) ≤ R / D := by
    exact
      (div_le_div_of_nonneg_left hfloor hD hDupper).trans
        (div_le_div_of_nonneg_right hR hD.le)
  rw [_root_.GD.N0232.N0719.N0922.d009972 hE]
  change _root_.GD.N0232.N0719.N0922.d009965 /
      (144 * (256 * _root_.GD.N0232.N0719.N0922.d009948 * L ^ 2)) ≤ R / D
  convert hdiv using 1 <;> ring

end

end GD.N0232.N0719.N0922

#print axioms _root_.GD.N0232.N0719.N0922.d009971
#print axioms _root_.GD.N0232.N0719.N0922.d009972
#print axioms _root_.GD.N0232.N0719.N0922.d009973
