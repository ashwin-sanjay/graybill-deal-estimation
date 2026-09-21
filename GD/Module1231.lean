import GD.Module1225
import GD.Module0314












open MeasureTheory Set
open scoped Topology BigOperators

namespace GD.N0232.N0720.N1331

open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1329
open _root_.GD.N0232.N0720.N1315
open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0232.N0720.N1376
open _root_.GD.N0232.N0720.N1383 (d004674)

noncomputable section

private def d020042 (m : ℕ) (hm : 2 ≤ m) (r : ℝ) : Fin m → ℝ :=
  Pi.single ⟨0, by omega⟩ r - Pi.single ⟨1, by omega⟩ r

private theorem d020043 (m : ℕ) (hm : 2 ≤ m) (r : ℝ) :
    (∑ i, _root_.GD.N0232.N0720.N1331.d020042 m hm r i) = 0 := by
  simp [_root_.GD.N0232.N0720.N1331.d020042, Finset.sum_sub_distrib]

private theorem d020044 (m : ℕ) (hm : 2 ≤ m) (r : ℝ) :
    (∑ i, _root_.GD.N0232.N0720.N1331.d020042 m hm r i ^ 2) = 2 * r ^ 2 := by
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; norm_num [i0, i1] at this
  have heq (i : Fin m) : _root_.GD.N0232.N0720.N1331.d020042 m hm r i ^ 2 =
      (Pi.single i0 (r ^ 2) : Fin m → ℝ) i + (Pi.single i1 (r ^ 2) : Fin m → ℝ) i := by
    by_cases h0 : i = i0
    · subst i
      simp [_root_.GD.N0232.N0720.N1331.d020042, i0, i1, h01]
    · by_cases h1 : i = i1
      · subst i
        simp [_root_.GD.N0232.N0720.N1331.d020042, i0, i1, Ne.symm h01]
      · simp [_root_.GD.N0232.N0720.N1331.d020042, i0, i1, h0, h1]
  simp_rw [heq]
  simp [Finset.sum_add_distrib, two_mul]

private def d020045 (m : ℕ) (hm : 2 ≤ m) (c : ℝ) : Fin m → ℝ :=
  fun i ↦ _root_.GD.N0232.N0720.N1331.d020042 m hm (Real.sqrt (m : ℝ)) i + c

private theorem d020046 (m : ℕ) (hm : 2 ≤ m) (c : ℝ) :
    _root_.GD.N0107.d009084 (_root_.GD.N0232.N0720.N1331.d020045 m hm c) = c := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  unfold _root_.GD.N0107.d009084 _root_.GD.N0126.d006420 _root_.GD.N0126.d006419 _root_.GD.N0232.N0720.N1331.d020045
  rw [Finset.sum_add_distrib, _root_.GD.N0232.N0720.N1331.d020043]
  simp [hmR]

private theorem d020047 (m : ℕ) (hm : 2 ≤ m) (c : ℝ) :
    _root_.GD.N0126.d006422 (_root_.GD.N0232.N0720.N1331.d020045 m hm c) = 2 * m := by
  letI : NeZero m := ⟨by omega⟩
  have hmean : _root_.GD.N0126.d006420 (_root_.GD.N0232.N0720.N1331.d020045 m hm c) = c := by
    simpa only [_root_.GD.N0126.d006420, _root_.GD.N0126.d006419,
      Fintype.card_fin, _root_.GD.N0107.d009084] using _root_.GD.N0232.N0720.N1331.d020046 m hm c
  unfold _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
  rw [hmean]
  simp only [_root_.GD.N0232.N0720.N1331.d020045, add_sub_cancel_right]
  rw [_root_.GD.N0232.N0720.N1331.d020044, Real.sq_sqrt (Nat.cast_nonneg m)]


theorem d020048 (m : ℕ) (hm : 2 ≤ m) (c : ℝ)
    {z : ℝ} (hz : 0 < z) :
    ∃ x : _root_.GD.N0137.d008894 m,
      _root_.GD.N0107.d009084 x = c ∧ _root_.GD.N0126.d006422 x = 2 * m * z := by
  let r := Real.sqrt ((m : ℝ) * z)
  let x : _root_.GD.N0137.d008894 m := fun i ↦ _root_.GD.N0232.N0720.N1331.d020042 m hm r i + c
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hmean : _root_.GD.N0107.d009084 x = c := by
    unfold _root_.GD.N0107.d009084 _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
    dsimp [x]
    rw [Finset.sum_add_distrib, _root_.GD.N0232.N0720.N1331.d020043]
    simp [hmR]
  refine ⟨x, hmean, ?_⟩
  change _root_.GD.N0126.d006420 x = c at hmean
  unfold _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
  rw [hmean]
  simp only [x, add_sub_cancel_right]
  rw [_root_.GD.N0232.N0720.N1331.d020044]
  dsimp [r]
  rw [Real.sq_sqrt (by positivity : 0 ≤ (m : ℝ) * z)]
  ring

theorem d020049 {m n d : ℕ} (hdim : m + n = d + 1) :
    Continuous (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim) := by
  have hf : Continuous (fun x : _root_.GD.N0232.N0720.N1341.d004414 d ↦ ((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm x).1) := by
    apply continuous_pi
    intro i
    change Continuous (fun x : _root_.GD.N0232.N0720.N1341.d004414 d ↦ x (_root_.GD.N0232.N0720.N1329.d019647 m n d hdim (.inl i)))
    fun_prop
  have hg : Continuous (fun x : _root_.GD.N0232.N0720.N1341.d004414 d ↦ ((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm x).2) := by
    apply continuous_pi
    intro i
    change Continuous (fun x : _root_.GD.N0232.N0720.N1341.d004414 d ↦ x (_root_.GD.N0232.N0720.N1329.d019647 m n d hdim (.inr i)))
    fun_prop
  apply continuous_pi
  intro i
  fin_cases i <;>
    dsimp [_root_.GD.N0232.N0720.N1315.d019850, _root_.GD.N0107.d009084, _root_.GD.N0126.d006422,
      _root_.GD.N0126.d006421, _root_.GD.N0126.d006420,
      _root_.GD.N0126.d006419] <;> fun_prop

def d020050 (lo hi : ℝ) : Set _root_.GD.N0232.N0720.N1315.d019833 :=
  {x | x 0 ∈ Ioo lo hi ∧ x 1 ∈ Ioo lo hi ∧
    x 2 ∈ Ioo (1 / 2 : ℝ) 2 ∧ x 3 ∈ Ioo (1 / 2 : ℝ) 2}

theorem d020051 (lo hi : ℝ) : IsOpen (_root_.GD.N0232.N0720.N1331.d020050 lo hi) := by
  exact (isOpen_Ioo.preimage (continuous_apply 0)).inter
    ((isOpen_Ioo.preimage (continuous_apply 1)).inter
      ((isOpen_Ioo.preimage (continuous_apply 2)).inter
        (isOpen_Ioo.preimage (continuous_apply 3))))

def d020052 (m n d : ℕ) (hdim : m + n = d + 1) (lo hi : ℝ) : Set (_root_.GD.N0232.N0720.N1341.d004414 d) :=
  (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim) ⁻¹' _root_.GD.N0232.N0720.N1331.d020050 lo hi

theorem d020053 {m n d : ℕ} (hdim : m + n = d + 1) (lo hi : ℝ) :
    IsOpen (_root_.GD.N0232.N0720.N1331.d020052 m n d hdim lo hi) :=
  (_root_.GD.N0232.N0720.N1331.d020051 lo hi).preimage (_root_.GD.N0232.N0720.N1331.d020049 hdim)

theorem d020054 {m n d : ℕ} (hdim : m + n = d + 1)
    (hm : 2 ≤ m) (hn : 2 ≤ n) {lo hi : ℝ} (hwidth : lo < hi) :
    (_root_.GD.N0232.N0720.N1331.d020052 m n d hdim lo hi).Nonempty := by
  let c := (lo + hi) / 2
  let x := _root_.GD.N0232.N0720.N1329.d019648 m n d hdim (_root_.GD.N0232.N0720.N1331.d020045 m hm c, _root_.GD.N0232.N0720.N1331.d020045 n hn c)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨x, ?_⟩
  change _root_.GD.N0232.N0720.N1315.d019850 m n d hdim x ∈ _root_.GD.N0232.N0720.N1331.d020050 lo hi
  dsimp [x, _root_.GD.N0232.N0720.N1315.d019850, _root_.GD.N0232.N0720.N1331.d020050]
  simp only [MeasurableEquiv.symm_apply_apply, _root_.GD.N0232.N0720.N1331.d020046, _root_.GD.N0232.N0720.N1331.d020047]
  have hmid : c ∈ Ioo lo hi := by dsimp [c]; constructor <;> linarith
  simpa [hmR, hnR] using And.intro hmid (And.intro hmid
    (show (1 : ℝ) ∈ Ioo (1 / 2) 2 ∧ (1 : ℝ) ∈ Ioo (1 / 2) 2 by norm_num))

theorem d020055 {m n d : ℕ} (hdim : m + n = d + 1)
    (hm : 2 ≤ m) (hn : 2 ≤ n) {lo hi : ℝ} (hwidth : lo < hi)
    {P : _root_.GD.N0232.N0720.N1341.d004414 d → Prop} (hP : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)), P x) :
    ∃ x ∈ _root_.GD.N0232.N0720.N1331.d020052 m n d hdim lo hi, P x := by
  have hpos := (_root_.GD.N0232.N0720.N1331.d020053 hdim lo hi).measure_pos volume
    (_root_.GD.N0232.N0720.N1331.d020054 hdim hm hn hwidth)
  by_contra hnot
  have hempty : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)), x ∉ _root_.GD.N0232.N0720.N1331.d020052 m n d hdim lo hi := by
    filter_upwards [hP] with x hx hbox
    exact hnot ⟨x, hbox, hx⟩
  have hzero : (volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)) (_root_.GD.N0232.N0720.N1331.d020052 m n d hdim lo hi) = 0 := by
    simpa only [ae_iff, not_not] using! hempty
  exact hpos.ne' hzero

theorem d020056 {t lo hi : ℝ} {x : _root_.GD.N0232.N0720.N1315.d019833}
    (ht : t ∈ Icc (0 : ℝ) 1) (hlo : 0 ≤ lo) (hx : x ∈ _root_.GD.N0232.N0720.N1331.d020050 lo hi) :
    _root_.GD.N0232.N0720.N1376.d002893 t (x 0) (x 1) ∈ Icc lo hi ∧
      _root_.GD.N0232.N0720.N1376.d002892 t (x 0) (x 1) (x 2) (x 3) ∈ Icc (lo ^ 2 + 1) (hi ^ 2 + 4) := by
  have hX := Ioo_subset_Icc_self hx.1
  have hY := Ioo_subset_Icc_self hx.2.1
  refine ⟨_root_.GD.N0232.N0720.N1383.d004674 ht hX hY, ?_⟩
  have hpoly : _root_.GD.N0232.N0720.N1376.d002892 t (x 0) (x 1) (x 2) (x 3) =
      (1 - t) * ((x 0) ^ 2 + 2 * x 2) + t * ((x 1) ^ 2 + 2 * x 3) := by
    unfold _root_.GD.N0232.N0720.N1376.d002892
    ring
  rw [hpoly]
  apply _root_.GD.N0232.N0720.N1383.d004674 ht
  · have hslo := (sq_le_sq₀ hlo (hlo.trans hX.1)).2 hX.1
    have hshi := (sq_le_sq₀ (hlo.trans hX.1) (hlo.trans (hX.1.trans hX.2))).2 hX.2
    constructor <;> linarith [hx.2.2.1.1, hx.2.2.1.2]
  · have hslo := (sq_le_sq₀ hlo (hlo.trans hY.1)).2 hY.1
    have hshi := (sq_le_sq₀ (hlo.trans hY.1) (hlo.trans (hY.1.trans hY.2))).2 hY.2
    constructor <;> linarith [hx.2.2.2.1, hx.2.2.2.2]

theorem d020057 {t lo hi level delta : ℝ} {x : _root_.GD.N0232.N0720.N1315.d019833}
    (ht : t ∈ Icc (0 : ℝ) 1) (hlo : 0 < lo) (hx : x ∈ _root_.GD.N0232.N0720.N1331.d020050 lo hi)
    (hlevel : hi ≤ level + delta) (hmargin : (level + delta - lo) * hi ≤ 1) :
    level + delta ≤ _root_.GD.N0232.N0720.N1376.d002892 t (x 0) (x 1) (x 2) (x 3) / _root_.GD.N0232.N0720.N1376.d002893 t (x 0) (x 1) := by
  have hB : 0 < _root_.GD.N0232.N0720.N1376.d002893 t (x 0) (x 1) :=
    hlo.trans_le (_root_.GD.N0232.N0720.N1331.d020056 ht hlo.le hx).1.1
  apply (le_div_iff₀ hB).2
  have hsingle (X z : ℝ) (hX : X ∈ Ioo lo hi) (hz : (1 / 2 : ℝ) < z) :
      (level + delta) * X ≤ X ^ 2 + 2 * z := by
    have hXpos : 0 ≤ X := (hlo.trans hX.1).le
    have hg : 0 ≤ level + delta - lo := by linarith [hX.1, hX.2]
    have hm := mul_le_mul_of_nonneg_left hX.2.le hg
    have hl := mul_le_mul_of_nonneg_right hX.1.le hXpos
    nlinarith
  have h0 := mul_le_mul_of_nonneg_left (hsingle (x 0) (x 2) hx.1 hx.2.2.1.1)
    (sub_nonneg.mpr ht.2)
  have h1 := mul_le_mul_of_nonneg_left (hsingle (x 1) (x 3) hx.2.1 hx.2.2.2.1) ht.1
  unfold _root_.GD.N0232.N0720.N1376.d002892 _root_.GD.N0232.N0720.N1376.d002893
  nlinarith

theorem d020058 {t lo hi beta : ℝ} {x : _root_.GD.N0232.N0720.N1315.d019833}
    (ht : t ∈ Icc (0 : ℝ) 1) (hlo : 0 < lo) (hx : x ∈ _root_.GD.N0232.N0720.N1331.d020050 lo hi)
    (hbeta : 0 ≤ beta) (hrate : 2 * beta * (hi ^ 2 + 4) ≤ lo ^ 2) :
    beta ≤ _root_.GD.N0232.N0720.N1376.d002893 t (x 0) (x 1) ^ 2 / (2 * _root_.GD.N0232.N0720.N1376.d002892 t (x 0) (x 1) (x 2) (x 3)) := by
  obtain ⟨hB, hA⟩ := _root_.GD.N0232.N0720.N1331.d020056 ht hlo.le hx
  have hApos : 0 < _root_.GD.N0232.N0720.N1376.d002892 t (x 0) (x 1) (x 2) (x 3) := by nlinarith [hA.1, sq_nonneg lo]
  apply (le_div_iff₀ (mul_pos (by norm_num) hApos)).2
  have hsquare := (sq_le_sq₀ hlo.le (hlo.trans_le hB.1).le).2 hB.1
  have hupper := mul_le_mul_of_nonneg_left hA.2 (by positivity : 0 ≤ 2 * beta)
  nlinarith

end
end GD.N0232.N0720.N1331

#print axioms _root_.GD.N0232.N0720.N1331.d020055
