import GD.Module0312
import GD.Module0212









open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1382

open _root_.GD.N0232.N0720.N1373 _root_.GD.N0232.N0720.N1376
open _root_.GD.N0232.N0720.N1377 _root_.GD.N0232.N0720.N1375
open _root_.GD.N0232.N0720.N1379

noncomputable section

abbrev d004651 := Fin 4 → ℝ

def d004652 : Set _root_.GD.N0232.N0720.N1382.d004651 := {x | 0 < x 2 ∧ 0 < x 3}

theorem d004653 : IsOpen _root_.GD.N0232.N0720.N1382.d004652 := by
  have hzero : Continuous (fun _ : _root_.GD.N0232.N0720.N1382.d004651 ↦ (0 : ℝ)) := continuous_const
  have hz : Continuous (fun x : _root_.GD.N0232.N0720.N1382.d004651 ↦ x 2) := by fun_prop
  have hw : Continuous (fun x : _root_.GD.N0232.N0720.N1382.d004651 ↦ x 3) := by fun_prop
  exact (isOpen_lt hzero hz).inter (isOpen_lt hzero hw)

def d004654 (x : _root_.GD.N0232.N0720.N1382.d004651) (t : _root_.GD.N0232.N0720.N1373.d004628) : ℝ := _root_.GD.N0232.N0720.N1376.d002892 t.1 (x 0) (x 1) (x 2) (x 3)
def d004655 (x : _root_.GD.N0232.N0720.N1382.d004651) (t : _root_.GD.N0232.N0720.N1373.d004628) : ℝ := _root_.GD.N0232.N0720.N1376.d002893 t.1 (x 0) (x 1)

theorem d004656 {x : _root_.GD.N0232.N0720.N1382.d004651} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) (t : _root_.GD.N0232.N0720.N1373.d004628) : 0 < _root_.GD.N0232.N0720.N1382.d004654 x t :=
  _root_.GD.N0232.N0720.N1376.d002898 t.2 hx.1 hx.2 (x 0) (x 1)

def d004657 (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) : Prop :=
  ∀ beta : ℝ, 0 < beta → beta < 1 / 2 →
    Integrable (fun p : _root_.GD.N0232.N0720.N1373.d004629 ↦ Real.exp (beta * p.1 ^ 2)) ν


theorem d004658 (m : ℕ) {inner outer : ℝ}
    (hgap : inner < outer) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℝ,
      |k| ^ m * Real.exp (inner * k ^ 2) ≤ C * Real.exp (outer * k ^ 2) := by
  let f : ℝ → ℝ := fun k ↦
    |k| ^ m * Real.exp (inner * k ^ 2) / Real.exp (outer * k ^ 2)
  have hf : Continuous f := by
    unfold f
    exact Continuous.div₀ (by fun_prop) (by fun_prop)
      (fun k ↦ Real.exp_ne_zero (outer * k ^ 2))
  have he : ∀ᶠ k in cocompact ℝ, f k < 1 :=
    (_root_.GD.N0232.N0720.N1375.d002939 m hgap).eventually (eventually_lt_nhds (by norm_num))
  obtain ⟨r, hr⟩ := closedBall_compl_subset_of_mem_cocompact he (0 : ℝ)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ) r).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro k
  apply (div_le_iff₀ (Real.exp_pos _)).1
  change f k ≤ max C 1
  by_cases hk : k ∈ closedBall (0 : ℝ) r
  · exact (le_trans (le_abs_self (f k)) (hC k hk)).trans (le_max_left _ _)
  · exact (hr hk).le.trans (le_max_right _ _)

def d004659 (delta R : ℝ) : Set _root_.GD.N0232.N0720.N1382.d004651 :=
  {x | |x 0| < R ∧ |x 1| < R ∧ delta < x 2 ∧ delta < x 3}

theorem d004660 (delta R : ℝ) : IsOpen (_root_.GD.N0232.N0720.N1382.d004659 delta R) := by
  have hdelta : Continuous (fun _ : _root_.GD.N0232.N0720.N1382.d004651 ↦ delta) := continuous_const
  have hR : Continuous (fun _ : _root_.GD.N0232.N0720.N1382.d004651 ↦ R) := continuous_const
  have hX : Continuous (fun x : _root_.GD.N0232.N0720.N1382.d004651 ↦ |x 0|) := by fun_prop
  have hY : Continuous (fun x : _root_.GD.N0232.N0720.N1382.d004651 ↦ |x 1|) := by fun_prop
  have hz : Continuous (fun x : _root_.GD.N0232.N0720.N1382.d004651 ↦ x 2) := by fun_prop
  have hw : Continuous (fun x : _root_.GD.N0232.N0720.N1382.d004651 ↦ x 3) := by fun_prop
  exact (isOpen_lt hX hR).inter ((isOpen_lt hY hR).inter
    ((isOpen_lt hdelta hz).inter (isOpen_lt hdelta hw)))

theorem d004661 {delta R : ℝ} {x : _root_.GD.N0232.N0720.N1382.d004651} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004659 delta R)
    (t : _root_.GD.N0232.N0720.N1373.d004628) : |_root_.GD.N0232.N0720.N1382.d004655 x t| ≤ R := by
  have ht0 := t.2.1
  have ht1 : 0 ≤ 1 - t.1 := sub_nonneg.mpr t.2.2
  unfold _root_.GD.N0232.N0720.N1382.d004655 _root_.GD.N0232.N0720.N1376.d002893
  calc
    _ ≤ |(1 - t.1) * x 0| + |t.1 * x 1| := abs_add_le _ _
    _ = (1 - t.1) * |x 0| + t.1 * |x 1| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht1, abs_of_nonneg ht0]
    _ ≤ (1 - t.1) * R + t.1 * R :=
      add_le_add (mul_le_mul_of_nonneg_left hx.1.le ht1)
        (mul_le_mul_of_nonneg_left hx.2.1.le ht0)
    _ = R := by ring

theorem d004662 {delta R : ℝ} {x : _root_.GD.N0232.N0720.N1382.d004651} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004659 delta R)
    (t : _root_.GD.N0232.N0720.N1373.d004628) : _root_.GD.N0232.N0720.N1382.d004655 x t ^ 2 + 2 * delta ≤ _root_.GD.N0232.N0720.N1382.d004654 x t := by
  have ht0 := t.2.1
  have ht1 : 0 ≤ 1 - t.1 := sub_nonneg.mpr t.2.2
  have h0 := mul_nonneg (mul_nonneg ht0 ht1) (sq_nonneg (x 0 - x 1))
  have hz := mul_nonneg ht1 (sub_nonneg.mpr hx.2.2.1.le)
  have hw := mul_nonneg ht0 (sub_nonneg.mpr hx.2.2.2.le)
  have hid := _root_.GD.N0232.N0720.N1376.d002896 t.1 (x 0) (x 1) (x 2) (x 3)
  change _root_.GD.N0232.N0720.N1382.d004655 x t ^ 2 + 2 * delta ≤ _root_.GD.N0232.N0720.N1382.d004654 x t
  dsimp [_root_.GD.N0232.N0720.N1382.d004654, _root_.GD.N0232.N0720.N1382.d004655] at *
  nlinarith

def d004663 (delta R : ℝ) : ℝ := R ^ 2 / (2 * (R ^ 2 + 2 * delta))

theorem d004664 {delta R : ℝ} (hd : 0 < delta) (hR : 0 < R) : 0 < _root_.GD.N0232.N0720.N1382.d004663 delta R := by
  unfold _root_.GD.N0232.N0720.N1382.d004663
  positivity

theorem d004665 {delta R : ℝ} (hd : 0 < delta) : _root_.GD.N0232.N0720.N1382.d004663 delta R < 1 / 2 := by
  unfold _root_.GD.N0232.N0720.N1382.d004663
  apply (div_lt_iff₀ (by positivity : 0 < 2 * (R ^ 2 + 2 * delta))).2
  nlinarith

theorem d004666 {delta R : ℝ} (hd : 0 < delta) (hR : 0 < R)
    {x : _root_.GD.N0232.N0720.N1382.d004651} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004659 delta R) (t : _root_.GD.N0232.N0720.N1373.d004628) :
    2 * delta ≤ _root_.GD.N0232.N0720.N1382.d004654 x t ∧ _root_.GD.N0232.N0720.N1382.d004655 x t ^ 2 / (2 * _root_.GD.N0232.N0720.N1382.d004654 x t) ≤ _root_.GD.N0232.N0720.N1382.d004663 delta R := by
  have hgap := _root_.GD.N0232.N0720.N1382.d004662 hx t
  have hb := _root_.GD.N0232.N0720.N1382.d004661 hx t
  have hbsq : _root_.GD.N0232.N0720.N1382.d004655 x t ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR.le).2 hb
  have hA : 0 < _root_.GD.N0232.N0720.N1382.d004654 x t := by nlinarith [sq_nonneg (_root_.GD.N0232.N0720.N1382.d004655 x t)]
  refine ⟨by nlinarith [sq_nonneg (_root_.GD.N0232.N0720.N1382.d004655 x t)], ?_⟩
  unfold _root_.GD.N0232.N0720.N1382.d004663
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * _root_.GD.N0232.N0720.N1382.d004654 x t)
    (by positivity : 0 < 2 * (R ^ 2 + 2 * delta))).2
  have h1 := mul_le_mul_of_nonneg_left hgap (sq_nonneg R)
  have h2 := mul_le_mul_of_nonneg_left hbsq hd.le
  nlinarith


theorem d004667 {x : _root_.GD.N0232.N0720.N1382.d004651} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) :
    ∃ delta R : ℝ, 0 < delta ∧ 0 < R ∧ _root_.GD.N0232.N0720.N1382.d004659 delta R ∈ 𝓝 x := by
  let delta := min (x 2) (x 3) / 2
  let R := |x 0| + |x 1| + 1
  have hd : 0 < delta := div_pos (lt_min_iff.mpr ⟨hx.1, hx.2⟩) (by norm_num)
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨delta, R, hd, hR, (_root_.GD.N0232.N0720.N1382.d004660 _ _).mem_nhds ?_⟩
  refine ⟨by dsimp [R]; linarith [abs_nonneg (x 1)],
    by dsimp [R]; linarith [abs_nonneg (x 0)], ?_, ?_⟩
  · have hm := min_le_left (x 2) (x 3)
    dsimp [delta] at hd ⊢
    linarith
  · have hm := min_le_right (x 2) (x 3)
    dsimp [delta] at hd ⊢
    linarith

def d004668 (n m : ℕ) (phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ) (x : _root_.GD.N0232.N0720.N1382.d004651)
    (p : _root_.GD.N0232.N0720.N1373.d004629) : ℝ :=
  p.1 ^ m * phi p.2 * _root_.GD.N0232.N0720.N1377.d002852 n (_root_.GD.N0232.N0720.N1382.d004654 x p.2) (_root_.GD.N0232.N0720.N1382.d004655 x p.2 * p.1)

theorem d004669 (n m : ℕ) {phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ}
    (hphi : Continuous phi) {x : _root_.GD.N0232.N0720.N1382.d004651} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) :
    Continuous (_root_.GD.N0232.N0720.N1382.d004668 n m phi x) := by
  have hG : Continuous (fun p : _root_.GD.N0232.N0720.N1373.d004629 ↦
      _root_.GD.N0232.N0720.N1377.d002852 n (_root_.GD.N0232.N0720.N1382.d004654 x p.2) (_root_.GD.N0232.N0720.N1382.d004655 x p.2 * p.1)) := by
    apply continuous_iff_continuousAt.2
    intro p
    exact (_root_.GD.N0232.N0720.N1379.d002889 n
      (p := (_root_.GD.N0232.N0720.N1382.d004654 x p.2, _root_.GD.N0232.N0720.N1382.d004655 x p.2 * p.1)) (_root_.GD.N0232.N0720.N1382.d004656 hx p.2)).continuousAt.comp
      (f := fun p : _root_.GD.N0232.N0720.N1373.d004629 ↦ (_root_.GD.N0232.N0720.N1382.d004654 x p.2, _root_.GD.N0232.N0720.N1382.d004655 x p.2 * p.1))
      (x := p)
      (show ContinuousAt (fun p : _root_.GD.N0232.N0720.N1373.d004629 ↦ (_root_.GD.N0232.N0720.N1382.d004654 x p.2, _root_.GD.N0232.N0720.N1382.d004655 x p.2 * p.1)) p by
        unfold _root_.GD.N0232.N0720.N1382.d004654 _root_.GD.N0232.N0720.N1382.d004655 _root_.GD.N0232.N0720.N1376.d002892 _root_.GD.N0232.N0720.N1376.d002893
        fun_prop)
  exact ((continuous_fst.pow m).mul (hphi.comp continuous_snd)).mul hG



theorem d004670 (n m : ℕ) {phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ}
    (hphi : Continuous phi) {delta R beta : ℝ} (hd : 0 < delta) (hR : 0 < R)
    (hbeta : _root_.GD.N0232.N0720.N1382.d004663 delta R < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ _root_.GD.N0232.N0720.N1382.d004659 delta R, ∀ p : _root_.GD.N0232.N0720.N1373.d004629,
      ‖_root_.GD.N0232.N0720.N1382.d004668 n m phi x p‖ ≤ C * Real.exp (beta * p.1 ^ 2) := by
  let b := _root_.GD.N0232.N0720.N1382.d004663 delta R
  let a := (b + beta) / 2
  let loss := a / b
  have hb : 0 < b := _root_.GD.N0232.N0720.N1382.d004664 hd hR
  have hba : b < a := by dsimp [a, b]; linarith
  have hab : a < beta := by dsimp [a, b]; linarith
  have hloss : 1 < loss := (lt_div_iff₀ hb).2 (by simpa using hba)
  have hlosspos : 0 < loss := lt_trans zero_lt_one hloss
  have hlossb : loss * b = a := div_mul_cancel₀ _ hb.ne'
  have hred : 0 < 2 * delta * (loss - 1) / loss := by positivity
  let C0 := _root_.GD.N0232.N0720.N1377.d002852 n (2 * delta * (loss - 1) / loss) 0
  have hC0 : 0 < C0 := _root_.GD.N0232.N0720.N1377.d002861 n hred 0
  obtain ⟨Cp, hCp, hpoly⟩ := _root_.GD.N0232.N0720.N1382.d004658 m hab
  obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn hphi.continuousOn
  let F := max D 1
  have hF : 0 < F := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hphiBound : ∀ t : _root_.GD.N0232.N0720.N1373.d004628, ‖phi t‖ ≤ F :=
    fun t ↦ (hD t (mem_univ t)).trans (le_max_left _ _)
  refine ⟨F * C0 * Cp, by positivity, ?_⟩
  intro x hx p
  obtain ⟨hA, hrate⟩ := _root_.GD.N0232.N0720.N1382.d004666 hd hR hx p.2
  have hApos : 0 < _root_.GD.N0232.N0720.N1382.d004654 x p.2 := lt_of_lt_of_le (by positivity) hA
  have hI := _root_.GD.N0232.N0720.N1375.d002934 n (Amin := 2 * delta)
    (by positivity) hA hloss hrate p.1
  rw [hlossb] at hI
  have hIpos := (_root_.GD.N0232.N0720.N1377.d002861 n hApos (_root_.GD.N0232.N0720.N1382.d004655 x p.2 * p.1)).le
  calc
    ‖_root_.GD.N0232.N0720.N1382.d004668 n m phi x p‖ = |p.1| ^ m * ‖phi p.2‖ *
        _root_.GD.N0232.N0720.N1377.d002852 n (_root_.GD.N0232.N0720.N1382.d004654 x p.2) (_root_.GD.N0232.N0720.N1382.d004655 x p.2 * p.1) := by
      rw [_root_.GD.N0232.N0720.N1382.d004668, norm_mul, norm_mul, norm_pow, Real.norm_eq_abs p.1,
        Real.norm_eq_abs (_root_.GD.N0232.N0720.N1377.d002852 _ _ _), abs_of_nonneg hIpos]
    _ ≤ |p.1| ^ m * F * (Real.exp (a * p.1 ^ 2) * C0) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hphiBound p.2) (pow_nonneg (abs_nonneg _) _))
        hI hIpos (mul_nonneg (pow_nonneg (abs_nonneg _) _) hF.le)
    _ = (F * C0) * (|p.1| ^ m * Real.exp (a * p.1 ^ 2)) := by ring
    _ ≤ (F * C0) * (Cp * Real.exp (beta * p.1 ^ 2)) :=
      mul_le_mul_of_nonneg_left (hpoly p.1) (mul_nonneg hF.le hC0.le)
    _ = _ := by ring

theorem d004671 (n m : ℕ) {phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ}
    (hphi : Continuous phi) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (hν : _root_.GD.N0232.N0720.N1382.d004657 ν)
    {x : _root_.GD.N0232.N0720.N1382.d004651} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) : Integrable (_root_.GD.N0232.N0720.N1382.d004668 n m phi x) ν := by
  obtain ⟨delta, R, hd, hR, hbox⟩ := _root_.GD.N0232.N0720.N1382.d004667 hx
  let beta := (_root_.GD.N0232.N0720.N1382.d004663 delta R + 1 / 2) / 2
  have hb0 : 0 < beta := by dsimp [beta]; linarith [_root_.GD.N0232.N0720.N1382.d004664 hd hR]
  have hb1 : beta < 1 / 2 := by dsimp [beta]; linarith [_root_.GD.N0232.N0720.N1382.d004665 hd (R := R)]
  have hbb : _root_.GD.N0232.N0720.N1382.d004663 delta R < beta := by dsimp [beta]; linarith [_root_.GD.N0232.N0720.N1382.d004665 hd (R := R)]
  obtain ⟨C, _hC, hbound⟩ := _root_.GD.N0232.N0720.N1382.d004670 n m hphi hd hR hbb
  exact ((hν beta hb0 hb1).const_mul C).mono'
    (_root_.GD.N0232.N0720.N1382.d004669 n m hphi hx).aestronglyMeasurable
    (ae_of_all _ (hbound x (mem_of_mem_nhds hbox)))

end

end GD.N0232.N0720.N1382

#print axioms _root_.GD.N0232.N0720.N1382.d004658
#print axioms _root_.GD.N0232.N0720.N1382.d004666
#print axioms _root_.GD.N0232.N0720.N1382.d004671
