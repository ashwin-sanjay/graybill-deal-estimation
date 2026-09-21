import GD.Module0313
import Mathlib.Analysis.Calculus.ParametricIntegral










open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace GD.N0232.N0720.N1386

open _root_.GD.N0232.N0720.N1373 _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1379 _root_.GD.N0232.N0720.N1382
open _root_.GD.N0232.N0720.N1376

noncomputable section

def d004697 (i : Fin 4) : _root_.GD.N0232.N0720.N1382.d004651 →L[ℝ] ℝ := ContinuousLinearMap.proj i

def d004698 (phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ) (t : _root_.GD.N0232.N0720.N1373.d004628) : ℝ := phi t * (1 - t.1)
def d004699 (phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ) (t : _root_.GD.N0232.N0720.N1373.d004628) : ℝ := phi t * t.1

theorem d004700 {phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ} (hphi : Continuous phi) :
    Continuous (_root_.GD.N0232.N0720.N1386.d004698 phi) := hphi.mul (by fun_prop)
theorem d004701 {phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ} (hphi : Continuous phi) :
    Continuous (_root_.GD.N0232.N0720.N1386.d004699 phi) := hphi.mul continuous_subtype_val

def d004702 (x : _root_.GD.N0232.N0720.N1382.d004651) : _root_.GD.N0232.N0720.N1382.d004651 →L[ℝ] ℝ := (-x 0) • _root_.GD.N0232.N0720.N1386.d004697 0 - _root_.GD.N0232.N0720.N1386.d004697 2
def d004703 (x : _root_.GD.N0232.N0720.N1382.d004651) : _root_.GD.N0232.N0720.N1382.d004651 →L[ℝ] ℝ := (-x 1) • _root_.GD.N0232.N0720.N1386.d004697 1 - _root_.GD.N0232.N0720.N1386.d004697 3

def d004704 (n m : ℕ) (phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ) (x : _root_.GD.N0232.N0720.N1382.d004651) (p : _root_.GD.N0232.N0720.N1373.d004629) :
    _root_.GD.N0232.N0720.N1382.d004651 →L[ℝ] ℝ :=
  _root_.GD.N0232.N0720.N1382.d004668 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004698 phi) x p • _root_.GD.N0232.N0720.N1386.d004702 x +
  _root_.GD.N0232.N0720.N1382.d004668 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004699 phi) x p • _root_.GD.N0232.N0720.N1386.d004703 x +
  _root_.GD.N0232.N0720.N1382.d004668 (n + 1) (m + 1) (_root_.GD.N0232.N0720.N1386.d004698 phi) x p • _root_.GD.N0232.N0720.N1386.d004697 0 +
  _root_.GD.N0232.N0720.N1382.d004668 (n + 1) (m + 1) (_root_.GD.N0232.N0720.N1386.d004699 phi) x p • _root_.GD.N0232.N0720.N1386.d004697 1

def d004705 (n m : ℕ) (phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ)
    (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1382.d004651) : ℝ := ∫ p, _root_.GD.N0232.N0720.N1382.d004668 n m phi x p ∂ν

def d004706 (n m : ℕ) (phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ)
    (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1382.d004651) : _root_.GD.N0232.N0720.N1382.d004651 →L[ℝ] ℝ :=
  _root_.GD.N0232.N0720.N1386.d004705 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004698 phi) ν x • _root_.GD.N0232.N0720.N1386.d004702 x +
  _root_.GD.N0232.N0720.N1386.d004705 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004699 phi) ν x • _root_.GD.N0232.N0720.N1386.d004703 x +
  _root_.GD.N0232.N0720.N1386.d004705 (n + 1) (m + 1) (_root_.GD.N0232.N0720.N1386.d004698 phi) ν x • _root_.GD.N0232.N0720.N1386.d004697 0 +
  _root_.GD.N0232.N0720.N1386.d004705 (n + 1) (m + 1) (_root_.GD.N0232.N0720.N1386.d004699 phi) ν x • _root_.GD.N0232.N0720.N1386.d004697 1

theorem d004707 (n m : ℕ) (phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ)
    {x : _root_.GD.N0232.N0720.N1382.d004651} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) (p : _root_.GD.N0232.N0720.N1373.d004629) :
    HasFDerivAt (fun y ↦ _root_.GD.N0232.N0720.N1382.d004668 n m phi y p) (_root_.GD.N0232.N0720.N1386.d004704 n m phi x p) x := by
  let A' : _root_.GD.N0232.N0720.N1382.d004651 →L[ℝ] ℝ :=
    (2 * (1 - p.2.1) * x 0) • _root_.GD.N0232.N0720.N1386.d004697 0 +
    (2 * p.2.1 * x 1) • _root_.GD.N0232.N0720.N1386.d004697 1 +
    (2 * (1 - p.2.1)) • _root_.GD.N0232.N0720.N1386.d004697 2 + (2 * p.2.1) • _root_.GD.N0232.N0720.N1386.d004697 3
  let b' : _root_.GD.N0232.N0720.N1382.d004651 →L[ℝ] ℝ :=
    (p.1 * (1 - p.2.1)) • _root_.GD.N0232.N0720.N1386.d004697 0 + (p.1 * p.2.1) • _root_.GD.N0232.N0720.N1386.d004697 1
  have hA : HasFDerivAt (fun y ↦ _root_.GD.N0232.N0720.N1382.d004654 y p.2) A' x := by
    apply (((((hasFDerivAt_apply (0 : Fin 4) x).pow 2).fun_add
      ((hasFDerivAt_apply (2 : Fin 4) x).const_mul 2)).const_mul (1 - p.2.1)).fun_add
      ((((hasFDerivAt_apply (1 : Fin 4) x).pow 2).fun_add
        ((hasFDerivAt_apply (3 : Fin 4) x).const_mul 2)).const_mul p.2.1)).congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    simp [A', _root_.GD.N0232.N0720.N1386.d004697, smul_eq_mul] <;> ring
  have hb : HasFDerivAt (fun y ↦ _root_.GD.N0232.N0720.N1382.d004655 y p.2 * p.1) b' x := by
    apply ((((hasFDerivAt_apply (0 : Fin 4) x).const_mul (1 - p.2.1)).fun_add
      ((hasFDerivAt_apply (1 : Fin 4) x).const_mul p.2.1)).mul_const p.1).congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    simp [b', _root_.GD.N0232.N0720.N1386.d004697, smul_eq_mul] <;> ring
  apply (((_root_.GD.N0232.N0720.N1379.d002889 n
    (p := (_root_.GD.N0232.N0720.N1382.d004654 x p.2, _root_.GD.N0232.N0720.N1382.d004655 x p.2 * p.1)) (_root_.GD.N0232.N0720.N1382.d004656 hx p.2)).comp x
    (hA.prodMk hb)).const_mul (p.1 ^ m * phi p.2)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [_root_.GD.N0232.N0720.N1386.d004704, _root_.GD.N0232.N0720.N1382.d004668, _root_.GD.N0232.N0720.N1386.d004698, _root_.GD.N0232.N0720.N1386.d004699, _root_.GD.N0232.N0720.N1386.d004702,
    _root_.GD.N0232.N0720.N1386.d004703, _root_.GD.N0232.N0720.N1386.d004697, _root_.GD.N0232.N0720.N1379.d002883,
    A', b', pow_succ, smul_eq_mul] <;> ring

theorem d004708 (n m : ℕ) {phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ}
    (hphi : Continuous phi) {x : _root_.GD.N0232.N0720.N1382.d004651} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) :
    Continuous (_root_.GD.N0232.N0720.N1386.d004704 n m phi x) := by
  unfold _root_.GD.N0232.N0720.N1386.d004704
  exact ((((_root_.GD.N0232.N0720.N1382.d004669 _ _ (_root_.GD.N0232.N0720.N1386.d004700 hphi) hx).smul continuous_const).add
    ((_root_.GD.N0232.N0720.N1382.d004669 _ _ (_root_.GD.N0232.N0720.N1386.d004701 hphi) hx).smul continuous_const)).add
    ((_root_.GD.N0232.N0720.N1382.d004669 _ _ (_root_.GD.N0232.N0720.N1386.d004700 hphi) hx).smul continuous_const)).add
    ((_root_.GD.N0232.N0720.N1382.d004669 _ _ (_root_.GD.N0232.N0720.N1386.d004701 hphi) hx).smul continuous_const)

theorem d004709 (n m : ℕ) {phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ}
    (hphi : Continuous phi) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (hν : _root_.GD.N0232.N0720.N1382.d004657 ν)
    {x : _root_.GD.N0232.N0720.N1382.d004651} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) :
    (∫ p, _root_.GD.N0232.N0720.N1386.d004704 n m phi x p ∂ν) = _root_.GD.N0232.N0720.N1386.d004706 n m phi ν x := by
  have h0 := (_root_.GD.N0232.N0720.N1382.d004671 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004700 hphi) ν hν hx).smul_const
    (_root_.GD.N0232.N0720.N1386.d004702 x)
  have h1 := (_root_.GD.N0232.N0720.N1382.d004671 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004701 hphi) ν hν hx).smul_const
    (_root_.GD.N0232.N0720.N1386.d004703 x)
  have h2 := (_root_.GD.N0232.N0720.N1382.d004671 (n + 1) (m + 1) (_root_.GD.N0232.N0720.N1386.d004700 hphi) ν hν hx).smul_const
    (_root_.GD.N0232.N0720.N1386.d004697 0)
  have h3 := (_root_.GD.N0232.N0720.N1382.d004671 (n + 1) (m + 1) (_root_.GD.N0232.N0720.N1386.d004701 hphi) ν hν hx).smul_const
    (_root_.GD.N0232.N0720.N1386.d004697 1)
  unfold _root_.GD.N0232.N0720.N1386.d004704 _root_.GD.N0232.N0720.N1386.d004706
  rw [integral_add
      (f := fun p ↦ _root_.GD.N0232.N0720.N1382.d004668 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004698 phi) x p • _root_.GD.N0232.N0720.N1386.d004702 x +
        _root_.GD.N0232.N0720.N1382.d004668 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004699 phi) x p • _root_.GD.N0232.N0720.N1386.d004703 x +
        _root_.GD.N0232.N0720.N1382.d004668 (n + 1) (m + 1) (_root_.GD.N0232.N0720.N1386.d004698 phi) x p • _root_.GD.N0232.N0720.N1386.d004697 0)
      (g := fun p ↦ _root_.GD.N0232.N0720.N1382.d004668 (n + 1) (m + 1) (_root_.GD.N0232.N0720.N1386.d004699 phi) x p • _root_.GD.N0232.N0720.N1386.d004697 1)
      ((h0.add h1).add h2) h3,
    integral_add
      (f := fun p ↦ _root_.GD.N0232.N0720.N1382.d004668 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004698 phi) x p • _root_.GD.N0232.N0720.N1386.d004702 x +
        _root_.GD.N0232.N0720.N1382.d004668 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004699 phi) x p • _root_.GD.N0232.N0720.N1386.d004703 x)
      (g := fun p ↦ _root_.GD.N0232.N0720.N1382.d004668 (n + 1) (m + 1) (_root_.GD.N0232.N0720.N1386.d004698 phi) x p • _root_.GD.N0232.N0720.N1386.d004697 0)
      (h0.add h1) h2,
    integral_add
      (f := fun p ↦ _root_.GD.N0232.N0720.N1382.d004668 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004698 phi) x p • _root_.GD.N0232.N0720.N1386.d004702 x)
      (g := fun p ↦ _root_.GD.N0232.N0720.N1382.d004668 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004699 phi) x p • _root_.GD.N0232.N0720.N1386.d004703 x)
      h0 h1, integral_smul_const, integral_smul_const,
    integral_smul_const, integral_smul_const]
  rfl

private theorem d004710 (a b c d : _root_.GD.N0232.N0720.N1382.d004651 →L[ℝ] ℝ) :
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  linarith [norm_add_le (a + b + c) d, norm_add_le (a + b) c, norm_add_le a b]

theorem d004711 (n m : ℕ) {phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ}
    (hphi : Continuous phi) {delta R beta : ℝ} (hd : 0 < delta) (hR : 0 < R)
    (hbeta : _root_.GD.N0232.N0720.N1382.d004663 delta R < beta) :
    ∃ C : ℝ, ∀ x ∈ _root_.GD.N0232.N0720.N1382.d004659 delta R, ∀ p : _root_.GD.N0232.N0720.N1373.d004629,
      ‖_root_.GD.N0232.N0720.N1386.d004704 n m phi x p‖ ≤ C * Real.exp (beta * p.1 ^ 2) := by
  obtain ⟨C0, hC0, hb0⟩ := _root_.GD.N0232.N0720.N1382.d004670 (n + 2) m
    (_root_.GD.N0232.N0720.N1386.d004700 hphi) hd hR hbeta
  obtain ⟨C1, hC1, hb1⟩ := _root_.GD.N0232.N0720.N1382.d004670 (n + 2) m
    (_root_.GD.N0232.N0720.N1386.d004701 hphi) hd hR hbeta
  obtain ⟨C2, hC2, hb2⟩ := _root_.GD.N0232.N0720.N1382.d004670 (n + 1) (m + 1)
    (_root_.GD.N0232.N0720.N1386.d004700 hphi) hd hR hbeta
  obtain ⟨C3, hC3, hb3⟩ := _root_.GD.N0232.N0720.N1382.d004670 (n + 1) (m + 1)
    (_root_.GD.N0232.N0720.N1386.d004701 hphi) hd hR hbeta
  refine ⟨C0 * (R * ‖_root_.GD.N0232.N0720.N1386.d004697 0‖ + ‖_root_.GD.N0232.N0720.N1386.d004697 2‖) +
    C1 * (R * ‖_root_.GD.N0232.N0720.N1386.d004697 1‖ + ‖_root_.GD.N0232.N0720.N1386.d004697 3‖) + C2 * ‖_root_.GD.N0232.N0720.N1386.d004697 0‖ + C3 * ‖_root_.GD.N0232.N0720.N1386.d004697 1‖, ?_⟩
  intro x hx p
  have hleft : ‖_root_.GD.N0232.N0720.N1386.d004702 x‖ ≤ R * ‖_root_.GD.N0232.N0720.N1386.d004697 0‖ + ‖_root_.GD.N0232.N0720.N1386.d004697 2‖ := by
    unfold _root_.GD.N0232.N0720.N1386.d004702
    apply (norm_sub_le _ _).trans
    rw [norm_smul, norm_neg, Real.norm_eq_abs]
    exact add_le_add
      (mul_le_mul_of_nonneg_right hx.1.le (norm_nonneg (_root_.GD.N0232.N0720.N1386.d004697 0))) le_rfl
  have hright : ‖_root_.GD.N0232.N0720.N1386.d004703 x‖ ≤ R * ‖_root_.GD.N0232.N0720.N1386.d004697 1‖ + ‖_root_.GD.N0232.N0720.N1386.d004697 3‖ := by
    unfold _root_.GD.N0232.N0720.N1386.d004703
    apply (norm_sub_le _ _).trans
    rw [norm_smul, norm_neg, Real.norm_eq_abs]
    exact add_le_add
      (mul_le_mul_of_nonneg_right hx.2.1.le (norm_nonneg (_root_.GD.N0232.N0720.N1386.d004697 1))) le_rfl
  have h0 := mul_le_mul (hb0 x hx p) hleft (norm_nonneg _) (by positivity)
  have h1 := mul_le_mul (hb1 x hx p) hright (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul_of_nonneg_right (hb2 x hx p) (norm_nonneg (_root_.GD.N0232.N0720.N1386.d004697 0))
  have h3 := mul_le_mul_of_nonneg_right (hb3 x hx p) (norm_nonneg (_root_.GD.N0232.N0720.N1386.d004697 1))
  have htriangle := _root_.GD.N0232.N0720.N1386.d004710
    (_root_.GD.N0232.N0720.N1382.d004668 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004698 phi) x p • _root_.GD.N0232.N0720.N1386.d004702 x)
    (_root_.GD.N0232.N0720.N1382.d004668 (n + 2) m (_root_.GD.N0232.N0720.N1386.d004699 phi) x p • _root_.GD.N0232.N0720.N1386.d004703 x)
    (_root_.GD.N0232.N0720.N1382.d004668 (n + 1) (m + 1) (_root_.GD.N0232.N0720.N1386.d004698 phi) x p • _root_.GD.N0232.N0720.N1386.d004697 0)
    (_root_.GD.N0232.N0720.N1382.d004668 (n + 1) (m + 1) (_root_.GD.N0232.N0720.N1386.d004699 phi) x p • _root_.GD.N0232.N0720.N1386.d004697 1)
  simp only [norm_smul] at htriangle
  exact htriangle.trans (by nlinarith)

theorem d004712 (n m : ℕ) {phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ}
    (hphi : Continuous phi) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (hν : _root_.GD.N0232.N0720.N1382.d004657 ν)
    {x : _root_.GD.N0232.N0720.N1382.d004651} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) :
    HasFDerivAt (_root_.GD.N0232.N0720.N1386.d004705 n m phi ν) (_root_.GD.N0232.N0720.N1386.d004706 n m phi ν x) x := by
  obtain ⟨delta, R, hd, hR, hbox⟩ := _root_.GD.N0232.N0720.N1382.d004667 hx
  let beta := (_root_.GD.N0232.N0720.N1382.d004663 delta R + 1 / 2) / 2
  have hb0 : 0 < beta := by dsimp [beta]; linarith [_root_.GD.N0232.N0720.N1382.d004664 hd hR]
  have hb1 : beta < 1 / 2 := by dsimp [beta]; linarith [_root_.GD.N0232.N0720.N1382.d004665 hd (R := R)]
  have hbb : _root_.GD.N0232.N0720.N1382.d004663 delta R < beta := by dsimp [beta]; linarith [_root_.GD.N0232.N0720.N1382.d004665 hd (R := R)]
  obtain ⟨C, hbound⟩ := _root_.GD.N0232.N0720.N1386.d004711 n m hphi hd hR hbb
  have hsub : _root_.GD.N0232.N0720.N1382.d004659 delta R ⊆ _root_.GD.N0232.N0720.N1382.d004652 :=
    fun y hy ↦ ⟨hd.trans hy.2.2.1, hd.trans hy.2.2.2⟩
  have hmeas : ∀ᶠ y : _root_.GD.N0232.N0720.N1382.d004651 in 𝓝 x, AEStronglyMeasurable (_root_.GD.N0232.N0720.N1382.d004668 n m phi y) ν := by
    filter_upwards [_root_.GD.N0232.N0720.N1382.d004653.mem_nhds hx] with y hy
    exact (_root_.GD.N0232.N0720.N1382.d004669 n m hphi hy).aestronglyMeasurable
  have hint : Integrable (_root_.GD.N0232.N0720.N1382.d004668 n m phi x) ν :=
    _root_.GD.N0232.N0720.N1382.d004671 n m hphi ν hν hx
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (H := _root_.GD.N0232.N0720.N1382.d004651) (E := ℝ) (α := _root_.GD.N0232.N0720.N1373.d004629) (x₀ := x)
    (F := _root_.GD.N0232.N0720.N1382.d004668 n m phi) (F' := _root_.GD.N0232.N0720.N1386.d004704 n m phi) (μ := ν)
    (s := _root_.GD.N0232.N0720.N1382.d004659 delta R) (bound := fun p : _root_.GD.N0232.N0720.N1373.d004629 ↦ C * Real.exp (beta * p.1 ^ 2))
    hbox hmeas hint
    (_root_.GD.N0232.N0720.N1386.d004708 n m hphi hx).aestronglyMeasurable
    (ae_of_all _ fun p y hy ↦ hbound y hy p)
    ((hν beta hb0 hb1).const_mul C)
    (ae_of_all _ fun p y hy ↦ _root_.GD.N0232.N0720.N1386.d004707 n m phi (hsub hy) p)
  rw [_root_.GD.N0232.N0720.N1386.d004709 n m hphi ν hν hx] at hderiv
  exact hderiv

theorem d004713 (n m : ℕ) {phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ}
    (hphi : Continuous phi) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (hν : _root_.GD.N0232.N0720.N1382.d004657 ν) :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1386.d004705 n m phi ν) _root_.GD.N0232.N0720.N1382.d004652 := by
  have hall : ∀ k : ℕ, ∀ n m : ℕ, ∀ phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ, Continuous phi →
      ContDiffOn ℝ k (_root_.GD.N0232.N0720.N1386.d004705 n m phi ν) _root_.GD.N0232.N0720.N1382.d004652 := by
    intro k
    induction k with
    | zero =>
        intro n m phi hphi
        change ContDiffOn ℝ 0 (_root_.GD.N0232.N0720.N1386.d004705 n m phi ν) _root_.GD.N0232.N0720.N1382.d004652
        rw [contDiffOn_zero]
        intro x hx
        exact (_root_.GD.N0232.N0720.N1386.d004712 n m hphi ν hν hx).continuousAt.continuousWithinAt
    | succ k ih =>
        intro n m phi hphi
        rw [Nat.cast_add, Nat.cast_one]
        apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn _root_.GD.N0232.N0720.N1382.d004653.uniqueDiffOn).2
        refine ⟨by simp, _root_.GD.N0232.N0720.N1386.d004706 n m phi ν, ?_, ?_⟩
        · unfold _root_.GD.N0232.N0720.N1386.d004706
          have hl : ContDiffOn ℝ k _root_.GD.N0232.N0720.N1386.d004702 _root_.GD.N0232.N0720.N1382.d004652 := by unfold _root_.GD.N0232.N0720.N1386.d004702; fun_prop
          have hr : ContDiffOn ℝ k _root_.GD.N0232.N0720.N1386.d004703 _root_.GD.N0232.N0720.N1382.d004652 := by unfold _root_.GD.N0232.N0720.N1386.d004703; fun_prop
          exact ((((ih _ _ _ (_root_.GD.N0232.N0720.N1386.d004700 hphi)).smul hl).add
            ((ih _ _ _ (_root_.GD.N0232.N0720.N1386.d004701 hphi)).smul hr)).add
            ((ih _ _ _ (_root_.GD.N0232.N0720.N1386.d004700 hphi)).smul contDiffOn_const)).add
            ((ih _ _ _ (_root_.GD.N0232.N0720.N1386.d004701 hphi)).smul contDiffOn_const)
        · intro x hx
          exact (_root_.GD.N0232.N0720.N1386.d004712 n m hphi ν hν hx).hasFDerivWithinAt
  exact contDiffOn_infty.mpr fun k ↦ hall k n m phi hphi

end

end GD.N0232.N0720.N1386

#print axioms _root_.GD.N0232.N0720.N1386.d004712
#print axioms _root_.GD.N0232.N0720.N1386.d004713
