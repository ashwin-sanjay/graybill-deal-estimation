import GD.Module0755
import GD.Module0664

set_option autoImplicit false
set_option warningAsError true










open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace GD.N0232.N0719.N0994

open _root_.GD.N0232.N0719.N0873 _root_.GD.N0232.N0719.N0989
open _root_.GD.N0232.N0719.N0992
open _root_.GD.N0232.N0719.N0983 (d009709 d009710 d009711 d009712)
open _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1379 (d002889)
open _root_.GD.N0232.N0720.N1382 (d004663 d004664 d004665)

noncomputable section
variable {k : ℕ}

abbrev d011371 (k : ℕ) := ℝ × _root_.GD.N0232.N0719.N0983.d009709 k

def d011372 (p : _root_.GD.N0232.N0719.N0983.d009709 k) (i : Fin k) : ℝ := (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ)

theorem d011373 (p : _root_.GD.N0232.N0719.N0983.d009709 k) (i : Fin k) : 0 ≤ _root_.GD.N0232.N0719.N0994.d011372 p i :=
  (_root_.GD.N0232.N0719.N0983.d009710 i p).property.1

theorem d011374 (p : _root_.GD.N0232.N0719.N0983.d009709 k) : ∑ i, _root_.GD.N0232.N0719.N0994.d011372 p i = 1 := _root_.GD.N0232.N0719.N0983.d009712 p

def d011375 (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) : Prop :=
  ∀ beta : ℝ, 0 < beta → beta < 1 / 2 →
    Integrable (fun p : _root_.GD.N0232.N0719.N0994.d011371 k => Real.exp (beta * p.1 ^ 2)) nu

def d011376 (delta R : ℝ) : Set (_root_.GD.N0232.N0719.N0873.d011295 (Fin k)) :=
  {x | (∀ i, |x.1 i| < R) ∧ ∀ i, delta < x.2 i}

theorem d011377 : IsOpen (_root_.GD.N0232.N0719.N0989.d011338 : Set (_root_.GD.N0232.N0719.N0873.d011295 (Fin k))) := by
  simp only [_root_.GD.N0232.N0719.N0989.d011338, setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const (_root_.GD.N0232.N0719.N0873.d011299 i).continuous

theorem d011378 (delta R : ℝ) : IsOpen (_root_.GD.N0232.N0719.N0994.d011376 (k := k) delta R) := by
  have hleft : IsOpen {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) | ∀ i, |x.1 i| < R} := by
    simp only [setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt (_root_.GD.N0232.N0719.N0873.d011298 i).continuous.abs continuous_const
  have hright : IsOpen {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) | ∀ i, delta < x.2 i} := by
    simp only [setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const (_root_.GD.N0232.N0719.N0873.d011299 i).continuous
  exact hleft.inter hright

private theorem d011379 (s : Finset (Fin k)) (r : Fin k → ℝ)
    (hr : ∀ i ∈ s, 0 < r i) : ∃ delta : ℝ, 0 < delta ∧ ∀ i ∈ s, delta < r i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨delta, hd, hds⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
    let e := min delta (r i) / 2
    have he : 0 < e := div_pos (lt_min_iff.mpr ⟨hd, hr i (Finset.mem_insert_self _ _)⟩) (by norm_num)
    refine ⟨e, he, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · have h := min_le_right delta (r j)
      dsimp [e] at he ⊢
      linarith
    · have h := min_le_left delta (r i)
      have hh := hds j hj
      dsimp [e] at he ⊢
      linarith

theorem d011380 {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) :
    ∃ delta R : ℝ, 0 < delta ∧ 0 < R ∧ _root_.GD.N0232.N0719.N0994.d011376 delta R ∈ 𝓝 x := by
  obtain ⟨delta, hd, hdr⟩ := _root_.GD.N0232.N0719.N0994.d011379 Finset.univ x.2 (fun i _ => hx i)
  let R := 1 + ∑ i, |x.1 i|
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨delta, R, hd, hR, (_root_.GD.N0232.N0719.N0994.d011378 delta R).mem_nhds ?_⟩
  refine ⟨?_, fun i => hdr i (Finset.mem_univ i)⟩
  intro i
  have hle : |x.1 i| ≤ ∑ j, |x.1 j| :=
    Finset.single_le_sum (f := fun j => |x.1 j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  dsimp [R]
  linarith

def d011381 (n m : ℕ) (phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ)
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) (p : _root_.GD.N0232.N0719.N0994.d011371 k) : ℝ :=
  p.1 ^ m * phi p.2 * _root_.GD.N0232.N0719.N0989.d011346 n p.1 (_root_.GD.N0232.N0719.N0994.d011372 p.2) x

theorem d011382 (n m : ℕ) {phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ}
    (hphi : Continuous phi) {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) :
    Continuous (_root_.GD.N0232.N0719.N0994.d011381 n m phi x) := by
  have hc (i : Fin k) : Continuous (fun p : _root_.GD.N0232.N0719.N0994.d011371 k => _root_.GD.N0232.N0719.N0994.d011372 p.2 i) :=
    (continuous_subtype_val.comp (_root_.GD.N0232.N0719.N0983.d009711 i)).comp continuous_snd
  have hA : Continuous (fun p : _root_.GD.N0232.N0719.N0994.d011371 k => _root_.GD.N0232.N0719.N0989.d011339 (_root_.GD.N0232.N0719.N0994.d011372 p.2) x) :=
    continuous_finsetSum _ fun i _ => (hc i).mul continuous_const
  have hB : Continuous (fun p : _root_.GD.N0232.N0719.N0994.d011371 k => _root_.GD.N0232.N0719.N0989.d011340 (_root_.GD.N0232.N0719.N0994.d011372 p.2) x) :=
    continuous_finsetSum _ fun i _ => (hc i).mul continuous_const
  have hG : Continuous (fun p : _root_.GD.N0232.N0719.N0994.d011371 k =>
      _root_.GD.N0232.N0720.N1377.d002852 n (_root_.GD.N0232.N0719.N0989.d011339 (_root_.GD.N0232.N0719.N0994.d011372 p.2) x) (_root_.GD.N0232.N0719.N0989.d011340 (_root_.GD.N0232.N0719.N0994.d011372 p.2) x * p.1)) := by
    apply continuous_iff_continuousAt.2
    intro p
    exact (_root_.GD.N0232.N0720.N1379.d002889 n
      (p := (_root_.GD.N0232.N0719.N0989.d011339 (_root_.GD.N0232.N0719.N0994.d011372 p.2) x, _root_.GD.N0232.N0719.N0989.d011340 (_root_.GD.N0232.N0719.N0994.d011372 p.2) x * p.1))
      (_root_.GD.N0232.N0719.N0989.d011345 _ (_root_.GD.N0232.N0719.N0994.d011373 p.2) (_root_.GD.N0232.N0719.N0994.d011374 p.2) hx)).continuousAt.comp
      (f := fun p : _root_.GD.N0232.N0719.N0994.d011371 k =>
        (_root_.GD.N0232.N0719.N0989.d011339 (_root_.GD.N0232.N0719.N0994.d011372 p.2) x, _root_.GD.N0232.N0719.N0989.d011340 (_root_.GD.N0232.N0719.N0994.d011372 p.2) x * p.1))
      (x := p) (hA.prodMk (hB.mul continuous_fst)).continuousAt
  exact ((continuous_fst.pow m).mul (hphi.comp continuous_snd)).mul hG

theorem d011383 (n m : ℕ) {phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ}
    (hphi : Continuous phi) {delta R beta : ℝ}
    (hd : 0 < delta) (hR : 0 < R) (hbeta : _root_.GD.N0232.N0720.N1382.d004663 delta R < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ _root_.GD.N0232.N0719.N0994.d011376 delta R, ∀ p : _root_.GD.N0232.N0719.N0994.d011371 k,
      ‖_root_.GD.N0232.N0719.N0994.d011381 n m phi x p‖ ≤ C * Real.exp (beta * p.1 ^ 2) := by
  obtain ⟨C0, hC0, hmoment⟩ := _root_.GD.N0232.N0719.N0992.d011370 (I := Fin k) n m hd hR hbeta
  obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn hphi.continuousOn
  let F := max D 1
  have hF : 0 < F := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨F * C0, mul_pos hF hC0, ?_⟩
  intro x hx p
  have hphiBound : ‖phi p.2‖ ≤ F := (hD p.2 (mem_univ _)).trans (le_max_left _ _)
  have hm := hmoment (_root_.GD.N0232.N0719.N0994.d011372 p.2) (_root_.GD.N0232.N0719.N0994.d011373 p.2) (_root_.GD.N0232.N0719.N0994.d011374 p.2) x
    (fun i => (hx.2 i).le) (fun i => (hx.1 i).le) p.1
  calc
    ‖_root_.GD.N0232.N0719.N0994.d011381 n m phi x p‖ =
        ‖phi p.2‖ * ‖p.1 ^ m * _root_.GD.N0232.N0719.N0989.d011346 n p.1 (_root_.GD.N0232.N0719.N0994.d011372 p.2) x‖ := by
      rw [← norm_mul]
      congr 1
      unfold _root_.GD.N0232.N0719.N0994.d011381
      ring
    _ ≤ F * (C0 * Real.exp (beta * p.1 ^ 2)) :=
      mul_le_mul hphiBound hm (norm_nonneg _) hF.le
    _ = _ := by ring

theorem d011384 (n m : ℕ) {phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ}
    (hphi : Continuous phi) (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (hnu : _root_.GD.N0232.N0719.N0994.d011375 nu)
    {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) : Integrable (_root_.GD.N0232.N0719.N0994.d011381 n m phi x) nu := by
  obtain ⟨delta, R, hd, hR, hbox⟩ := _root_.GD.N0232.N0719.N0994.d011380 hx
  let beta := (_root_.GD.N0232.N0720.N1382.d004663 delta R + 1 / 2) / 2
  have hb0 : 0 < beta := by dsimp [beta]; linarith [_root_.GD.N0232.N0720.N1382.d004664 hd hR]
  have hb1 : beta < 1 / 2 := by dsimp [beta]; linarith [_root_.GD.N0232.N0720.N1382.d004665 hd (R := R)]
  have hbb : _root_.GD.N0232.N0720.N1382.d004663 delta R < beta := by dsimp [beta]; linarith [_root_.GD.N0232.N0720.N1382.d004665 hd (R := R)]
  obtain ⟨C, _, hbound⟩ := _root_.GD.N0232.N0719.N0994.d011383 n m hphi hd hR hbb
  exact ((hnu beta hb0 hb1).const_mul C).mono'
    (_root_.GD.N0232.N0719.N0994.d011382 n m hphi hx).aestronglyMeasurable
    (ae_of_all _ (hbound x (mem_of_mem_nhds hbox)))

end
end GD.N0232.N0719.N0994

#print axioms _root_.GD.N0232.N0719.N0994.d011384
