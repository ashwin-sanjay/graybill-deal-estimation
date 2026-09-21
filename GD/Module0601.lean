import Mathlib
import GD.Module0424
import GD.Module0425
import GD.Module0597
import GD.Module0598
import GD.Module0600






















open Set

namespace GD.N0113

noncomputable section

open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0135
open _root_.GD.N0115
open _root_.GD.N0115.d006632
open _root_.GD.N0146
open _root_.GD.N0147
open _root_.GD.N0118



structure d008646
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) where
  C₁ : ℚ
  C₂ : ℚ
  Cstar : ℚ
  C₁_nonneg : 0 ≤ C₁
  C₂_nonneg : 0 ≤ C₂
  Cstar_pos : 0 < Cstar
  k : ℕ
  stopping :
    C₁ / _root_.GD.N0134.d006546 k + C₂ / (_root_.GD.N0134.d006546 k) ^ 2 ≤ Cstar / 4

namespace d008646

def d008647
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (H : _root_.GD.N0113.d008646 m n hm hn) :
    _root_.GD.N0146.d008625 m n hm hn :=
  let D := _root_.GD.N0134.d006543 m n hm hn
  { C₁ := H.C₁
    C₂ := H.C₂
    Cstar := H.Cstar
    C₁_nonneg := H.C₁_nonneg
    C₂_nonneg := H.C₂_nonneg
    Cstar_pos := H.Cstar_pos
    k := H.k
    stopping := H.stopping
    branch := _root_.GD.N0146.d008621 D
    branch_eq := rfl
    atoms := _root_.GD.N0146.d008622 D H.k
    atoms_eq := rfl
    atoms_physical := _root_.GD.N0146.d008623 D H.k }

@[simp] theorem d008648
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (H : _root_.GD.N0113.d008646 m n hm hn) :
    H.d008647.atoms =
      _root_.GD.N0146.d008622 (_root_.GD.N0134.d006543 m n hm hn) H.k := rfl

end d008646



def d008649 (D : _root_.GD.N0134.d006518) (k : ℕ) : List (ℚ × ℚ) :=
  (_root_.GD.N0146.d008622 D k).map _root_.GD.N0115.d006635

@[simp] theorem d008650 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    (_root_.GD.N0113.d008649 D k).length = (_root_.GD.N0146.d008622 D k).length := by
  simp [_root_.GD.N0113.d008649]








structure d008651
    (rho : (ℚ × ℚ) → ℝ) (D : _root_.GD.N0134.d006518) (k : ℕ) where
  width : ℚ
  width_pos : 0 < width
  width_le_generated : width ≤ _root_.GD.N0115.d006638 D k
  boxes :
    ∀ i : Fin (_root_.GD.N0146.d008622 D k).length,
      _root_.GD.N0115.d006632 rho
  center_exact :
    ∀ i, (boxes i).center = _root_.GD.N0115.d006635 ((_root_.GD.N0146.d008622 D k).get i)
  width_exact :
    ∀ i, (boxes i).width = width

namespace d008651

def d008652
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k)
    (i : Fin (_root_.GD.N0146.d008622 D k).length) : _root_.GD.N0135.d006593 :=
  (_root_.GD.N0146.d008622 D k).get i

def d008653
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k)
    (i : Fin (_root_.GD.N0146.d008622 D k).length) : ℚ :=
  (T.boxes i).d006633

def d008654
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k)
    (i : Fin (_root_.GD.N0146.d008622 D k).length) : ℚ :=
  _root_.GD.N0115.d006629 (T.boxes i).lower (T.boxes i).upper

theorem d008655
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k)
    (i : Fin (_root_.GD.N0146.d008622 D k).length)
    {p : ℚ × ℚ}
    (hp : _root_.GD.N0115.d006631 (_root_.GD.N0115.d006635 (T.d008652 i)) T.width p) :
    |(T.d008653 i : ℝ) * rho p - 1|
      ≤ (T.d008654 i : ℝ) := by
  apply (T.boxes i).d006634
  rw [T.center_exact i, T.width_exact i]
  exact hp

private theorem d008656
    (D : _root_.GD.N0134.d006518) (k : ℕ)
    (G : _root_.GD.N0115.d006648 D k) :
    G.centers = _root_.GD.N0113.d008649 D k := by
  rw [G.centers_eq]
  unfold _root_.GD.N0113.d008649 _root_.GD.N0146.d008622
  by_cases h : _root_.GD.N0135.d006594 D = 0
  · simp [h, _root_.GD.N0115.d006637]
  · simp [h, _root_.GD.N0115.d006636]







def d008657
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k) :
    _root_.GD.N0146.d008637 := by
  let G : _root_.GD.N0115.d006648 D k :=
    Classical.choice (_root_.GD.N0115.d006649 D k)
  have hcenters : G.centers = _root_.GD.N0113.d008649 D k :=
    _root_.GD.N0113.d008651.d008656 D k G
  have hGw : G.width = _root_.GD.N0115.d006638 D k := G.width_eq
  refine
    { centers := _root_.GD.N0113.d008649 D k
      width := T.width
      width_pos := T.width_pos
      multipliers :=
        List.ofFn (fun i => T.d008653 i)
      multiplier_count := by
        simp [_root_.GD.N0113.d008649]
      all_boxes_physical := ?_
      boxes_pairwise_disjoint := ?_ }
  · intro center hc p hp
    have hcG : center ∈ G.centers := by
      simpa [hcenters] using hc
    have hpG : _root_.GD.N0115.d006631 center G.width p := by
      rw [_root_.GD.N0115.d006631]
      have hw : T.width ≤ G.width := by
        rw [hGw]
        exact T.width_le_generated
      exact ⟨lt_of_lt_of_le hp.1 hw, lt_of_lt_of_le hp.2 hw⟩
    exact G.physical center hcG p hpG
  · intro first hf second hs hne
    rintro ⟨p, hp, hq⟩
    have hfG : first ∈ G.centers := by
      simpa [hcenters] using hf
    have hsG : second ∈ G.centers := by
      simpa [hcenters] using hs
    apply G.pairwise_disjoint first hfG second hsG hne
    refine ⟨p, ?_, ?_⟩
    · rw [_root_.GD.N0115.d006631]
      have hw : T.width ≤ G.width := by
        rw [hGw]
        exact T.width_le_generated
      exact ⟨lt_of_lt_of_le hp.1 hw, lt_of_lt_of_le hp.2 hw⟩
    · rw [_root_.GD.N0115.d006631]
      have hw : T.width ≤ G.width := by
        rw [hGw]
        exact T.width_le_generated
      exact ⟨lt_of_lt_of_le hq.1 hw, lt_of_lt_of_le hq.2 hw⟩

@[simp] theorem d008658
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k) :
    T.d008657.centers = _root_.GD.N0113.d008649 D k := rfl



def d008659
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k) (p : ℝ × ℝ) : ℝ :=
  ∑ i : Fin (_root_.GD.N0146.d008622 D k).length,
    (((T.d008652 i).weight * T.d008653 i : ℚ) : ℝ) *
      _root_.GD.N0118.d008583 ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
        (T.width : ℝ) p

def d008660
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k)
    (i : Fin (_root_.GD.N0146.d008622 D k).length) : Set (ℝ × ℝ) :=
  Icc (((T.d008652 i).ell : ℝ) - T.width)
      (((T.d008652 i).ell : ℝ) + T.width) ×ˢ
    Icc (((T.d008652 i).f : ℝ) - T.width)
      (((T.d008652 i).f : ℝ) + T.width)

def d008661
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k) : Set (ℝ × ℝ) :=
  ⋃ i : Fin (_root_.GD.N0146.d008622 D k).length, T.d008660 i

private theorem d008662
    (c w x : ℝ) (hw : 0 ≤ w)
    (hx : x ∉ Icc (c - w) (c + w)) :
    _root_.GD.N0118.d008582 c w x = 0 := by
  have hxL : x ∉ Ioc (c - w) c := by
    intro h
    exact hx ⟨h.1.le, h.2.trans (by linarith)⟩
  have hxR : x ∉ Ioc c (c + w) := by
    intro h
    exact hx ⟨by linarith [h.1], h.2⟩
  simp [_root_.GD.N0118.d008582, hxL, hxR]

private theorem d008663
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k)
    (i : Fin (_root_.GD.N0146.d008622 D k).length) (p : ℝ × ℝ)
    (hp : p ∉ T.d008660 i) :
    _root_.GD.N0118.d008583 ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
      (T.width : ℝ) p = 0 := by
  rw [_root_.GD.N0113.d008651.d008660, mem_prod] at hp
  have hw : (0 : ℝ) ≤ T.width := by
    exact_mod_cast T.width_pos.le
  by_cases h₁ :
      p.1 ∈ Icc (((T.d008652 i).ell : ℝ) - T.width)
        (((T.d008652 i).ell : ℝ) + T.width)
  · have h₂ :
        p.2 ∉ Icc (((T.d008652 i).f : ℝ) - T.width)
          (((T.d008652 i).f : ℝ) + T.width) := by
      intro hp₂
      exact hp ⟨h₁, hp₂⟩
    simp [_root_.GD.N0118.d008583, _root_.GD.N0113.d008651.d008662 _ _ _ hw h₂]
  · simp [_root_.GD.N0118.d008583, _root_.GD.N0113.d008651.d008662 _ _ _ hw h₁]

theorem d008664
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k) :
    Measurable T.d008659 := by
  unfold _root_.GD.N0113.d008651.d008659
  exact Finset.measurable_fun_sum Finset.univ (fun i _ =>
    (_root_.GD.N0118.d008590
      ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
      (T.width : ℝ)).const_mul _)

theorem d008665
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k) :
    MeasureTheory.Integrable T.d008659
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  unfold _root_.GD.N0113.d008651.d008659
  apply MeasureTheory.integrable_finsetSum
  intro i hi
  exact (_root_.GD.N0118.d008591
    ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
    (T.width : ℝ)).const_mul _

theorem d008666
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k) :
    HasCompactSupport T.d008659 := by
  apply HasCompactSupport.intro
    (K := T.d008661)
  · apply isCompact_iUnion
    intro i
    exact isCompact_Icc.prod isCompact_Icc
  · intro p hp
    unfold _root_.GD.N0113.d008651.d008659
    apply Finset.sum_eq_zero
    intro i hi
    have hnot : p ∉ T.d008660 i := by
      intro hmem
      exact hp (mem_iUnion_of_mem i hmem)
    rw [_root_.GD.N0113.d008651.d008663 T i p hnot, mul_zero]

end d008651



def d008667
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k) : ℚ :=
  ∑ i : Fin (_root_.GD.N0146.d008622 D k).length, |(T.d008652 i).weight|

def d008668
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k)
    (gradientBound : ℚ) : ℚ :=
  T.width * gradientBound * _root_.GD.N0113.d008667 T

def d008669
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k)
    (carrierBound : ℚ) : ℚ :=
  ∑ i : Fin (_root_.GD.N0146.d008622 D k).length,
    |(T.d008652 i).weight| * T.d008654 i * carrierBound

def d008670
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k)
    (inversePower : ℚ) : ℚ :=
  (4 / (9 * T.width ^ 2)) *
    (∑ i : Fin (_root_.GD.N0146.d008622 D k).length,
      (T.d008652 i).weight ^ 2 * T.d008653 i ^ 2 *
        (T.boxes i).upper) *
    inversePower







structure d008671
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (T : _root_.GD.N0113.d008651 rho D k) where
  C : ℚ
  C_pos : 0 < C
  atomicError : ℚ
  atomicError_nonneg : 0 ≤ atomicError
  atomicValue : ℚ
  atomic_upper : atomicValue ≤ -C + atomicError
  atomic_error_budget : atomicError ≤ C / 4
  gradientBound : ℚ
  gradientBound_nonneg : 0 ≤ gradientBound
  carrierBound : ℚ
  carrierBound_nonneg : 0 ≤ carrierBound
  inversePower : ℚ
  inversePower_pos : 0 < inversePower
  smearValue : ℚ
  smear_bound :
    |smearValue| ≤ _root_.GD.N0113.d008668 T gradientBound
  smear_budget :
    _root_.GD.N0113.d008668 T gradientBound ≤ C / 16
  densityValue : ℚ
  density_bound :
    |densityValue| ≤ _root_.GD.N0113.d008669 T carrierBound
  density_budget :
    _root_.GD.N0113.d008669 T carrierBound ≤ C / 16
  energyValue : ℚ
  energy_nonneg : 0 ≤ energyValue
  energy_bound :
    energyValue ≤ _root_.GD.N0113.d008670 T inversePower
  energy_ceiling_pos : 0 < _root_.GD.N0113.d008670 T inversePower

namespace d008671

theorem d008672
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    {T : _root_.GD.N0113.d008651 rho D k}
    (L : _root_.GD.N0113.d008671 T) :
    L.atomicValue ≤ -(3 * L.C / 4) := by
  linarith [L.atomic_upper, L.atomic_error_budget]

theorem d008673
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    {T : _root_.GD.N0113.d008651 rho D k}
    (L : _root_.GD.N0113.d008671 T) :
    |L.smearValue| ≤ L.C / 16 :=
  L.smear_bound.trans L.smear_budget

theorem d008674
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    {T : _root_.GD.N0113.d008651 rho D k}
    (L : _root_.GD.N0113.d008671 T) :
    |L.densityValue| ≤ L.C / 16 :=
  L.density_bound.trans L.density_budget

end d008671



structure d008675 where
  C : ℚ
  atomicError : ℚ
  atomicValue : ℚ
  gradientBound : ℚ
  carrierBound : ℚ
  inversePower : ℚ
  smearValue : ℚ
  densityValue : ℚ
  energyValue : ℚ
deriving DecidableEq, Repr

namespace d008675

def d008676
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (P : _root_.GD.N0113.d008675)
    (T : _root_.GD.N0113.d008651 rho D k) : Prop :=
  0 < P.C
    ∧ 0 ≤ P.atomicError
    ∧ P.atomicValue ≤ -P.C + P.atomicError
    ∧ P.atomicError ≤ P.C / 4
    ∧ 0 ≤ P.gradientBound
    ∧ 0 ≤ P.carrierBound
    ∧ 0 < P.inversePower
    ∧ |P.smearValue| ≤ _root_.GD.N0113.d008668 T P.gradientBound
    ∧ _root_.GD.N0113.d008668 T P.gradientBound ≤ P.C / 16
    ∧ |P.densityValue| ≤ _root_.GD.N0113.d008669 T P.carrierBound
    ∧ _root_.GD.N0113.d008669 T P.carrierBound ≤ P.C / 16
    ∧ 0 ≤ P.energyValue
    ∧ P.energyValue ≤ _root_.GD.N0113.d008670 T P.inversePower
    ∧ 0 < _root_.GD.N0113.d008670 T P.inversePower

instance d008677
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (P : _root_.GD.N0113.d008675)
    (T : _root_.GD.N0113.d008651 rho D k) :
    Decidable (P.d008676 T) := by
  unfold _root_.GD.N0113.d008675.d008676
  infer_instance

def d008678
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (P : _root_.GD.N0113.d008675)
    (T : _root_.GD.N0113.d008651 rho D k) : Bool :=
  decide (P.d008676 T)

theorem d008679
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (P : _root_.GD.N0113.d008675)
    (T : _root_.GD.N0113.d008651 rho D k) :
    P.d008678 T = true ↔ P.d008676 T := by
  simp [_root_.GD.N0113.d008675.d008678]

def d008680
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (P : _root_.GD.N0113.d008675)
    (T : _root_.GD.N0113.d008651 rho D k)
    (h : P.d008676 T) : _root_.GD.N0113.d008671 T := by
  rcases h with
    ⟨hC, hAtomicError, hAtomicUpper, hAtomicBudget,
      hGradient, hCarrier, hPower, hSmear, hSmearBudget,
      hDensity, hDensityBudget, hEnergy, hEnergyBound, hM⟩
  exact
    { C := P.C
      C_pos := hC
      atomicError := P.atomicError
      atomicError_nonneg := hAtomicError
      atomicValue := P.atomicValue
      atomic_upper := hAtomicUpper
      atomic_error_budget := hAtomicBudget
      gradientBound := P.gradientBound
      gradientBound_nonneg := hGradient
      carrierBound := P.carrierBound
      carrierBound_nonneg := hCarrier
      inversePower := P.inversePower
      inversePower_pos := hPower
      smearValue := P.smearValue
      smear_bound := hSmear
      smear_budget := hSmearBudget
      densityValue := P.densityValue
      density_bound := hDensity
      density_budget := hDensityBudget
      energyValue := P.energyValue
      energy_nonneg := hEnergy
      energy_bound := hEnergyBound
      energy_ceiling_pos := hM }

@[simp] theorem d008681
    {rho : (ℚ × ℚ) → ℝ} {D : _root_.GD.N0134.d006518} {k : ℕ}
    (P : _root_.GD.N0113.d008675)
    (T : _root_.GD.N0113.d008651 rho D k)
    (h : P.d008676 T) :
    (P.d008680 T h).C = P.C := by
  rcases h with
    ⟨hC, hAtomicError, hAtomicUpper, hAtomicBudget,
      hGradient, hCarrier, hPower, hSmear, hSmearBudget,
      hDensity, hDensityBudget, hEnergy, hEnergyBound, hM⟩
  rfl

end d008675



structure d008682
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) where
  header : _root_.GD.N0113.d008646 m n hm hn
  rho : (ℚ × ℚ) → ℝ
  table :
    _root_.GD.N0113.d008651 rho (_root_.GD.N0134.d006543 m n hm hn) header.k
  ledger : _root_.GD.N0113.d008671 table
  C_matches_header : ledger.C = header.Cstar

namespace d008682

def d008683
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (R : _root_.GD.N0113.d008682 m n hm hn) :
    _root_.GD.N0146.d008638 m n hm hn := by
  let M : ℚ := _root_.GD.N0113.d008670 R.table R.ledger.inversePower
  refine
    { seed := R.header.d008647
      geometry := R.table.d008657
      centers_match := ?_
      C := R.ledger.C
      M := M
      C_pos := R.ledger.C_pos
      M_pos := R.ledger.energy_ceiling_pos
      atomic := (R.ledger.atomicValue : ℝ)
      smear := (R.ledger.smearValue : ℝ)
      densityError := (R.ledger.densityValue : ℝ)
      energy := (R.ledger.energyValue : ℝ)
      trace :=
        ((R.ledger.atomicValue + R.ledger.smearValue +
          R.ledger.densityValue : ℚ) : ℝ)
      trace_eq := by norm_num
      atomic_margin := ?_
      smearing_bound := ?_
      density_bound := ?_
      energy_nonneg := by exact_mod_cast R.ledger.energy_nonneg
      energy_ceiling := by
        exact_mod_cast R.ledger.energy_bound }
  · rfl
  · exact_mod_cast R.ledger.d008672
  · exact_mod_cast R.ledger.d008673
  · exact_mod_cast R.ledger.d008674

@[simp] theorem d008684
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (R : _root_.GD.N0113.d008682 m n hm hn) :
    R.d008683.d008640 =
      (R.ledger.C / 2) /
        _root_.GD.N0113.d008670 R.table R.ledger.inversePower := rfl







theorem d008685
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (R : _root_.GD.N0113.d008682 m n hm hn) :
    let C := R.d008683
    C.seed.atoms =
        _root_.GD.N0146.d008622 (_root_.GD.N0134.d006543 m n hm hn) R.header.k
      ∧ C.geometry.centers =
        C.seed.atoms.map (fun a => (a.ell, a.f))
      ∧ C.trace ≤ -((R.ledger.C : ℝ) / 2)
      ∧ 0 < C.d008640
      ∧ C.d008640 =
          (R.ledger.C / 2) /
            _root_.GD.N0113.d008670 R.table R.ledger.inversePower
      ∧ 2 * (C.d008640 : ℝ) * C.trace
          + (C.d008640 : ℝ) ^ 2 * C.energy
            ≤ -((((R.ledger.C / 2 : ℚ) : ℝ) ^ 2) /
              (_root_.GD.N0113.d008670 R.table R.ledger.inversePower : ℝ))
      ∧ 2 * (C.d008640 : ℝ) * C.trace
          + (C.d008640 : ℝ) ^ 2 * C.energy < 0 := by
  dsimp
  let C := R.d008683
  have hclose := _root_.GD.N0146.d008645 m n hm hn C
  refine ⟨?_, ?_, ?_, hclose.2.2.2.2.1, ?_,
    hclose.2.2.2.2.2.1, hclose.2.2.2.2.2.2⟩
  · exact hclose.2.1
  · exact C.centers_match
  · simpa [C, _root_.GD.N0113.d008682.d008683] using
      hclose.2.2.2.1
  · rfl

end d008682







structure d008686
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) where
  header : _root_.GD.N0113.d008646 m n hm hn
  rho : (ℚ × ℚ) → ℝ
  table :
    _root_.GD.N0113.d008651 rho (_root_.GD.N0134.d006543 m n hm hn) header.k
  payload : _root_.GD.N0113.d008675
  payload_valid : payload.d008676 table
  C_matches_header : payload.C = header.Cstar

namespace d008686

def d008687
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (R : _root_.GD.N0113.d008686 m n hm hn) :
    _root_.GD.N0113.d008682 m n hm hn :=
  { header := R.header
    rho := R.rho
    table := R.table
    ledger := R.payload.d008680 R.table R.payload_valid
    C_matches_header := by
      simpa using R.C_matches_header }

theorem d008688
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (R : _root_.GD.N0113.d008686 m n hm hn) :
    let C := R.d008687.d008683
    C.trace ≤ -((R.payload.C : ℝ) / 2)
      ∧ 0 < C.d008640
      ∧ 2 * (C.d008640 : ℝ) * C.trace
          + (C.d008640 : ℝ) ^ 2 * C.energy < 0 := by
  let h := R.d008687.d008685
  exact ⟨by simpa [_root_.GD.N0113.d008686.d008687] using h.2.2.1,
    h.2.2.2.1, h.2.2.2.2.2.2⟩

end d008686



theorem d008689
    (c₁ c₂ w : ℝ) (hw : 0 < w) :
    (∫ p, _root_.GD.N0118.d008583 c₁ c₂ w p ∂(MeasureTheory.volume.prod MeasureTheory.volume)) = 1
      ∧
    (∫ p, _root_.GD.N0118.d008583 c₁ c₂ w p ^ 2
        ∂(MeasureTheory.volume.prod MeasureTheory.volume)) =
          4 / (9 * w ^ 2) := by
  exact ⟨_root_.GD.N0118.d008601 c₁ c₂ w hw,
    _root_.GD.N0118.d008602 c₁ c₂ w hw⟩

end

end GD.N0113
