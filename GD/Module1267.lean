import GD.Module0667
import GD.Module1220
import GD.Module0664
import GD.Module1262
import GD.Module1223
import GD.Module0634
import GD.Module0026

set_option autoImplicit false
set_option warningAsError true































open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0210.N0457

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0977 _root_.GD.N0232.N0719.N0983
open _root_.GD.N0232.N0719.N0986 _root_.GD.N0232.N0719.N0997
open _root_.GD.N0232.N0720.N1341

noncomputable section

variable {d : ℕ}



theorem d020464 (c a b : ℝ) (v : _root_.GD.N0232.N0719.N0977.d009765 d) :
    _root_.GD.N0232.N0719.N0977.d009774 d c a (_root_.GD.N0232.N0719.N0977.d009768 d (b, v)) = _root_.GD.N0232.N0719.N0977.d009768 d (c + a * b, a • v) := by
  rw [_root_.GD.N0232.N0719.N0977.d009769, _root_.GD.N0232.N0719.N0977.d009769]
  funext i
  cases i using Fin.cases <;> simp [_root_.GD.N0232.N0719.N0977.d009774]
  ring


theorem d020465 (P : _root_.GD.N0232.N0719.N0977.d009764 d → Prop) :
    (∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d)), P z) ↔
      ∀ᵐ p ∂(volume : Measure (ℝ × _root_.GD.N0232.N0719.N0977.d009765 d)), P (_root_.GD.N0232.N0719.N0977.d009768 d p) := by
  rw [← (_root_.GD.N0232.N0719.N0977.d009770 d).map_eq]
  exact (_root_.GD.N0232.N0719.N0977.d009768 d).measurableEmbedding.ae_map_iff

theorem d020466 (P : _root_.GD.N0232.N0719.N0977.d009764 d → Prop)
    (hinv : ∀ c a : ℝ, 0 < a → ∀ z, P z → P (_root_.GD.N0232.N0719.N0977.d009774 d c a z))
    (hv : ∀ᵐ v ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)), P (_root_.GD.N0232.N0719.N0977.d009768 d (0, v))) :
    ∀ᵐ p ∂(volume : Measure (ℝ × _root_.GD.N0232.N0719.N0977.d009765 d)), P (_root_.GD.N0232.N0719.N0977.d009768 d p) := by
  rw [Measure.volume_eq_prod]
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hv] with p hp
  have h := hinv p.1 1 one_pos _ hp
  rwa [_root_.GD.N0210.N0457.d020464, mul_zero, add_zero, one_smul] at h

theorem d020467 (P : _root_.GD.N0232.N0719.N0977.d009764 d → Prop)
    (hinv : ∀ c a : ℝ, 0 < a → ∀ z, P z → P (_root_.GD.N0232.N0719.N0977.d009774 d c a z))
    (hsphere : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, P (_root_.GD.N0232.N0719.N0977.d009773 d u)) :
    ∀ᵐ v ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)), P (_root_.GD.N0232.N0719.N0977.d009768 d (0, v)) := by
  have hfst : ∀ᵐ p : _root_.GD.N0232.N0720.N1341.d004415 d × Ioi (0 : ℝ)
      ∂(_root_.GD.N0232.N0720.N1341.d004416 d).prod (Measure.volumeIoiPow d), P (_root_.GD.N0232.N0719.N0977.d009773 d p.1) :=
    Measure.quasiMeasurePreserving_fst.ae hsphere
  have hprod : ∀ᵐ p : _root_.GD.N0232.N0720.N1341.d004415 d × Ioi (0 : ℝ)
      ∂(_root_.GD.N0232.N0720.N1341.d004416 d).prod (Measure.volumeIoiPow d),
      P (_root_.GD.N0232.N0719.N0977.d009768 d (0, ((homeomorphUnitSphereProd (_root_.GD.N0232.N0719.N0977.d009765 d)).symm p : _root_.GD.N0232.N0719.N0977.d009765 d))) := by
    filter_upwards [hfst] with p hp
    rw [homeomorphUnitSphereProd_symm_apply_coe, _root_.GD.N0232.N0719.N0977.d009775]
    exact hinv 0 p.2.1 p.2.2 _ hp
  have hpolar := (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)).measurePreserving_homeomorphUnitSphereProd
  have hsub : ∀ᵐ x : ({0}ᶜ : Set (_root_.GD.N0232.N0719.N0977.d009765 d)) ∂volume.comap Subtype.val,
      P (_root_.GD.N0232.N0719.N0977.d009768 d (0, (x : _root_.GD.N0232.N0719.N0977.d009765 d))) := by
    have hp := hpolar.quasiMeasurePreserving.ae (by
      simpa only [finrank_euclideanSpace_fin, Nat.add_sub_cancel, _root_.GD.N0232.N0720.N1341.d004416] using hprod)
    simpa only [Homeomorph.symm_apply_apply] using hp
  have hr : ∀ᵐ v ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)).restrict ({0}ᶜ : Set (_root_.GD.N0232.N0719.N0977.d009765 d)),
      P (_root_.GD.N0232.N0719.N0977.d009768 d (0, v)) :=
    (ae_restrict_iff_subtype (μ := (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)))
      (p := fun v : _root_.GD.N0232.N0719.N0977.d009765 d => P (_root_.GD.N0232.N0719.N0977.d009768 d (0, v)))
      (measurableSet_singleton (0 : _root_.GD.N0232.N0719.N0977.d009765 d)).compl).2 hsub
  simpa only [restrict_compl_singleton] using hr



theorem d020468 (P : _root_.GD.N0232.N0719.N0977.d009764 d → Prop)
    (hinv : ∀ c a : ℝ, 0 < a → ∀ z, P z → P (_root_.GD.N0232.N0719.N0977.d009774 d c a z))
    (hsphere : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, P (_root_.GD.N0232.N0719.N0977.d009773 d u)) :
    ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d)), P z :=
  (_root_.GD.N0210.N0457.d020465 P).2
    (_root_.GD.N0210.N0457.d020466 P hinv (_root_.GD.N0210.N0457.d020467 P hinv hsphere))


theorem d020469 (F G : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ) (hF : _root_.GD.N0232.N0719.N0977.d009783 d F) (hG : _root_.GD.N0232.N0719.N0977.d009783 d G)
    (h : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, F (_root_.GD.N0232.N0719.N0977.d009773 d u) = G (_root_.GD.N0232.N0719.N0977.d009773 d u)) :
    F =ᵐ[(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d))] G := by
  apply _root_.GD.N0210.N0457.d020468 (fun z => F z = G z) _ h
  intro c a ha z hz
  rw [hF c a ha, hG c a ha, hz]



section Simplex
variable {k : ℕ}

theorem d020470 (c a : ℝ) (y : Fin k → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    _root_.GD.N0232.N0719.N0983.d009713 (fun i => c + a * y i) p = c + a * _root_.GD.N0232.N0719.N0983.d009713 y p := by
  unfold _root_.GD.N0232.N0719.N0983.d009713
  have h1 : (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * (c + a * y i)) =
      c * ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) + a * ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * y i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h1, _root_.GD.N0232.N0719.N0983.d009712, mul_one]

theorem d020471 (c a : ℝ) (y r : Fin k → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    _root_.GD.N0232.N0719.N0983.d009714 (fun i => c + a * y i) (fun i => a ^ 2 * r i) p = a ^ 2 * _root_.GD.N0232.N0719.N0983.d009714 y r p := by
  have h1 : (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * (a ^ 2 * r i)) =
      a ^ 2 * ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * r i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * (c + a * y i - (c + a * _root_.GD.N0232.N0719.N0983.d009713 y p)) ^ 2) =
      a ^ 2 * ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * (y i - _root_.GD.N0232.N0719.N0983.d009713 y p) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold _root_.GD.N0232.N0719.N0983.d009714
  rw [_root_.GD.N0210.N0457.d020470, h1, h2]
  ring

theorem d020472 (q c a : ℝ) (ha : 0 < a) (y r : Fin k → ℝ) (hr : ∀ i, 0 ≤ r i)
    (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    _root_.GD.N0232.N0719.N0983.d009720 q (fun i => c + a * y i) (fun i => a ^ 2 * r i) p =
      (a ^ 2) ^ (-q) * _root_.GD.N0232.N0719.N0983.d009720 q y r p := by
  unfold _root_.GD.N0232.N0719.N0983.d009720
  rw [_root_.GD.N0210.N0457.d020471, Real.mul_rpow (by positivity) (_root_.GD.N0232.N0719.N0983.d009717 y r hr p)]

theorem d020473 (q c a : ℝ) (ha : 0 < a) (y r : Fin k → ℝ) (hr : ∀ i, 0 ≤ r i)
    (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) :
    _root_.GD.N0232.N0719.N0983.d009723 q (fun i => c + a * y i) (fun i => a ^ 2 * r i) μ =
      (a ^ 2) ^ (-q) * _root_.GD.N0232.N0719.N0983.d009723 q y r μ := by
  unfold _root_.GD.N0232.N0719.N0983.d009723
  simp_rw [_root_.GD.N0210.N0457.d020472 q c a ha y r hr]
  exact integral_const_mul _ _


theorem d020474 (q c a : ℝ) (ha : 0 < a) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure μ] :
    _root_.GD.N0232.N0719.N0983.d009724 q (fun i => c + a * y i) (fun i => a ^ 2 * r i) μ =
      c + a * _root_.GD.N0232.N0719.N0983.d009724 q y r μ := by
  have hr0 : ∀ i, 0 ≤ r i := fun i => (hr i).le
  have hM := _root_.GD.N0232.N0719.N0983.d009728 q y r hr μ
  have hs : 0 < (a ^ 2) ^ (-q) := Real.rpow_pos_of_pos (by positivity) _
  have hK := _root_.GD.N0232.N0719.N0983.d009726 q y r hr μ
  have hB : Integrable (fun p => _root_.GD.N0232.N0719.N0983.d009713 y p * _root_.GD.N0232.N0719.N0983.d009720 q y r p) μ :=
    ((_root_.GD.N0232.N0719.N0983.d009715 y).mul (_root_.GD.N0232.N0719.N0983.d009721 q y r hr)).integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  have hnum : (∫ p, _root_.GD.N0232.N0719.N0983.d009713 (fun i => c + a * y i) p *
      _root_.GD.N0232.N0719.N0983.d009720 q (fun i => c + a * y i) (fun i => a ^ 2 * r i) p ∂μ) =
      (a ^ 2) ^ (-q) * (c * _root_.GD.N0232.N0719.N0983.d009723 q y r μ + a * ∫ p, _root_.GD.N0232.N0719.N0983.d009713 y p * _root_.GD.N0232.N0719.N0983.d009720 q y r p ∂μ) := by
    have h1 : ∀ p : _root_.GD.N0232.N0719.N0983.d009709 k, _root_.GD.N0232.N0719.N0983.d009713 (fun i => c + a * y i) p *
        _root_.GD.N0232.N0719.N0983.d009720 q (fun i => c + a * y i) (fun i => a ^ 2 * r i) p =
        (a ^ 2) ^ (-q) * (c * _root_.GD.N0232.N0719.N0983.d009720 q y r p + a * (_root_.GD.N0232.N0719.N0983.d009713 y p * _root_.GD.N0232.N0719.N0983.d009720 q y r p)) := by
      intro p
      rw [_root_.GD.N0210.N0457.d020470, _root_.GD.N0210.N0457.d020472 q c a ha y r hr0]
      ring
    simp_rw [h1]
    have hadd : (∫ p, (c * _root_.GD.N0232.N0719.N0983.d009720 q y r p + a * (_root_.GD.N0232.N0719.N0983.d009713 y p * _root_.GD.N0232.N0719.N0983.d009720 q y r p)) ∂μ) =
        (∫ p, c * _root_.GD.N0232.N0719.N0983.d009720 q y r p ∂μ) + ∫ p, a * (_root_.GD.N0232.N0719.N0983.d009713 y p * _root_.GD.N0232.N0719.N0983.d009720 q y r p) ∂μ :=
      integral_add (hK.const_mul c) (hB.const_mul a)
    rw [integral_const_mul, hadd, integral_const_mul, integral_const_mul, _root_.GD.N0232.N0719.N0983.d009723]
  unfold _root_.GD.N0232.N0719.N0983.d009724
  rw [hnum, _root_.GD.N0210.N0457.d020473 q c a ha y r hr0, mul_div_mul_left _ _ hs.ne', add_div,
    mul_div_cancel_right₀ c hM.ne', mul_div_assoc]

end Simplex



section Grouped
variable {k : ℕ} (sizes : Fin k → ℕ)


def d020475 (c a : ℝ) (z : _root_.GD.N0232.N0719.N0997.d019804 sizes) : _root_.GD.N0232.N0719.N0997.d019804 sizes :=
  fun i j => c + a * z i j

theorem d020476 (hn : ∀ i, 0 < sizes i) (c a : ℝ) (z : _root_.GD.N0232.N0719.N0997.d019804 sizes) (i : Fin k) :
    _root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0210.N0457.d020475 sizes c a z) i = c + a * _root_.GD.N0232.N0719.N0986.d020360 sizes z i := by
  have hpos : (0 : ℝ) < sizes i := by exact_mod_cast hn i
  have hsum : (∑ j, (c + a * z i j)) = (sizes i : ℝ) * c + a * ∑ j, z i j := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.mul_sum]
  unfold _root_.GD.N0232.N0719.N0986.d020360 _root_.GD.N0210.N0457.d020475
  rw [hsum, add_div, mul_div_cancel_left₀ c hpos.ne', mul_div_assoc]

theorem d020477 (hn : ∀ i, 0 < sizes i) (c a : ℝ) (z : _root_.GD.N0232.N0719.N0997.d019804 sizes) :
    _root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0210.N0457.d020475 sizes c a z) = fun i => c + a * _root_.GD.N0232.N0719.N0986.d020360 sizes z i := by
  funext i
  exact _root_.GD.N0210.N0457.d020476 sizes hn c a z i

theorem d020478 (hn : ∀ i, 0 < sizes i) (c a : ℝ) (z : _root_.GD.N0232.N0719.N0997.d019804 sizes)
    (i : Fin k) :
    _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0210.N0457.d020475 sizes c a z) i = a ^ 2 * _root_.GD.N0232.N0719.N0986.d020361 sizes z i := by
  have hsum : (∑ j, (c + a * z i j - (c + a * _root_.GD.N0232.N0719.N0986.d020360 sizes z i)) ^ 2) =
      a ^ 2 * ∑ j, (z i j - _root_.GD.N0232.N0719.N0986.d020360 sizes z i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold _root_.GD.N0232.N0719.N0986.d020361
  rw [_root_.GD.N0210.N0457.d020476 sizes hn]
  unfold _root_.GD.N0210.N0457.d020475
  rw [hsum, mul_div_assoc]

theorem d020479 (hn : ∀ i, 0 < sizes i) (c a : ℝ) (z : _root_.GD.N0232.N0719.N0997.d019804 sizes) :
    _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0210.N0457.d020475 sizes c a z) = fun i => a ^ 2 * _root_.GD.N0232.N0719.N0986.d020361 sizes z i := by
  funext i
  exact _root_.GD.N0210.N0457.d020478 sizes hn c a z i


def d020480 (s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ) : Prop :=
  ∀ c a : ℝ, 0 < a → ∀ z, s (_root_.GD.N0210.N0457.d020475 sizes c a z) = c + a * s z



theorem d020481 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229)
        (omega : _root_.GD.N0232.N0719.N0997.d019804 sizes) => g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) => g • y) s) :
    _root_.GD.N0210.N0457.d020480 sizes s := by
  intro c a ha z
  let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨c, Real.log a⟩
  have hinput : g • z = _root_.GD.N0210.N0457.d020475 sizes c a z := by
    funext i j
    change c + Real.exp (Real.log a) * _ = c + a * _
    rw [Real.exp_log ha]
  have he : s (g • z) = g • s z := hs g z
  rw [hinput] at he
  simpa only [_root_.GD.N0232.N0719.N0946.d009229.d009244, g,
    _root_.GD.N0232.N0719.N0946.d009229.d009239, Real.exp_log ha] using he


theorem d020482 (hn : ∀ i, 0 < sizes i) (q c a : ℝ) (ha : 0 < a)
    (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure μ]
    (z : _root_.GD.N0232.N0719.N0997.d019804 sizes) (hr : ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes z i) :
    _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0210.N0457.d020475 sizes c a z))
      (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0210.N0457.d020475 sizes c a z)) μ =
      c + a * _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes z) (_root_.GD.N0232.N0719.N0986.d020361 sizes z) μ := by
  rw [_root_.GD.N0210.N0457.d020477 sizes hn, _root_.GD.N0210.N0457.d020479 sizes hn]
  exact _root_.GD.N0210.N0457.d020474 q c a ha _ _ hr μ

variable {d : ℕ} (hdim : (∑ i, sizes i) = d + 2)



def d020483 (z : _root_.GD.N0232.N0719.N0977.d009764 d) : _root_.GD.N0232.N0719.N0997.d019804 sizes :=
  fun i j => z (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i, j⟩)

theorem d020484 (z : _root_.GD.N0232.N0719.N0977.d009764 d) :
    _root_.GD.N0210.N0457.d020483 sizes hdim z = (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm (WithLp.toLp 2 z) := rfl

theorem d020485 (c a : ℝ) (z : _root_.GD.N0232.N0719.N0977.d009764 d) :
    _root_.GD.N0210.N0457.d020483 sizes hdim (_root_.GD.N0232.N0719.N0977.d009774 d c a z) = _root_.GD.N0210.N0457.d020475 sizes c a (_root_.GD.N0210.N0457.d020483 sizes hdim z) := rfl

def d020486 : _root_.GD.N0232.N0719.N0977.d009764 d ≃ᵐ _root_.GD.N0232.N0719.N0997.d019804 sizes :=
  (MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).trans (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm

theorem d020487 (z : _root_.GD.N0232.N0719.N0977.d009764 d) : _root_.GD.N0210.N0457.d020486 sizes hdim z = _root_.GD.N0210.N0457.d020483 sizes hdim z := rfl

theorem d020488 : MeasurePreserving (_root_.GD.N0210.N0457.d020486 sizes hdim) := by
  have htoLp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)) volume volume :=
    ⟨(MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).measurable,
      (PiLp.volume_preserving_toLp (Fin (d + 2))).map_eq⟩
  have h := (MeasurePreserving.symm (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim) (_root_.GD.N0232.N0719.N0997.d019809 sizes hdim)).comp
    htoLp
  simpa only [_root_.GD.N0210.N0457.d020486, MeasurableEquiv.coe_trans] using h

theorem d020489 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : _root_.GD.N0232.N0719.N0977.d009783 d (s ∘ _root_.GD.N0210.N0457.d020483 sizes hdim)) : _root_.GD.N0210.N0457.d020480 sizes s := by
  intro c a ha z
  have hw : _root_.GD.N0210.N0457.d020483 sizes hdim ((_root_.GD.N0210.N0457.d020486 sizes hdim).symm z) = z :=
    (_root_.GD.N0210.N0457.d020486 sizes hdim).apply_symm_apply z
  have h := hs c a ha ((_root_.GD.N0210.N0457.d020486 sizes hdim).symm z)
  simpa only [Function.comp_apply, _root_.GD.N0210.N0457.d020485, hw] using h

theorem d020490 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : _root_.GD.N0210.N0457.d020480 sizes s) : _root_.GD.N0232.N0719.N0977.d009783 d (s ∘ _root_.GD.N0210.N0457.d020483 sizes hdim) :=
  fun c a ha z => hs c a ha (_root_.GD.N0210.N0457.d020483 sizes hdim z)



theorem d020491 (P : _root_.GD.N0232.N0719.N0997.d019804 sizes → Prop)
    (hinv : ∀ c a : ℝ, 0 < a → ∀ z, P z → P (_root_.GD.N0210.N0457.d020475 sizes c a z))
    (hsphere : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, P (_root_.GD.N0210.N0457.d020483 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u))) :
    ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)), P z := by
  have h := _root_.GD.N0210.N0457.d020468 (fun w => P (_root_.GD.N0210.N0457.d020483 sizes hdim w))
    (fun c a ha w hw => hinv c a ha _ hw) hsphere
  rw [← (_root_.GD.N0210.N0457.d020488 sizes hdim).map_eq]
  exact (_root_.GD.N0210.N0457.d020486 sizes hdim).measurableEmbedding.ae_map_iff.2 h






theorem d020492 (hn : ∀ i, 0 < sizes i) (q : ℝ)
    (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure μ]
    (s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ) (hs : _root_.GD.N0210.N0457.d020480 sizes s)
    (hres : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)), ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes z i)
    (hsphere : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      s (_root_.GD.N0210.N0457.d020483 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)) =
        _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0210.N0457.d020483 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
          (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0210.N0457.d020483 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u))) μ) :
    ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)),
      s z = _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes z) (_root_.GD.N0232.N0719.N0986.d020361 sizes z) μ := by
  have hP := _root_.GD.N0210.N0457.d020491 sizes hdim
    (fun z => (∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes z i) →
      s z = _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes z) (_root_.GD.N0232.N0719.N0986.d020361 sizes z) μ)
    (by
      intro c a ha z hz hr'
      have hr : ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes z i := by
        intro i
        have h := hr' i
        rw [_root_.GD.N0210.N0457.d020478 sizes hn] at h
        exact (pos_iff_pos_of_mul_pos h).mp (by positivity)
      rw [hs c a ha z, hz hr, _root_.GD.N0210.N0457.d020482 sizes hn q c a ha μ z hr])
    (by
      filter_upwards [hsphere] with u hu
      intro _
      exact hu)
  filter_upwards [hP, hres] with z hz hr
  exact hz hr


theorem d020493 (hn : ∀ i, 0 < sizes i) (q : ℝ)
    (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure μ]
    (s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ) (hs : _root_.GD.N0210.N0457.d020480 sizes s)
    (hres : ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)), ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes z i)
    (hsphere : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      s (_root_.GD.N0210.N0457.d020483 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)) =
        _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes (_root_.GD.N0210.N0457.d020483 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)))
          (_root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0210.N0457.d020483 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u))) μ) :
    ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0997.d019804 sizes)),
      s z = _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020362 sizes z).1 (_root_.GD.N0232.N0719.N0986.d020362 sizes z).2 μ :=
  _root_.GD.N0210.N0457.d020492 sizes hdim hn q μ s hs hres hsphere

end Grouped

end
end GD.N0210.N0457

#print axioms _root_.GD.N0210.N0457.d020468
#print axioms _root_.GD.N0210.N0457.d020469
#print axioms _root_.GD.N0210.N0457.d020474
#print axioms _root_.GD.N0210.N0457.d020481
#print axioms _root_.GD.N0210.N0457.d020491
#print axioms _root_.GD.N0210.N0457.d020492
#print axioms _root_.GD.N0210.N0457.d020493
