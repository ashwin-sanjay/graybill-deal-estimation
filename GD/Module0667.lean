import GD.Module0307
import GD.Module0666









open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0232.N0719.N0977

open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0719.N0985
open _root_.GD.N0230.N0615

noncomputable section

abbrev d009764 (k : ℕ) := Fin (k + 2) → ℝ
abbrev d009765 (k : ℕ) := EuclideanSpace ℝ (Fin (k + 1))

variable (k : ℕ)

def d009766 : ℝ × (Fin (k + 1) → ℝ) ≃ᵐ ℝ × (Fin (k + 1) → ℝ) where
  toFun p := (p.1, fun i => p.1 + p.2 i)
  invFun p := (p.1, fun i => p.2 i - p.1)
  left_inv p := by ext i <;> simp
  right_inv p := by ext i <;> simp
  measurable_toFun := by
    change Measurable (fun p : ℝ × (Fin (k + 1) → ℝ) => (p.1, fun i => p.1 + p.2 i))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × (Fin (k + 1) → ℝ) => (p.1, fun i => p.2 i - p.1))
    fun_prop

theorem d009767 : MeasurePreserving (_root_.GD.N0232.N0719.N0977.d009766 k) := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (g := fun c (v : Fin (k + 1) → ℝ) => (fun _ => c) + v)
    (by fun_prop)
    (ae_of_all _ fun c => (measurePreserving_add_left volume (fun _ : Fin (k + 1) => c)).map_eq)
  exact h

def d009768 : (ℝ × _root_.GD.N0232.N0719.N0977.d009765 k) ≃ᵐ _root_.GD.N0232.N0719.N0977.d009764 k :=
  ((MeasurableEquiv.refl ℝ).prodCongr
    (MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ)).symm).trans
    ((_root_.GD.N0232.N0719.N0977.d009766 k).trans (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) => ℝ) 0).symm)

theorem d009769 (c : ℝ) (v : _root_.GD.N0232.N0719.N0977.d009765 k) :
    _root_.GD.N0232.N0719.N0977.d009768 k (c, v) = Fin.cons c (fun i => c + v i) := by
  change @Fin.insertNth (k + 1) (fun _ : Fin (k + 2) => ℝ) 0 c (fun i => c + v i) = _
  exact Fin.insertNth_zero' c _

theorem d009770 : MeasurePreserving (_root_.GD.N0232.N0719.N0977.d009768 k) := by
  have hfin := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 2) => ℝ) 0).symm _
  have hprod := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (k + 1)))
  exact hfin.comp ((_root_.GD.N0232.N0719.N0977.d009767 k).comp hprod)

theorem d009771 (f : _root_.GD.N0232.N0719.N0977.d009764 k → ℝ) :
    (∫ z, f z) = ∫ p : ℝ × _root_.GD.N0232.N0719.N0977.d009765 k, f (_root_.GD.N0232.N0719.N0977.d009768 k p) := by
  exact ((_root_.GD.N0232.N0719.N0977.d009770 k).integral_comp
    (_root_.GD.N0232.N0719.N0977.d009768 k).measurableEmbedding f).symm

theorem d009772 (f : _root_.GD.N0232.N0719.N0977.d009764 k → ℝ) :
    Integrable (fun p : ℝ × _root_.GD.N0232.N0719.N0977.d009765 k => f (_root_.GD.N0232.N0719.N0977.d009768 k p)) ↔ Integrable f :=
  (_root_.GD.N0232.N0719.N0977.d009770 k).integrable_comp_emb (_root_.GD.N0232.N0719.N0977.d009768 k).measurableEmbedding

def d009773 (u : _root_.GD.N0232.N0720.N1341.d004415 k) : _root_.GD.N0232.N0719.N0977.d009764 k := Fin.cons 0 (fun i => (u : _root_.GD.N0232.N0719.N0977.d009765 k) i)

def d009774 (shift scale : ℝ) (z : _root_.GD.N0232.N0719.N0977.d009764 k) : _root_.GD.N0232.N0719.N0977.d009764 k := fun i => shift + scale * z i

theorem d009775 (c a : ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 k) :
    _root_.GD.N0232.N0719.N0977.d009768 k (c, a • (u : _root_.GD.N0232.N0719.N0977.d009765 k)) = _root_.GD.N0232.N0719.N0977.d009774 k c a (_root_.GD.N0232.N0719.N0977.d009773 k u) := by
  rw [_root_.GD.N0232.N0719.N0977.d009769]
  funext i
  cases i using Fin.cases <;> simp [_root_.GD.N0232.N0719.N0977.d009774, _root_.GD.N0232.N0719.N0977.d009773]


theorem d009776 (f : _root_.GD.N0232.N0719.N0977.d009764 k → ℝ) (hf : Integrable f) :
    (∫ z, f z) = ∫ u : _root_.GD.N0232.N0720.N1341.d004415 k, (∫ a : ℝ in Ioi 0,
      a ^ k * ∫ c : ℝ, f (_root_.GD.N0232.N0719.N0977.d009768 k (c, a • (u : _root_.GD.N0232.N0719.N0977.d009765 k))))
      ∂_root_.GD.N0232.N0720.N1341.d004416 k := by
  have hchart := (_root_.GD.N0232.N0719.N0977.d009772 k f).mpr hf
  have hG : Integrable (fun v : _root_.GD.N0232.N0719.N0977.d009765 k => ∫ c : ℝ, f (_root_.GD.N0232.N0719.N0977.d009768 k (c, v))) :=
    hchart.integral_prod_right
  rw [_root_.GD.N0232.N0719.N0977.d009771 k f, Measure.volume_eq_prod, integral_prod_symm _ hchart, _root_.GD.N0232.N0720.N1341.d004422]
  rw [integral_prod _ ((_root_.GD.N0232.N0720.N1341.d004423 _).mp hG)]
  apply integral_congr_ae
  exact ae_of_all _ fun u => _root_.GD.N0232.N0720.N1341.d004424 k
    (fun a => ∫ c : ℝ, f (_root_.GD.N0232.N0719.N0977.d009768 k (c, a • (u : _root_.GD.N0232.N0719.N0977.d009765 k))))

def d009777 (tau : _root_.GD.N0232.N0719.N0977.d009764 k) (z : _root_.GD.N0232.N0719.N0977.d009764 k) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, tau i * z i ^ 2

def d009778 (tau : _root_.GD.N0232.N0719.N0977.d009764 k) (u : _root_.GD.N0232.N0720.N1341.d004415 k) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, tau i *
    (_root_.GD.N0232.N0719.N0977.d009773 k u i - _root_.GD.N0230.N0615.d000152 tau (_root_.GD.N0232.N0719.N0977.d009773 k u)) ^ 2

theorem d009779 (tau : _root_.GD.N0232.N0719.N0977.d009764 k) (htau : ∀ i, 0 < tau i) : 0 < _root_.GD.N0230.N0615.d000151 tau := by
  unfold _root_.GD.N0230.N0615.d000151
  exact Finset.sum_pos (fun i _ => htau i) Finset.univ_nonempty

theorem d009780 (tau : _root_.GD.N0232.N0719.N0977.d009764 k) (htau : ∀ i, 0 < tau i) (u : _root_.GD.N0232.N0720.N1341.d004415 k) :
    0 < _root_.GD.N0232.N0719.N0977.d009778 k tau u := by
  have hex : ∃ i, _root_.GD.N0232.N0719.N0977.d009773 k u i - _root_.GD.N0230.N0615.d000152 tau (_root_.GD.N0232.N0719.N0977.d009773 k u) ≠ 0 := by
    by_contra! h
    have hcenter : _root_.GD.N0230.N0615.d000152 tau (_root_.GD.N0232.N0719.N0977.d009773 k u) = 0 := by
      have h0 := h 0
      change 0 - _root_.GD.N0230.N0615.d000152 tau (_root_.GD.N0232.N0719.N0977.d009773 k u) = 0 at h0
      linarith
    have hu : (u : _root_.GD.N0232.N0719.N0977.d009765 k) = 0 := by
      ext i
      have hi := h i.succ
      rw [hcenter] at hi
      simpa [_root_.GD.N0232.N0719.N0977.d009773] using hi
    have hnorm := mem_sphere_zero_iff_norm.mp u.property
    rw [hu, norm_zero] at hnorm
    norm_num at hnorm
  obtain ⟨j, hj⟩ := hex
  unfold _root_.GD.N0232.N0719.N0977.d009778
  apply mul_pos (by norm_num)
  apply Finset.sum_pos'
  · exact fun i _ => mul_nonneg (htau i).le (sq_nonneg _)
  · exact ⟨j, Finset.mem_univ j, mul_pos (htau j) (sq_pos_of_ne_zero hj)⟩

theorem d009781 (tau z : _root_.GD.N0232.N0719.N0977.d009764 k) (a : ℝ) :
    _root_.GD.N0230.N0615.d000152 tau (fun i => a * z i) = a * _root_.GD.N0230.N0615.d000152 tau z := by
  unfold _root_.GD.N0230.N0615.d000152
  rw [show (∑ i, tau i * (a * z i)) = a * ∑ i, tau i * z i by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  ring

theorem d009782 (tau : _root_.GD.N0232.N0719.N0977.d009764 k) (hT : _root_.GD.N0230.N0615.d000151 tau ≠ 0)
    (c a : ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 k) :
    _root_.GD.N0232.N0719.N0977.d009777 k tau (_root_.GD.N0232.N0719.N0977.d009768 k (c, a • (u : _root_.GD.N0232.N0719.N0977.d009765 k))) =
      a ^ 2 * _root_.GD.N0232.N0719.N0977.d009778 k tau u +
        (_root_.GD.N0230.N0615.d000151 tau / 2) * (c + a * _root_.GD.N0230.N0615.d000152 tau (_root_.GD.N0232.N0719.N0977.d009773 k u)) ^ 2 := by
  rw [_root_.GD.N0232.N0719.N0977.d009775]
  have hc := _root_.GD.N0230.N0615.d000158 tau (fun i => a * _root_.GD.N0232.N0719.N0977.d009773 k u i) (-c) hT
  rw [_root_.GD.N0232.N0719.N0977.d009781] at hc
  have hleft : (∑ i, tau i * (a * _root_.GD.N0232.N0719.N0977.d009773 k u i - -c) ^ 2) =
      ∑ i, tau i * (_root_.GD.N0232.N0719.N0977.d009774 k c a (_root_.GD.N0232.N0719.N0977.d009773 k u) i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    unfold _root_.GD.N0232.N0719.N0977.d009774
    ring
  have hright : (∑ i, tau i * (a * _root_.GD.N0232.N0719.N0977.d009773 k u i - a * _root_.GD.N0230.N0615.d000152 tau (_root_.GD.N0232.N0719.N0977.d009773 k u)) ^ 2) =
      a ^ 2 * ∑ i, tau i * (_root_.GD.N0232.N0719.N0977.d009773 k u i - _root_.GD.N0230.N0615.d000152 tau (_root_.GD.N0232.N0719.N0977.d009773 k u)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hleft, hright] at hc
  unfold _root_.GD.N0232.N0719.N0977.d009777 _root_.GD.N0232.N0719.N0977.d009778
  nlinarith

def d009783 (d : _root_.GD.N0232.N0719.N0977.d009764 k → ℝ) : Prop :=
  ∀ (c a : ℝ), 0 < a → ∀ z, d (_root_.GD.N0232.N0719.N0977.d009774 k c a z) = c + a * d z


theorem d009784 (tau : _root_.GD.N0232.N0719.N0977.d009764 k) (hT : 0 < _root_.GD.N0230.N0615.d000151 tau)
    (d : _root_.GD.N0232.N0719.N0977.d009764 k → ℝ) (hd : _root_.GD.N0232.N0719.N0977.d009783 k d) (u : _root_.GD.N0232.N0720.N1341.d004415 k) (c : ℝ)
    {a : ℝ} (ha : 0 < a) :
    d (_root_.GD.N0232.N0719.N0977.d009768 k (c, a • (u : _root_.GD.N0232.N0719.N0977.d009765 k))) ^ 2 *
        Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 k tau (_root_.GD.N0232.N0719.N0977.d009768 k (c, a • (u : _root_.GD.N0232.N0719.N0977.d009765 k)))) =
      Real.exp (-_root_.GD.N0232.N0719.N0977.d009778 k tau u * a ^ 2) *
        ((c + a * d (_root_.GD.N0232.N0719.N0977.d009773 k u)) ^ 2 *
          Real.exp (-((c + a * _root_.GD.N0230.N0615.d000152 tau (_root_.GD.N0232.N0719.N0977.d009773 k u)) ^ 2) /
            (2 * (1 / _root_.GD.N0230.N0615.d000151 tau)))) := by
  rw [_root_.GD.N0232.N0719.N0977.d009782 k tau hT.ne', _root_.GD.N0232.N0719.N0977.d009775, hd c a ha]
  have he : -(a ^ 2 * _root_.GD.N0232.N0719.N0977.d009778 k tau u +
      (_root_.GD.N0230.N0615.d000151 tau / 2) * (c + a * _root_.GD.N0230.N0615.d000152 tau (_root_.GD.N0232.N0719.N0977.d009773 k u)) ^ 2) =
      -_root_.GD.N0232.N0719.N0977.d009778 k tau u * a ^ 2 +
        -((c + a * _root_.GD.N0230.N0615.d000152 tau (_root_.GD.N0232.N0719.N0977.d009773 k u)) ^ 2) /
          (2 * (1 / _root_.GD.N0230.N0615.d000151 tau)) := by
    field_simp [hT.ne']
    ring
  rw [he, Real.exp_add]
  ring



theorem d009785 (tau : _root_.GD.N0232.N0719.N0977.d009764 k) (hT : 0 < _root_.GD.N0230.N0615.d000151 tau)
    (d : _root_.GD.N0232.N0719.N0977.d009764 k → ℝ) (hd : _root_.GD.N0232.N0719.N0977.d009783 k d)
    (hint : Integrable (fun z => d z ^ 2 * Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 k tau z))) :
    (∫ z, d z ^ 2 * Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 k tau z)) =
      ∫ u : _root_.GD.N0232.N0720.N1341.d004415 k, _root_.GD.N0232.N0719.N0985.d009756 ((k : ℝ) + 2) (1 / _root_.GD.N0230.N0615.d000151 tau)
        (_root_.GD.N0232.N0719.N0977.d009778 k tau u) (d (_root_.GD.N0232.N0719.N0977.d009773 k u))
          (_root_.GD.N0230.N0615.d000152 tau (_root_.GD.N0232.N0719.N0977.d009773 k u)) ∂_root_.GD.N0232.N0720.N1341.d004416 k := by
  rw [_root_.GD.N0232.N0719.N0977.d009776 k _ hint]
  apply integral_congr_ae
  apply ae_of_all
  intro u
  unfold _root_.GD.N0232.N0719.N0985.d009756
  apply setIntegral_congr_fun measurableSet_Ioi
  intro a ha
  dsimp only
  have hinner : (∫ c : ℝ, d (_root_.GD.N0232.N0719.N0977.d009768 k (c, a • (u : _root_.GD.N0232.N0719.N0977.d009765 k))) ^ 2 *
      Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 k tau (_root_.GD.N0232.N0719.N0977.d009768 k (c, a • (u : _root_.GD.N0232.N0719.N0977.d009765 k))))) =
      Real.exp (-_root_.GD.N0232.N0719.N0977.d009778 k tau u * a ^ 2) *
        ∫ c : ℝ, (c + a * d (_root_.GD.N0232.N0719.N0977.d009773 k u)) ^ 2 *
          Real.exp (-((c + a * _root_.GD.N0230.N0615.d000152 tau (_root_.GD.N0232.N0719.N0977.d009773 k u)) ^ 2) /
            (2 * (1 / _root_.GD.N0230.N0615.d000151 tau))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun c => _root_.GD.N0232.N0719.N0977.d009784 k tau hT d hd u c ha
  rw [hinner, show (k : ℝ) + 2 - 2 = k by ring, Real.rpow_natCast]
  ring



theorem d009786 (tau : _root_.GD.N0232.N0719.N0977.d009764 k) (htau : ∀ i, 0 < tau i)
    (d : _root_.GD.N0232.N0719.N0977.d009764 k → ℝ) (hd : _root_.GD.N0232.N0719.N0977.d009783 k d)
    (hint : Integrable (fun z => d z ^ 2 * Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 k tau z))) :
    (∫ z, d z ^ 2 * Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 k tau z)) =
      ∫ u : _root_.GD.N0232.N0720.N1341.d004415 k, Real.sqrt (2 * Real.pi * (1 / _root_.GD.N0230.N0615.d000151 tau)) *
        ((1 / _root_.GD.N0230.N0615.d000151 tau) * _root_.GD.N0232.N0719.N0985.d009755 (k : ℝ) (_root_.GD.N0232.N0719.N0977.d009778 k tau u) +
          (d (_root_.GD.N0232.N0719.N0977.d009773 k u) - _root_.GD.N0230.N0615.d000152 tau (_root_.GD.N0232.N0719.N0977.d009773 k u)) ^ 2 *
            _root_.GD.N0232.N0719.N0985.d009755 ((k : ℝ) + 2) (_root_.GD.N0232.N0719.N0977.d009778 k tau u)) ∂_root_.GD.N0232.N0720.N1341.d004416 k := by
  have hT := _root_.GD.N0232.N0719.N0977.d009779 k tau htau
  rw [_root_.GD.N0232.N0719.N0977.d009785 k tau hT d hd hint]
  apply integral_congr_ae
  exact ae_of_all _ fun u => by
    dsimp only
    rw [_root_.GD.N0232.N0719.N0985.d009757 (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith : 1 < (k : ℝ) + 2)
      (by positivity : 0 < 1 / _root_.GD.N0230.N0615.d000151 tau) (_root_.GD.N0232.N0719.N0977.d009780 k tau htau u),
      show (k : ℝ) + 2 - 2 = k by ring]

end

end GD.N0232.N0719.N0977

#print axioms _root_.GD.N0232.N0719.N0977.d009770
#print axioms _root_.GD.N0232.N0719.N0977.d009776
#print axioms _root_.GD.N0232.N0719.N0977.d009782
#print axioms _root_.GD.N0232.N0719.N0977.d009785
#print axioms _root_.GD.N0232.N0719.N0977.d009786
