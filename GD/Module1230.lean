import GD.Module1225
import GD.Module1226












open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0720.N1330

open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1329 _root_.GD.N0232.N0720.N1314
open _root_.GD.N0232.N0720.N1315 _root_.GD.N0232.N0720.N1326
open _root_.GD.N0232.N0720.N1342 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1377 _root_.GD.N0107
open _root_.GD.N0238.N0753
open _root_.GD.N0230.N0556

noncomputable section

variable {k : ℕ}

private theorem d020025 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β}
    (hf : Measure.QuasiMeasurePreserving f μ ν) {p : β → Prop}
    (hp : ∀ᵐ y ∂ν, p y) : ∀ᵐ x ∂μ, p (f x) :=
  hf.ae hp



theorem d020026
    (f : ℕ → (_root_.GD.N0232.N0720.N1341.d004414 k) → ℝ) (hf : ∀ n, _root_.GD.N0238.N0753.d004397 (f n))
    (h : (_root_.GD.N0232.N0720.N1341.d004415 k) → ℝ)
    (hlim : ∀ᵐ (u : (_root_.GD.N0232.N0720.N1341.d004415 k)) ∂(_root_.GD.N0232.N0720.N1341.d004416 k),
      Tendsto (fun n ↦ f n u) atTop (𝓝 (h u))) :
    ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)),
      Tendsto (fun n ↦ f n x) atTop (𝓝 (_root_.GD.N0232.N0720.N1341.d004418 h x)) := by
  have hfst : ∀ᵐ (p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ)) ∂(_root_.GD.N0232.N0720.N1341.d004416 k).prod (Measure.volumeIoiPow k),
      Tendsto (fun n ↦ f n (p.1 : (_root_.GD.N0232.N0720.N1341.d004414 k))) atTop (𝓝 (h p.1)) :=
    _root_.GD.N0232.N0720.N1330.d020025 (Measure.quasiMeasurePreserving_fst
      (μ := (_root_.GD.N0232.N0720.N1341.d004416 k)) (ν := Measure.volumeIoiPow k)) hlim
  have hprod : ∀ᵐ p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ) ∂(_root_.GD.N0232.N0720.N1341.d004416 k).prod (Measure.volumeIoiPow k),
      Tendsto (fun n ↦ f n (((homeomorphUnitSphereProd (_root_.GD.N0232.N0720.N1341.d004414 k)).symm p).1))
        atTop (𝓝 (_root_.GD.N0232.N0720.N1341.d004418 h (((homeomorphUnitSphereProd (_root_.GD.N0232.N0720.N1341.d004414 k)).symm p).1))) := by
    filter_upwards [hfst] with p hp
    simp only [homeomorphUnitSphereProd_symm_apply_coe, _root_.GD.N0232.N0720.N1341.d004421]
    have heq : (fun n ↦ f n (p.2.1 • (p.1 : (_root_.GD.N0232.N0720.N1341.d004414 k)))) =
        (fun n ↦ p.2.1 * f n p.1) := by
      funext n
      simpa only [smul_eq_mul] using hf n p.2.1 p.2.2 (p.1 : (_root_.GD.N0232.N0720.N1341.d004414 k))
    rw [heq]
    exact tendsto_const_nhds.mul hp
  have hpolar := (volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)).measurePreserving_homeomorphUnitSphereProd
  have hsub : ∀ᵐ x : ({0}ᶜ : Set (_root_.GD.N0232.N0720.N1341.d004414 k)) ∂volume.comap Subtype.val,
      Tendsto (fun n ↦ f n x.1) atTop (𝓝 (_root_.GD.N0232.N0720.N1341.d004418 h x.1)) := by
    have hp := _root_.GD.N0232.N0720.N1330.d020025 hpolar.quasiMeasurePreserving (by
      simpa only [finrank_euclideanSpace_fin, Nat.add_sub_cancel, _root_.GD.N0232.N0720.N1341.d004416] using hprod)
    simpa only [Homeomorph.symm_apply_apply] using hp
  have hr : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)).restrict ({0}ᶜ : Set (_root_.GD.N0232.N0720.N1341.d004414 k)),
      Tendsto (fun n ↦ f n x) atTop (𝓝 (_root_.GD.N0232.N0720.N1341.d004418 h x)) :=
    (ae_restrict_iff_subtype (μ := (volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)))
      (p := fun x : (_root_.GD.N0232.N0720.N1341.d004414 k) ↦
        Tendsto (fun n ↦ f n x) atTop (𝓝 (_root_.GD.N0232.N0720.N1341.d004418 h x)))
      (measurableSet_singleton (0 : (_root_.GD.N0232.N0720.N1341.d004414 k))).compl).2 hsub
  simpa only [restrict_compl_singleton] using hr

theorem d020027 (q : _root_.GD.N0232.N0720.N1316.d004440 k) (x : _root_.GD.N0232.N0720.N1341.d004414 k) (c : ℝ) :
    _root_.GD.N0232.N0720.N1316.d004441 q (c • x) = c ^ 2 * _root_.GD.N0232.N0720.N1316.d004441 q x := by
  unfold _root_.GD.N0232.N0720.N1316.d004441
  simp only [PiLp.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d020028 (q : _root_.GD.N0232.N0720.N1316.d004440 k) (x : _root_.GD.N0232.N0720.N1341.d004414 k) (c : ℝ) :
    _root_.GD.N0232.N0720.N1316.d004442 q (c • x) = c * _root_.GD.N0232.N0720.N1316.d004442 q x := by
  unfold _root_.GD.N0232.N0720.N1316.d004442
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d020029 (j : ℕ) (q : _root_.GD.N0232.N0720.N1316.d004440 k) (x : _root_.GD.N0232.N0720.N1341.d004414 k)
    {c : ℝ} (hc : 0 < c) :
    _root_.GD.N0232.N0720.N1377.d002852 j (_root_.GD.N0232.N0720.N1316.d004441 q (c • x)) (_root_.GD.N0232.N0720.N1316.d004442 q (c • x)) =
      (c ^ (j + 1))⁻¹ * _root_.GD.N0232.N0720.N1377.d002852 j (_root_.GD.N0232.N0720.N1316.d004441 q x) (_root_.GD.N0232.N0720.N1316.d004442 q x) := by
  rw [_root_.GD.N0232.N0720.N1330.d020027, _root_.GD.N0232.N0720.N1330.d020028, _root_.GD.N0232.N0720.N1377.d002866 j _ _ hc]

section Finite

variable {I : Type*} [Fintype I]

def d020030 (q : I → _root_.GD.N0232.N0720.N1316.d004440 k) (w : I → ℝ) (x : _root_.GD.N0232.N0720.N1341.d004414 k) : ℝ :=
  ∑ i, w i * _root_.GD.N0232.N0720.N1316.d004444 (q i) *
    _root_.GD.N0232.N0720.N1377.d002852 (k + 2) (_root_.GD.N0232.N0720.N1316.d004441 (q i) x) (_root_.GD.N0232.N0720.N1316.d004442 (q i) x)

def d020031 (q : I → _root_.GD.N0232.N0720.N1316.d004440 k) (w : I → ℝ) (x : _root_.GD.N0232.N0720.N1341.d004414 k) : ℝ :=
  ∑ i, w i * _root_.GD.N0232.N0720.N1316.d004444 (q i) * (q i).1 *
    _root_.GD.N0232.N0720.N1377.d002852 (k + 1) (_root_.GD.N0232.N0720.N1316.d004441 (q i) x) (_root_.GD.N0232.N0720.N1316.d004442 (q i) x)

def d020032 (q : I → _root_.GD.N0232.N0720.N1316.d004440 k) (w : I → ℝ) (x : _root_.GD.N0232.N0720.N1341.d004414 k) : ℝ :=
  _root_.GD.N0232.N0720.N1330.d020031 q w x / _root_.GD.N0232.N0720.N1330.d020030 q w x

theorem d020033 (q : I → _root_.GD.N0232.N0720.N1316.d004440 k) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 k) :
    _root_.GD.N0232.N0720.N1330.d020032 q w u = _root_.GD.N0232.N0720.N1314.d019699 q w u / _root_.GD.N0232.N0720.N1314.d019698 q w u := by
  rw [_root_.GD.N0232.N0720.N1314.d019703, _root_.GD.N0232.N0720.N1314.d019702]
  rfl

theorem d020034 (q : I → _root_.GD.N0232.N0720.N1316.d004440 k) (w : I → ℝ)
    (x : _root_.GD.N0232.N0720.N1341.d004414 k) {c : ℝ} (hc : 0 < c) :
    _root_.GD.N0232.N0720.N1330.d020030 q w (c • x) = (c ^ (k + 3))⁻¹ * _root_.GD.N0232.N0720.N1330.d020030 q w x := by
  unfold _root_.GD.N0232.N0720.N1330.d020030
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0232.N0720.N1330.d020029 _ _ _ hc]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  ring

theorem d020035 (q : I → _root_.GD.N0232.N0720.N1316.d004440 k) (w : I → ℝ)
    (x : _root_.GD.N0232.N0720.N1341.d004414 k) {c : ℝ} (hc : 0 < c) :
    _root_.GD.N0232.N0720.N1330.d020031 q w (c • x) = (c ^ (k + 2))⁻¹ * _root_.GD.N0232.N0720.N1330.d020031 q w x := by
  unfold _root_.GD.N0232.N0720.N1330.d020031
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0232.N0720.N1330.d020029 _ _ _ hc]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  ring

theorem d020036 (q : I → _root_.GD.N0232.N0720.N1316.d004440 k) (w : I → ℝ) :
    _root_.GD.N0238.N0753.d004397 (_root_.GD.N0232.N0720.N1330.d020032 q w) := by
  intro c hc x
  have hpower : c ^ (k + 3) = c ^ (k + 2) * c := by
    rw [show k + 3 = (k + 2) + 1 by omega, pow_succ]
  have hfactor : (c ^ (k + 2))⁻¹ = (c ^ (k + 3))⁻¹ * c := by
    rw [hpower]
    field_simp [hc.ne']
  unfold _root_.GD.N0232.N0720.N1330.d020032
  rw [_root_.GD.N0232.N0720.N1330.d020035 _ _ _ hc, _root_.GD.N0232.N0720.N1330.d020034 _ _ _ hc, hfactor, mul_assoc,
    mul_div_mul_left _ _ (inv_ne_zero (pow_ne_zero (k + 3) hc.ne'))]
  simp only [smul_eq_mul, mul_div_assoc]

variable {m n : ℕ} (hdim : m + n = k + 1) (hm : 0 < m) (hn : 0 < n)

def d020037 (ν : Measure _root_.GD.N0232.N0720.N1315.d019832) (x : _root_.GD.N0232.N0720.N1341.d004414 k) : ℝ :=
  (∫ p, _root_.GD.N0232.N0720.N1315.d019849 k p (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) ∂ν) /
    (∫ p, _root_.GD.N0232.N0720.N1315.d019848 k p (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) ∂ν)



theorem d020038 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) (x : _root_.GD.N0232.N0720.N1341.d004414 k) :
    _root_.GD.N0232.N0720.N1330.d020037 hdim (_root_.GD.N0232.N0720.N1315.d019873 hdim hm hn q w hw hp : Measure _root_.GD.N0232.N0720.N1315.d019832) x =
      _root_.GD.N0232.N0720.N1330.d020032 (fun i ↦ _root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q i)) w x := by
  have hK : _root_.GD.N0232.N0720.N1330.d020030 (fun i ↦ _root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q i)) w x =
      ∑ i, _root_.GD.N0232.N0720.N1315.d019866 hdim q w i *
        _root_.GD.N0232.N0720.N1315.d019848 k (_root_.GD.N0232.N0720.N1315.d019847 m n hm hn (q i)) (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) := by
    unfold _root_.GD.N0232.N0720.N1330.d020030
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc, _root_.GD.N0232.N0720.N1315.d019864 hdim hm hn]
    unfold _root_.GD.N0232.N0720.N1315.d019866
    ring
  have hL : _root_.GD.N0232.N0720.N1330.d020031 (fun i ↦ _root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q i)) w x =
      ∑ i, _root_.GD.N0232.N0720.N1315.d019866 hdim q w i *
        _root_.GD.N0232.N0720.N1315.d019849 k (_root_.GD.N0232.N0720.N1315.d019847 m n hm hn (q i)) (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) := by
    unfold _root_.GD.N0232.N0720.N1330.d020031
    apply Finset.sum_congr rfl
    intro i _
    change w i * _root_.GD.N0232.N0720.N1316.d004444 (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q i)) * (q i).1 *
      _root_.GD.N0232.N0720.N1377.d002852 (k + 1) (_root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q i)) x)
        (_root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q i)) x) = _
    rw [show w i * _root_.GD.N0232.N0720.N1316.d004444 (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q i)) * (q i).1 *
        _root_.GD.N0232.N0720.N1377.d002852 (k + 1) (_root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q i)) x)
          (_root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q i)) x) =
      w i * (_root_.GD.N0232.N0720.N1316.d004444 (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q i)) * (q i).1 *
        _root_.GD.N0232.N0720.N1377.d002852 (k + 1) (_root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q i)) x)
          (_root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q i)) x)) by ring]
    rw [_root_.GD.N0232.N0720.N1315.d019865 hdim hm hn]
    unfold _root_.GD.N0232.N0720.N1315.d019866
    ring
  unfold _root_.GD.N0232.N0720.N1330.d020037 _root_.GD.N0232.N0720.N1330.d020032
  rw [_root_.GD.N0232.N0720.N1315.d019875, _root_.GD.N0232.N0720.N1315.d019875, hK, hL]
  exact mul_div_mul_left _ _ (inv_ne_zero (_root_.GD.N0232.N0720.N1315.d019869 hdim hm hn q w hw hp).ne')

end Finite

section RawTerminal

variable (m n k : ℕ) (hdim : m + n = k + 1)

theorem d020039 {g : ℝ × ℝ → ℝ}
    (hg : ∀ p, g p ∈ Icc (0 : ℝ) 1) (x : _root_.GD.N0232.N0720.N1341.d004414 k) :
    _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g x ∈
      Icc (min (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 0) (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 1))
        (max (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 0) (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 1)) := by
  simpa only [_root_.GD.N0232.N0720.N1329.d019671, _root_.GD.N0232.N0720.N1315.d019850, Matrix.cons_val_zero,
    Matrix.cons_val_one] using _root_.GD.N0232.N0720.N1342.d019643 m n hg
      ((_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm x)

theorem d020040 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {δ : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n δ) :
    ∃ (g : ℝ × ℝ → ℝ) (h : _root_.GD.N0232.N0720.N1341.d004417 k), Measurable g ∧
      (∀ p, g p ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        δ =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ]
          _root_.GD.N0232.N0720.N1425.d014719 m n g) ∧
      _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1314.d019711 m n k hdim) h ∧
      _root_.GD.N0232.N0720.N1341.d004418 h =ᵐ[(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k))]
        _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g := by
  obtain ⟨g, hg, hb, hae⟩ := _root_.GD.N0232.N0720.N1342.d019642 m n hm hn hd
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  let f := _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g
  have hf : Measurable f := _root_.GD.N0232.N0720.N1329.d019672 m n k hdim hg
  have hhom : _root_.GD.N0238.N0753.d004397 f :=
    _root_.GD.N0232.N0720.N1329.d019675 m n k hdim hm0 hn0 g
  have hbound : ∀ u : _root_.GD.N0232.N0720.N1341.d004415 k, ‖f u‖ ≤ 1 :=
    _root_.GD.N0232.N0720.N1329.d019679 m n k hdim hm0 hn0 hb
  have hrep : ∀ θ : _root_.GD.N0232.N0720.N1326.d019882,
      f ∘ _root_.GD.N0232.N0720.N1329.d019648 m n k hdim =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] δ := by
    intro θ
    simpa only [Function.comp_def, f, _root_.GD.N0232.N0720.N1329.d019673] using (hae θ).symm
  refine ⟨g, _root_.GD.N0232.N0720.N1326.d019889 f hf 1 hbound, hg, hb, hae, ?_, ?_⟩
  · exact _root_.GD.N0232.N0720.N1326.d019921 m n k hdim hd f hf hhom 1 hbound hrep
  · exact _root_.GD.N0232.N0720.N1326.d019891 f hf hhom 1 hbound




theorem d020041 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {δ : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n δ) :
    ∃ (g : ℝ × ℝ → ℝ) (ell : ℕ → ℕ)
      (p : ∀ j, Option (Fin (ell j)) → _root_.GD.N0232.N0720.N1315.d019832)
      (a : ∀ j, Option (Fin (ell j)) → ℝ) (ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1315.d019832),
      Measurable g ∧ (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        δ =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ]
          _root_.GD.N0232.N0720.N1425.d014719 m n g) ∧
      (∀ j i, 0 ≤ a j i) ∧ (∀ j, ∑ i, a j i = 1) ∧
      (∀ j, (ν j : Measure _root_.GD.N0232.N0720.N1315.d019832) =
        ∑ i, ENNReal.ofReal (a j i) • Measure.dirac (p j i)) ∧
      (∀ j i, (p j i).2.1 ∈ Ioo (0 : ℝ) 1) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)),
        Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1330.d020037 hdim (ν j : Measure _root_.GD.N0232.N0720.N1315.d019832) x) atTop
          (𝓝 (_root_.GD.N0232.N0720.N1329.d019671 m n k hdim g x))) ∧
      (∀ x : _root_.GD.N0232.N0720.N1341.d004414 k, _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g x ∈
        Icc (min (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 0) (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 1))
          (max (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 0) (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 1))) := by
  obtain ⟨g, h, hg, hb, hrep, hadm, hcoordinate⟩ :=
    _root_.GD.N0232.N0720.N1330.d020040 m n k hdim hm hn hd
  obtain ⟨w, ns, hw, _hns, hlim⟩ := _root_.GD.N0232.N0720.N1314.d019732 hdim h hadm
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  let q : ∀ j, Option (Fin (ns j)) → _root_.GD.N0232.N0720.N1329.d019646 :=
    fun j ↦ _root_.GD.N0232.N0720.N1315.d019879 (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1314.d019725 i)
  let v : ∀ j, Option (Fin (ns j)) → ℝ := fun j ↦ _root_.GD.N0232.N0720.N1314.d019720 (w (ns j))
  have hv : ∀ j i, 0 ≤ v j i := fun j ↦ _root_.GD.N0232.N0720.N1314.d019721 _ (hw (ns j))
  have hp : ∀ j, ∃ i, 0 < v j i := fun j ↦ _root_.GD.N0232.N0720.N1314.d019722 _
  let ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1315.d019832 :=
    fun j ↦ _root_.GD.N0232.N0720.N1315.d019873 hdim hm0 hn0 (q j) (v j) (hv j) (hp j)
  have hlim' : ∀ᵐ u : _root_.GD.N0232.N0720.N1341.d004415 k ∂_root_.GD.N0232.N0720.N1341.d004416 k,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1330.d020032 (fun i ↦ _root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q j i)) (v j) u)
        atTop (𝓝 (h u)) := by
    simpa only [q, v, _root_.GD.N0232.N0720.N1330.d020033, _root_.GD.N0232.N0720.N1315.d019880] using hlim
  have hraw := _root_.GD.N0232.N0720.N1330.d020026
    (fun j ↦ _root_.GD.N0232.N0720.N1330.d020032 (fun i ↦ _root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q j i)) (v j))
    (fun j ↦ _root_.GD.N0232.N0720.N1330.d020036 _ (v j)) h hlim'
  refine ⟨g, ns, (fun j i ↦ _root_.GD.N0232.N0720.N1315.d019847 m n hm0 hn0 (q j i)),
    (fun j ↦ _root_.GD.N0232.N0720.N1315.d019870 hdim (q j) (v j)), ν, hg, hb, hrep,
    (fun j i ↦ _root_.GD.N0232.N0720.N1315.d019871 hdim hm0 hn0 (q j) (v j) (hv j) (hp j) i),
    (fun j ↦ _root_.GD.N0232.N0720.N1315.d019872 hdim hm0 hn0 (q j) (v j) (hv j) (hp j)),
    (fun _ ↦ rfl), (fun j i ↦ _root_.GD.N0232.N0720.N1315.d019841 hm0 hn0 (q j i)), ?_, ?_⟩
  · filter_upwards [hraw, hcoordinate] with x hx heq
    simp only [ν, _root_.GD.N0232.N0720.N1330.d020038]
    rwa [heq] at hx
  · exact _root_.GD.N0232.N0720.N1330.d020039 m n k hdim hb

end RawTerminal

end
end GD.N0232.N0720.N1330

#print axioms _root_.GD.N0232.N0720.N1330.d020026
#print axioms _root_.GD.N0232.N0720.N1330.d020036
#print axioms _root_.GD.N0232.N0720.N1330.d020038
#print axioms _root_.GD.N0232.N0720.N1330.d020041
