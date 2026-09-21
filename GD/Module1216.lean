import GD.Module0308
import GD.Module1215
import GD.Module0632















open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal BigOperators

namespace GD.N0232.N0720.N1329

noncomputable section

open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1342
open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0720.N1425
open _root_.GD.N0238.N0753

abbrev d019645 (m n : ℕ) := _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n
abbrev d019646 := ℝ × Ioo (0 : ℝ) 1


def d019647 (m n k : ℕ) (hdim : m + n = k + 1) :
    Fin m ⊕ Fin n ≃ Fin (k + 1) :=
  finSumFinEquiv.trans (finCongr hdim)


def d019648 (m n k : ℕ) (hdim : m + n = k + 1) :
    _root_.GD.N0232.N0720.N1329.d019645 m n ≃ᵐ _root_.GD.N0232.N0720.N1341.d004414 k :=
  ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n ↦ ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (k + 1) ↦ ℝ)
      (_root_.GD.N0232.N0720.N1329.d019647 m n k hdim))).trans
    (MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ))

@[simp] theorem d019649 (m n k : ℕ) (hdim : m + n = k + 1)
    (x : _root_.GD.N0232.N0720.N1341.d004414 k) (i : Fin m) :
    ((_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm x).1 i = x (_root_.GD.N0232.N0720.N1329.d019647 m n k hdim (.inl i)) := rfl

@[simp] theorem d019650 (m n k : ℕ) (hdim : m + n = k + 1)
    (x : _root_.GD.N0232.N0720.N1341.d004414 k) (i : Fin n) :
    ((_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm x).2 i = x (_root_.GD.N0232.N0720.N1329.d019647 m n k hdim (.inr i)) := rfl

theorem d019651 (m n k : ℕ) (hdim : m + n = k + 1) :
    MeasurePreserving (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim) volume volume := by
  have h := (PiLp.volume_preserving_toLp (Fin (k + 1))).comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin (k + 1) ↦ ℝ)
      (_root_.GD.N0232.N0720.N1329.d019647 m n k hdim)).comp
      (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin n ↦ ℝ)))
  simpa only [_root_.GD.N0232.N0720.N1329.d019648, MeasurableEquiv.coe_trans, Function.comp_assoc] using! h

theorem d019652 (m n k : ℕ) (hdim : m + n = k + 1)
    (c : ℝ) (x : _root_.GD.N0232.N0720.N1341.d004414 k) :
    (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm (c • x) = c • (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm x := by
  apply Prod.ext <;> funext i <;> rfl

private theorem d019653 {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ : Measure α) (ν : Measure β) (he : MeasurePreserving e μ ν)
    (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = ν.withDensity (fun y ↦ f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs]
  simpa only [Function.comp_apply, e.symm_apply_apply] using
    he.setLIntegral_comp_preimage hs (hf.comp e.symm.measurable)

def d019654 (v : Ioo (0 : ℝ) 1) : ℝ≥0 := ⟨v.1, v.2.1.le⟩

theorem d019655 (v : Ioo (0 : ℝ) 1) : _root_.GD.N0232.N0720.N1329.d019654 v ≠ 0 :=
  ne_of_gt (show 0 < _root_.GD.N0232.N0720.N1329.d019654 v from v.2.1)

def d019656 {k : ℕ} (q : _root_.GD.N0232.N0720.N1316.d004440 k) : Measure (_root_.GD.N0232.N0720.N1341.d004414 k) :=
  (Measure.pi (fun i : Fin (k + 1) ↦ gaussianReal q.1 (_root_.GD.N0232.N0720.N1329.d019654 (q.2 i)))).map
    (MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ))


theorem d019657 {k : ℕ} (q : _root_.GD.N0232.N0720.N1316.d004440 k) (x : _root_.GD.N0232.N0720.N1341.d004414 k) :
    (∏ i, gaussianPDFReal q.1 (_root_.GD.N0232.N0720.N1329.d019654 (q.2 i)) (x i)) = _root_.GD.N0232.N0720.N1316.d004445 q x := by
  unfold gaussianPDFReal _root_.GD.N0232.N0720.N1316.d004445 _root_.GD.N0232.N0720.N1316.d004443 _root_.GD.N0232.N0720.N1329.d019654
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Real.exp_sum]
  rfl


theorem d019658 {k : ℕ} (q : _root_.GD.N0232.N0720.N1316.d004440 k) :
    _root_.GD.N0232.N0720.N1329.d019656 q = volume.withDensity (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1316.d004445 q x)) := by
  let f : (i : Fin (k + 1)) → ℝ → ℝ :=
    fun i ↦ gaussianPDFReal q.1 (_root_.GD.N0232.N0720.N1329.d019654 (q.2 i))
  have hpi :
      Measure.pi (fun i : Fin (k + 1) ↦ gaussianReal q.1 (_root_.GD.N0232.N0720.N1329.d019654 (q.2 i))) =
        (volume : Measure (Fin (k + 1) → ℝ)).withDensity
          (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0719.N0932.d009190 f x)) := by
    exact _root_.GD.N0232.N0719.N0932.d009192
      (fun _ ↦ volume) (fun i ↦ gaussianReal q.1 (_root_.GD.N0232.N0720.N1329.d019654 (q.2 i))) f
      (fun i ↦ measurable_gaussianPDFReal _ _)
      (fun i x ↦ gaussianPDFReal_nonneg _ _ _)
      (fun i ↦ integrable_gaussianPDFReal _ _)
      (fun i ↦ gaussianReal_of_var_ne_zero _ (_root_.GD.N0232.N0720.N1329.d019655 (q.2 i)))
  unfold _root_.GD.N0232.N0720.N1329.d019656
  rw [hpi, _root_.GD.N0232.N0720.N1329.d019653
    (MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ)) volume volume
    (PiLp.volume_preserving_toLp (Fin (k + 1)))
    (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0719.N0932.d009190 f x))
    ((_root_.GD.N0232.N0719.N0932.d009191 f (fun i ↦ measurable_gaussianPDFReal _ _)).ennreal_ofReal)]
  congr 1
  funext x
  exact congrArg ENNReal.ofReal (_root_.GD.N0232.N0720.N1329.d019657 q x)

def d019659 (t : Ioo (0 : ℝ) 1) : Ioo (0 : ℝ) 1 :=
  ⟨1 - t.1, sub_pos.mpr t.2.2, by linarith [t.2.1]⟩


def d019660 (m n k : ℕ) (hdim : m + n = k + 1) (q : _root_.GD.N0232.N0720.N1329.d019646) : _root_.GD.N0232.N0720.N1316.d004440 k :=
  (q.1, fun i ↦ Sum.elim (fun _ : Fin m ↦ q.2)
    (fun _ : Fin n ↦ _root_.GD.N0232.N0720.N1329.d019659 q.2) ((_root_.GD.N0232.N0720.N1329.d019647 m n k hdim).symm i))

@[simp] theorem d019661 (m n k : ℕ) (hdim : m + n = k + 1)
    (q : _root_.GD.N0232.N0720.N1329.d019646) (i : Fin m) :
    (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim q).2 (_root_.GD.N0232.N0720.N1329.d019647 m n k hdim (.inl i)) = q.2 := by
  simp only [_root_.GD.N0232.N0720.N1329.d019660, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem d019662 (m n k : ℕ) (hdim : m + n = k + 1)
    (q : _root_.GD.N0232.N0720.N1329.d019646) (i : Fin n) :
    (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim q).2 (_root_.GD.N0232.N0720.N1329.d019647 m n k hdim (.inr i)) =
      _root_.GD.N0232.N0720.N1329.d019659 q.2 := by
  simp only [_root_.GD.N0232.N0720.N1329.d019660, Equiv.symm_apply_apply, Sum.elim_inr]

def d019663 (q : _root_.GD.N0232.N0720.N1329.d019646) : ℝ := Real.sqrt q.2.1
def d019664 (q : _root_.GD.N0232.N0720.N1329.d019646) : ℝ := Real.sqrt (1 - q.2.1)

theorem d019665 (q : _root_.GD.N0232.N0720.N1329.d019646) : 0 < _root_.GD.N0232.N0720.N1329.d019663 q :=
  Real.sqrt_pos.mpr q.2.2.1

theorem d019666 (q : _root_.GD.N0232.N0720.N1329.d019646) : 0 < _root_.GD.N0232.N0720.N1329.d019664 q :=
  Real.sqrt_pos.mpr (sub_pos.mpr q.2.2.2)

theorem d019667 (q : _root_.GD.N0232.N0720.N1329.d019646) :
    _root_.GD.N0232.N0719.N0932.d009193 (_root_.GD.N0232.N0720.N1329.d019663 q) = _root_.GD.N0232.N0720.N1329.d019654 q.2 := by
  apply Subtype.ext
  exact Real.sq_sqrt q.2.2.1.le

theorem d019668 (q : _root_.GD.N0232.N0720.N1329.d019646) :
    _root_.GD.N0232.N0719.N0932.d009193 (_root_.GD.N0232.N0720.N1329.d019664 q) = _root_.GD.N0232.N0720.N1329.d019654 (_root_.GD.N0232.N0720.N1329.d019659 q.2) := by
  apply Subtype.ext
  exact Real.sq_sqrt (sub_pos.mpr q.2.2.2).le



theorem d019669 (m n k : ℕ) (hdim : m + n = k + 1)
    (q : _root_.GD.N0232.N0720.N1329.d019646) :
    (_root_.GD.N0107.d009030 m n q.1 (_root_.GD.N0232.N0720.N1329.d019663 q) (_root_.GD.N0232.N0720.N1329.d019664 q)).map
        (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim) =
      volume.withDensity (fun x ↦ ENNReal.ofReal
        (_root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim q) x)) := by
  let p := _root_.GD.N0232.N0720.N1329.d019660 m n k hdim q
  let μ : Fin (k + 1) → Measure ℝ :=
    fun i ↦ gaussianReal p.1 (_root_.GD.N0232.N0720.N1329.d019654 (p.2 i))
  have hsum := measurePreserving_sumPiEquivProdPi_symm
    (fun i : Fin m ⊕ Fin n ↦ μ (_root_.GD.N0232.N0720.N1329.d019647 m n k hdim i))
  have hreindex := measurePreserving_piCongrLeft μ (_root_.GD.N0232.N0720.N1329.d019647 m n k hdim)
  have htoLp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (k + 1) → ℝ))
      (Measure.pi μ) (_root_.GD.N0232.N0720.N1329.d019656 p) := ⟨(MeasurableEquiv.toLp _ _).measurable, rfl⟩
  have h := (htoLp.comp (hreindex.comp hsum)).map_eq
  have hraw : _root_.GD.N0107.d009030 m n q.1 (_root_.GD.N0232.N0720.N1329.d019663 q) (_root_.GD.N0232.N0720.N1329.d019664 q) =
      (Measure.pi (fun i : Fin m ↦ μ (_root_.GD.N0232.N0720.N1329.d019647 m n k hdim (.inl i)))).prod
        (Measure.pi (fun i : Fin n ↦ μ (_root_.GD.N0232.N0720.N1329.d019647 m n k hdim (.inr i)))) := by
    rw [_root_.GD.N0232.N0720.d009061]
    change (_root_.GD.N0232.N0719.d009174 m q.1 (_root_.GD.N0232.N0720.N1329.d019663 q)).prod
      (_root_.GD.N0232.N0719.d009174 n q.1 (_root_.GD.N0232.N0720.N1329.d019664 q)) = _
    rw [_root_.GD.N0232.N0719.N0932.d009211, _root_.GD.N0232.N0719.N0932.d009211,
      _root_.GD.N0232.N0720.N1329.d019667, _root_.GD.N0232.N0720.N1329.d019668]
    simp only [μ, p, _root_.GD.N0232.N0720.N1329.d019660, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  rw [hraw]
  calc
    _ = _root_.GD.N0232.N0720.N1329.d019656 p := by
      simpa only [_root_.GD.N0232.N0720.N1329.d019648, MeasurableEquiv.coe_trans, Function.comp_assoc] using! h
    _ = _ := _root_.GD.N0232.N0720.N1329.d019658 p



theorem d019670 (m n k : ℕ) (hdim : m + n = k + 1)
    (q : _root_.GD.N0232.N0720.N1329.d019646) (f : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ) (hf : Measurable f) :
    (∫⁻ omega, ENNReal.ofReal ((f (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim omega) - q.1) ^ 2)
      ∂_root_.GD.N0107.d009030 m n q.1 (_root_.GD.N0232.N0720.N1329.d019663 q) (_root_.GD.N0232.N0720.N1329.d019664 q)) =
      ∫⁻ x, ENNReal.ofReal ((f x - q.1) ^ 2)
        ∂volume.withDensity (fun x ↦ ENNReal.ofReal
          (_root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0232.N0720.N1329.d019660 m n k hdim q) x)) := by
  rw [← _root_.GD.N0232.N0720.N1329.d019669 m n k hdim q]
  exact (lintegral_map ((hf.sub measurable_const).pow_const 2 |>.ennreal_ofReal)
    (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).measurable).symm


def d019671 (m n k : ℕ) (hdim : m + n = k + 1)
    (g : ℝ × ℝ → ℝ) (x : _root_.GD.N0232.N0720.N1341.d004414 k) : ℝ :=
  _root_.GD.N0232.N0720.N1425.d014719 m n g ((_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm x)

theorem d019672 (m n k : ℕ) (hdim : m + n = k + 1)
    {g : ℝ × ℝ → ℝ} (hg : Measurable g) :
    Measurable (_root_.GD.N0232.N0720.N1329.d019671 m n k hdim g) :=
  (_root_.GD.N0232.N0720.N1398.d019599 m n hg).comp
    (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm.measurable

theorem d019673 (m n k : ℕ) (hdim : m + n = k + 1)
    (g : ℝ × ℝ → ℝ) (omega : _root_.GD.N0232.N0720.N1329.d019645 m n) :
    _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim omega) =
      _root_.GD.N0232.N0720.N1425.d014719 m n g omega := by
  simp only [_root_.GD.N0232.N0720.N1329.d019671, MeasurableEquiv.symm_apply_apply]

theorem d019674 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (g : ℝ × ℝ → ℝ) (c : ℝ) (hc : 0 < c) (omega : _root_.GD.N0232.N0720.N1329.d019645 m n) :
    _root_.GD.N0232.N0720.N1425.d014719 m n g (c • omega) = c * _root_.GD.N0232.N0720.N1425.d014719 m n g omega := by
  have hXa : _root_.GD.N0107.d009018 m 0 c omega.1 = c • omega.1 := by
    funext i
    change 0 + c * omega.1 i = c * omega.1 i
    exact zero_add _
  have hYa : _root_.GD.N0107.d009018 n 0 c omega.2 = c • omega.2 := by
    funext i
    change 0 + c * omega.2 i = c * omega.2 i
    exact zero_add _
  have hXm : _root_.GD.N0107.d009084 (c • omega.1) = c * _root_.GD.N0107.d009084 omega.1 := by
    simpa only [hXa, zero_add] using!
      _root_.GD.N0232.N0719.N0900.d009135 hm 0 c omega.1
  have hYm : _root_.GD.N0107.d009084 (c • omega.2) = c * _root_.GD.N0107.d009084 omega.2 := by
    simpa only [hYa, zero_add] using!
      _root_.GD.N0232.N0719.N0900.d009135 hn 0 c omega.2
  have hXv : _root_.GD.N0107.d009085 (c • omega.1) = c ^ 2 * _root_.GD.N0107.d009085 omega.1 := by
    simpa only [hXa] using!
      _root_.GD.N0232.N0719.N0900.d009136 hm 0 c omega.1
  have hYv : _root_.GD.N0107.d009085 (c • omega.2) = c ^ 2 * _root_.GD.N0107.d009085 omega.2 := by
    simpa only [hYa] using!
      _root_.GD.N0232.N0719.N0900.d009136 hn 0 c omega.2
  have hfirst : _root_.GD.N0232.N0720.N1084.d014252 m n (c • omega) =
      c ^ 2 * _root_.GD.N0232.N0720.N1084.d014252 m n omega := by
    change _root_.GD.N0107.d009085 (c • omega.1) / m =
      c ^ 2 * (_root_.GD.N0107.d009085 omega.1 / m)
    rw [hXv]
    ring
  have hsecond : _root_.GD.N0232.N0720.N1084.d014253 m n (c • omega) =
      c ^ 2 * _root_.GD.N0232.N0720.N1084.d014253 m n omega := by
    change _root_.GD.N0107.d009085 (c • omega.2) / n =
      c ^ 2 * (_root_.GD.N0107.d009085 omega.2 / n)
    rw [hYv]
    ring
  change _root_.GD.N0107.d009084 (c • omega).1 = c * _root_.GD.N0107.d009084 omega.1 at hXm
  change _root_.GD.N0107.d009084 (c • omega).2 = c * _root_.GD.N0107.d009084 omega.2 at hYm
  unfold _root_.GD.N0232.N0720.N1425.d014719
  rw [hfirst, hsecond, hXm, hYm]
  simpa only [zero_add] using
    _root_.GD.N0232.N0720.N1437.d003003 (fun r s ↦ g (r, s))
      0 c (_root_.GD.N0107.d009084 omega.1) (_root_.GD.N0107.d009084 omega.2)
      (_root_.GD.N0232.N0720.N1084.d014252 m n omega)
      (_root_.GD.N0232.N0720.N1084.d014253 m n omega) hc

theorem d019675 (m n k : ℕ) (hdim : m + n = k + 1)
    (hm : 0 < m) (hn : 0 < n) (g : ℝ × ℝ → ℝ) :
    _root_.GD.N0238.N0753.d004397 (_root_.GD.N0232.N0720.N1329.d019671 m n k hdim g) := by
  intro c hc x
  change _root_.GD.N0232.N0720.N1425.d014719 m n g ((_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm (c • x)) = _
  rw [_root_.GD.N0232.N0720.N1329.d019652, _root_.GD.N0232.N0720.N1329.d019674 m n hm hn g c hc]
  rfl

private theorem d019676 {n : ℕ} (hn : 0 < n)
    (x : _root_.GD.N0137.d008894 n) (B : ℝ) (hx : ∀ i, |x i| ≤ B) :
    |_root_.GD.N0107.d009084 x| ≤ B := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [_root_.GD.N0107.d009084, _root_.GD.N0126.d006420,
    _root_.GD.N0126.d006419, Fintype.card_fin, abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  calc
    |∑ i, x i| ≤ ∑ i, |x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum (fun i _ ↦ hx i)
    _ = B * n := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_comm]



theorem d019677 (m n k : ℕ) (hdim : m + n = k + 1)
    (hm : 0 < m) (hn : 0 < n) (x : _root_.GD.N0232.N0720.N1341.d004414 k) :
    |_root_.GD.N0107.d009084 ((_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm x).1| ≤ ‖x‖ ∧
      |_root_.GD.N0107.d009084 ((_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm x).2| ≤ ‖x‖ := by
  constructor
  · apply _root_.GD.N0232.N0720.N1329.d019676 hm
    intro i
    exact PiLp.norm_apply_le x (_root_.GD.N0232.N0720.N1329.d019647 m n k hdim (.inl i))
  · apply _root_.GD.N0232.N0720.N1329.d019676 hn
    intro i
    exact PiLp.norm_apply_le x (_root_.GD.N0232.N0720.N1329.d019647 m n k hdim (.inr i))



theorem d019678 (m n k : ℕ) (hdim : m + n = k + 1)
    (hm : 0 < m) (hn : 0 < n)
    {g : ℝ × ℝ → ℝ} (hg : ∀ p, g p ∈ Icc (0 : ℝ) 1) (x : _root_.GD.N0232.N0720.N1341.d004414 k) :
    ‖_root_.GD.N0232.N0720.N1329.d019671 m n k hdim g x‖ ≤ ‖x‖ := by
  obtain ⟨hX, hY⟩ := _root_.GD.N0232.N0720.N1329.d019677 m n k hdim hm hn x
  have hbetween := _root_.GD.N0232.N0720.N1342.d019643 m n hg
    ((_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm x)
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · exact (le_min (abs_le.mp hX).1 (abs_le.mp hY).1).trans hbetween.1
  · exact hbetween.2.trans (max_le (abs_le.mp hX).2 (abs_le.mp hY).2)

theorem d019679 (m n k : ℕ) (hdim : m + n = k + 1)
    (hm : 0 < m) (hn : 0 < n)
    {g : ℝ × ℝ → ℝ} (hg : ∀ p, g p ∈ Icc (0 : ℝ) 1) (u : _root_.GD.N0232.N0720.N1341.d004415 k) :
    ‖_root_.GD.N0232.N0720.N1329.d019671 m n k hdim g u‖ ≤ 1 := by
  simpa only [mem_sphere_zero_iff_norm.mp u.2] using
    _root_.GD.N0232.N0720.N1329.d019678 m n k hdim hm hn hg (u : _root_.GD.N0232.N0720.N1341.d004414 k)

theorem d019680 (m n k : ℕ) (hdim : m + n = k + 1)
    (hm : 0 < m) (hn : 0 < n)
    {g : ℝ × ℝ → ℝ} (hg : Measurable g) (hb : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    MemLp (fun u : _root_.GD.N0232.N0720.N1341.d004415 k ↦ _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g u) 2 (_root_.GD.N0232.N0720.N1341.d004416 k) :=
  MemLp.of_bound
    ((_root_.GD.N0232.N0720.N1329.d019672 m n k hdim hg).comp measurable_subtype_coe).aestronglyMeasurable
    1 (Filter.Eventually.of_forall (_root_.GD.N0232.N0720.N1329.d019679 m n k hdim hm hn hb))

end
end GD.N0232.N0720.N1329

#print axioms _root_.GD.N0232.N0720.N1329.d019651
#print axioms _root_.GD.N0232.N0720.N1329.d019658
#print axioms _root_.GD.N0232.N0720.N1329.d019669
#print axioms _root_.GD.N0232.N0720.N1329.d019670
#print axioms _root_.GD.N0232.N0720.N1329.d019675
#print axioms _root_.GD.N0232.N0720.N1329.d019678
#print axioms _root_.GD.N0232.N0720.N1329.d019680
