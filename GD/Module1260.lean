import GD.Module0753
import GD.Module1259

set_option autoImplicit false
set_option warningAsError true


















open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology

namespace GD.N0232.N0719.N0982

open _root_.GD.N0232.N0719.N0873
open _root_.GD.N0232.N0720


noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]


def d020335 (i : I) : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] _root_.GD.N0232.N0719.N0873.d011295 I :=
  (ContinuousLinearMap.pi fun j => _root_.GD.N0232.N0720.N1352.d002741 (if j = i then 0 else 1)).prod
    (ContinuousLinearMap.pi fun j => _root_.GD.N0232.N0720.N1352.d002741 (if j = i then 2 else 3))

omit [Fintype I] in
@[simp] theorem d020336 (i j : I) (x : _root_.GD.N0232.N0720.N1352.d002739) :
    (_root_.GD.N0232.N0719.N0982.d020335 i x).1 j = if j = i then x 0 else x 1 := by
  by_cases h : j = i <;> simp [_root_.GD.N0232.N0719.N0982.d020335, h]

omit [Fintype I] in
@[simp] theorem d020337 (i j : I) (x : _root_.GD.N0232.N0720.N1352.d002739) :
    (_root_.GD.N0232.N0719.N0982.d020335 i x).2 j = if j = i then x 2 else x 3 := by
  by_cases h : j = i <;> simp [_root_.GD.N0232.N0719.N0982.d020335, h]

omit [Fintype I] in
theorem d020338 (i : I) : _root_.GD.N0232.N0719.N0982.d020335 i (_root_.GD.N0232.N0720.N1352.d002740 0) = _root_.GD.N0232.N0719.N0873.d011296 i := by
  ext j <;> by_cases h : j = i <;> simp [_root_.GD.N0232.N0720.N1352.d002740, _root_.GD.N0232.N0719.N0873.d011296, h, eq_comm]

omit [Fintype I] in
theorem d020339 (i : I) : _root_.GD.N0232.N0719.N0982.d020335 i (_root_.GD.N0232.N0720.N1352.d002740 2) = _root_.GD.N0232.N0719.N0873.d011297 i := by
  ext j <;> by_cases h : j = i <;> simp [_root_.GD.N0232.N0720.N1352.d002740, _root_.GD.N0232.N0719.N0873.d011297, h, eq_comm]

theorem d020340 (i : I) :
    _root_.GD.N0232.N0719.N0982.d020335 i (_root_.GD.N0232.N0720.N1352.d002740 1) = ∑ j ∈ Finset.univ.erase i, _root_.GD.N0232.N0719.N0873.d011296 j := by
  ext l
  · change _ = _root_.GD.N0232.N0719.N0873.d011298 l (∑ j ∈ Finset.univ.erase i, _root_.GD.N0232.N0719.N0873.d011296 j)
    rw [map_sum]
    by_cases h : l = i <;> simp [_root_.GD.N0232.N0720.N1352.d002740, _root_.GD.N0232.N0719.N0873.d011296, Pi.single_apply, h]
  · change _ = _root_.GD.N0232.N0719.N0873.d011299 l (∑ j ∈ Finset.univ.erase i, _root_.GD.N0232.N0719.N0873.d011296 j)
    rw [map_sum]
    by_cases h : l = i <;> simp [_root_.GD.N0232.N0720.N1352.d002740, _root_.GD.N0232.N0719.N0873.d011296, h]

theorem d020341 (i : I) :
    _root_.GD.N0232.N0719.N0982.d020335 i (_root_.GD.N0232.N0720.N1352.d002740 3) = ∑ j ∈ Finset.univ.erase i, _root_.GD.N0232.N0719.N0873.d011297 j := by
  ext l
  · change _ = _root_.GD.N0232.N0719.N0873.d011298 l (∑ j ∈ Finset.univ.erase i, _root_.GD.N0232.N0719.N0873.d011297 j)
    rw [map_sum]
    by_cases h : l = i <;> simp [_root_.GD.N0232.N0720.N1352.d002740, _root_.GD.N0232.N0719.N0873.d011297, h]
  · change _ = _root_.GD.N0232.N0719.N0873.d011299 l (∑ j ∈ Finset.univ.erase i, _root_.GD.N0232.N0719.N0873.d011297 j)
    rw [map_sum]
    by_cases h : l = i <;> simp [_root_.GD.N0232.N0720.N1352.d002740, _root_.GD.N0232.N0719.N0873.d011297, Pi.single_apply, h]

def d020342 : Set (_root_.GD.N0232.N0719.N0873.d011295 I) := {x | ∀ i, 0 < x.2 i}

omit [DecidableEq I] in
theorem d020343 : IsOpen (_root_.GD.N0232.N0719.N0982.d020342 (I := I)) := by
  simp only [_root_.GD.N0232.N0719.N0982.d020342, setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const (_root_.GD.N0232.N0719.N0873.d011299 i).continuous

omit [Fintype I] in
theorem d020344 (i : I) {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    _root_.GD.N0232.N0719.N0982.d020335 i x ∈ _root_.GD.N0232.N0719.N0982.d020342 := by
  intro j
  by_cases h : j = i <;> simp [h, _root_.GD.N0232.N0720.N1270.d020224] at * <;> tauto

def d020345 (x : _root_.GD.N0232.N0719.N0873.d011295 I) (a : ℝ) : _root_.GD.N0232.N0719.N0873.d011295 I := (a • x.1, a ^ 2 • x.2)

omit [Fintype I] in
theorem d020346 (i : I) (x : _root_.GD.N0232.N0720.N1352.d002739) (a : ℝ) :
    _root_.GD.N0232.N0719.N0982.d020335 i (_root_.GD.N0232.N0720.N1352.d002795 x a) = _root_.GD.N0232.N0719.N0982.d020345 (_root_.GD.N0232.N0719.N0982.d020335 i x) a := by
  ext j <;> by_cases h : j = i <;>
    simp [_root_.GD.N0232.N0719.N0982.d020345, h, _root_.GD.N0232.N0720.N1352.d002795, _root_.GD.N0232.N0720.N1352.d002793, _root_.GD.N0232.N0720.N1352.d002794, _root_.GD.N0232.N0720.N1352.d002740]

theorem d020347 (i : I) {F : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hF : DifferentiableAt ℝ F (_root_.GD.N0232.N0719.N0982.d020335 i x)) (v : _root_.GD.N0232.N0720.N1352.d002739) :
    fderiv ℝ (F ∘ _root_.GD.N0232.N0719.N0982.d020335 i) x v = fderiv ℝ F (_root_.GD.N0232.N0719.N0982.d020335 i x) (_root_.GD.N0232.N0719.N0982.d020335 i v) := by
  rw [(hF.hasFDerivAt.comp x (_root_.GD.N0232.N0719.N0982.d020335 i).hasFDerivAt).fderiv]
  rfl



theorem d020348 (i : I) {M N : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ} {x : _root_.GD.N0232.N0720.N1352.d002739}
    (hM : DifferentiableAt ℝ M (_root_.GD.N0232.N0719.N0982.d020335 i x))
    (hN : DifferentiableAt ℝ N (_root_.GD.N0232.N0719.N0982.d020335 i x))
    (hpde : ∀ j, fderiv ℝ N (_root_.GD.N0232.N0719.N0982.d020335 i x) (_root_.GD.N0232.N0719.N0873.d011297 j) =
      (_root_.GD.N0232.N0719.N0982.d020335 i x).1 j * fderiv ℝ M (_root_.GD.N0232.N0719.N0982.d020335 i x) (_root_.GD.N0232.N0719.N0873.d011297 j) -
        fderiv ℝ M (_root_.GD.N0232.N0719.N0982.d020335 i x) (_root_.GD.N0232.N0719.N0873.d011296 j)) :
    fderiv ℝ (N ∘ _root_.GD.N0232.N0719.N0982.d020335 i) x (_root_.GD.N0232.N0720.N1352.d002740 2) =
      x 0 * fderiv ℝ (M ∘ _root_.GD.N0232.N0719.N0982.d020335 i) x (_root_.GD.N0232.N0720.N1352.d002740 2) -
        fderiv ℝ (M ∘ _root_.GD.N0232.N0719.N0982.d020335 i) x (_root_.GD.N0232.N0720.N1352.d002740 0) ∧
    fderiv ℝ (N ∘ _root_.GD.N0232.N0719.N0982.d020335 i) x (_root_.GD.N0232.N0720.N1352.d002740 3) =
      x 1 * fderiv ℝ (M ∘ _root_.GD.N0232.N0719.N0982.d020335 i) x (_root_.GD.N0232.N0720.N1352.d002740 3) -
        fderiv ℝ (M ∘ _root_.GD.N0232.N0719.N0982.d020335 i) x (_root_.GD.N0232.N0720.N1352.d002740 1) := by
  simp only [_root_.GD.N0232.N0719.N0982.d020347 i hM, _root_.GD.N0232.N0719.N0982.d020347 i hN,
    _root_.GD.N0232.N0719.N0982.d020338, _root_.GD.N0232.N0719.N0982.d020340, _root_.GD.N0232.N0719.N0982.d020339, _root_.GD.N0232.N0719.N0982.d020341]
  constructor
  · simpa using hpde i
  · simp only [map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simpa [(Finset.mem_erase.mp hj).1] using hpde j

omit [Fintype I] in

theorem d020349 (i : I) (δ : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ) (G : _root_.GD.N0232.N0720.N1352.d002739 → ℝ)
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hδ : δ (_root_.GD.N0232.N0719.N0982.d020335 i x) = _root_.GD.N0232.N0720.N1352.d002804 G x) :
    _root_.GD.N0232.N0719.N0982.d020335 i (_root_.GD.N0232.N0720.N1352.d002753 G x) = _root_.GD.N0232.N0719.N0873.d011318 δ i (_root_.GD.N0232.N0719.N0982.d020335 i x) := by
  simp [_root_.GD.N0232.N0720.N1352.d002753, _root_.GD.N0232.N0719.N0982.d020338, _root_.GD.N0232.N0719.N0982.d020339, _root_.GD.N0232.N0719.N0873.d011318,
    hδ, _root_.GD.N0232.N0720.N1352.d002804]


theorem d020350 (i : I) (δ : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ) (G : _root_.GD.N0232.N0720.N1352.d002739 → ℝ)
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hδ : δ (_root_.GD.N0232.N0719.N0982.d020335 i x) = _root_.GD.N0232.N0720.N1352.d002804 G x) :
    _root_.GD.N0232.N0719.N0982.d020335 i (_root_.GD.N0232.N0720.N1352.d002754 G x) =
      ∑ j ∈ Finset.univ.erase i, _root_.GD.N0232.N0719.N0873.d011318 δ j (_root_.GD.N0232.N0719.N0982.d020335 i x) := by
  simp only [_root_.GD.N0232.N0720.N1352.d002754, map_add, map_smul, _root_.GD.N0232.N0719.N0982.d020340, _root_.GD.N0232.N0719.N0982.d020341,
    Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hji := (Finset.mem_erase.mp hj).1
  simp only [_root_.GD.N0232.N0719.N0873.d011318, _root_.GD.N0232.N0719.N0982.d020336, if_neg hji, hδ]
  congr 2
  simp only [_root_.GD.N0232.N0720.N1352.d002804, _root_.GD.N0232.N0720.N1352.d002742]
  ring


structure d020351 (degree : ℕ) (δ : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ) where
  M : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ
  N : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ
  smooth_M : ContDiffOn ℝ ∞ M _root_.GD.N0232.N0719.N0982.d020342
  smooth_N : ContDiffOn ℝ ∞ N _root_.GD.N0232.N0719.N0982.d020342
  positive_M : ∀ x ∈ _root_.GD.N0232.N0719.N0982.d020342, 0 < M x
  numerator : ∀ x ∈ _root_.GD.N0232.N0719.N0982.d020342, N x = δ x * M x
  pde : ∀ x ∈ _root_.GD.N0232.N0719.N0982.d020342, ∀ j,
    fderiv ℝ N x (_root_.GD.N0232.N0719.N0873.d011297 j) = x.1 j * fderiv ℝ M x (_root_.GD.N0232.N0719.N0873.d011297 j) -
      fderiv ℝ M x (_root_.GD.N0232.N0719.N0873.d011296 j)
  homogeneous : ∀ x ∈ _root_.GD.N0232.N0719.N0982.d020342, ∀ a : ℝ, 0 < a →
    a ^ degree * M (_root_.GD.N0232.N0719.N0982.d020345 x a) = M x



def d020351.d020352 {degree : ℕ} {δ : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ} (m : _root_.GD.N0232.N0719.N0982.d020351 degree δ)
    (i : I) (g : _root_.GD.N0232.N0720.N1351.d002812 → ℝ)
    (hδ : ∀ x ∈ _root_.GD.N0232.N0720.N1270.d020224,
      δ (_root_.GD.N0232.N0719.N0982.d020335 i x) = _root_.GD.N0232.N0720.N1352.d002804 (g ∘ _root_.GD.N0232.N0720.N1351.d002814) x) :
    _root_.GD.N0232.N0720.N1270.d020238 degree g where
  M := m.M ∘ _root_.GD.N0232.N0719.N0982.d020335 i
  N := m.N ∘ _root_.GD.N0232.N0719.N0982.d020335 i
  smooth_M := m.smooth_M.comp (_root_.GD.N0232.N0719.N0982.d020335 i).contDiff.contDiffOn
    (fun _ hx => _root_.GD.N0232.N0719.N0982.d020344 i hx)
  positive_M := fun _ hx => m.positive_M _ (_root_.GD.N0232.N0719.N0982.d020344 i hx)
  numerator := by
    intro x hx
    simpa only [Function.comp_apply, hδ x hx] using
      m.numerator _ (_root_.GD.N0232.N0719.N0982.d020344 i hx)
  pde := by
    intro x hx
    have hy := _root_.GD.N0232.N0719.N0982.d020344 i hx
    exact _root_.GD.N0232.N0719.N0982.d020348 i
      ((m.smooth_M.contDiffAt (_root_.GD.N0232.N0719.N0982.d020343.mem_nhds hy)).differentiableAt (by simp))
      ((m.smooth_N.contDiffAt (_root_.GD.N0232.N0719.N0982.d020343.mem_nhds hy)).differentiableAt (by simp))
      (m.pde _ hy)
  homogeneous := by
    intro x hx a ha
    simpa only [Function.comp_apply, _root_.GD.N0232.N0719.N0982.d020346] using
      m.homogeneous _ (_root_.GD.N0232.N0719.N0982.d020344 i hx) a ha

open _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1308 _root_.GD.N0232.N0720.N1317
open _root_.GD.N0232.N0720.N1368
open _root_.GD.N0232.N0720.N1352 (d002742 d002762)
open _root_.GD.N0232.N0720.N1270 (d020224 d020225 d020226
  d020227 d020228)





theorem d020353
    (D : ℕ) {δ : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ} (m : _root_.GD.N0232.N0719.N0982.d020351 (D + 1) δ)
    (i : I) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hδ : ∀ x ∈ _root_.GD.N0232.N0720.N1270.d020224, δ (_root_.GD.N0232.N0719.N0982.d020335 i x) =
      _root_.GD.N0232.N0720.N1352.d002804
        (_root_.GD.N0232.N0720.N1308.d020280 D mu ∘ _root_.GD.N0232.N0720.N1351.d002814) x)
    (z w : ℝ) (hz : 0 < z) (hw : 0 < w) :
    _root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 ((D : ℝ) / 2) mu) z w 0 = 0 := by
  by_contra hF
  let m0 := _root_.GD.N0232.N0720.N1308.d020292 D mu
  let m1 := m.d020352 i (_root_.GD.N0232.N0720.N1308.d020280 D mu) hδ
  let H : _root_.GD.N0232.N0720.N1352.d002739 → ℝ := fun x => m1.M x / m0.M x
  have hHinf : ContDiffOn ℝ ∞ H _root_.GD.N0232.N0720.N1270.d020224 :=
    m1.smooth_M.fun_div m0.smooth_M (fun x hx => (m0.positive_M x hx).ne')
  have hH : ContDiffOn ℝ 2 H _root_.GD.N0232.N0720.N1270.d020224 := (contDiffOn_infty.mp hHinf) 2
  have hx := _root_.GD.N0232.N0720.N1270.d020227 hw hz
  apply _root_.GD.N0232.N0720.N1318.d002811
    D _root_.GD.N0232.N0720.N1270.d020225 (_root_.GD.N0232.N0720.N1317.d020332 D mu)
    hH m0.smooth_M m1.smooth_M
    (fun x hx => (m0.positive_M x hx).ne')
    (fun x hx => (div_mul_cancel₀ (m1.M x) (m0.positive_M x hx).ne').symm)
    m0.numerator m1.numerator m0.pde m1.pde hx (_root_.GD.N0232.N0720.N1270.d020228 w z)
  · rw [_root_.GD.N0232.N0720.N1317.d020333 _ _ hz hw]
    exact neg_ne_zero.mpr hF
  · exact (m1.positive_M _ hx).ne'
  · filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num)] with a ha
    exact ⟨m0.homogeneous _ hx a ha, m1.homogeneous _ hx a ha⟩



theorem d020354
    (D : ℕ) {δ : _root_.GD.N0232.N0719.N0873.d011295 I → ℝ} (m : _root_.GD.N0232.N0719.N0982.d020351 (D + 1) δ)
    (i : I) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hδ : ∀ x ∈ _root_.GD.N0232.N0720.N1270.d020224, δ (_root_.GD.N0232.N0719.N0982.d020335 i x) =
      _root_.GD.N0232.N0720.N1352.d002804
        (_root_.GD.N0232.N0720.N1308.d020280 D mu ∘ _root_.GD.N0232.N0720.N1351.d002814) x)
    (center : ℝ) :
    ∀ᶠ epsilon in 𝓝 (0 : ℝ),
      _root_.GD.N0232.N0720.N1290.d004143 ((D : ℝ) / 2) (_root_.GD.N0232.N0720.N1290.d004147 center epsilon) mu = 0 :=
  _root_.GD.N0232.N0720.N1368.d020221 _ center mu
    (_root_.GD.N0232.N0719.N0982.d020353 D m i mu hδ)

end
end GD.N0232.N0719.N0982

#print axioms _root_.GD.N0232.N0719.N0982.d020348
#print axioms _root_.GD.N0232.N0719.N0982.d020351.d020352
#print axioms _root_.GD.N0232.N0719.N0982.d020353
#print axioms _root_.GD.N0232.N0719.N0982.d020354
