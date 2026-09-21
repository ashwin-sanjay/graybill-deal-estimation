import GD.Module1220
import GD.Module1228
import GD.Module0663

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace GD.N0211.N0459

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0977 _root_.GD.N0232.N0719.N0976
open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1326
  (d019884 d019886 d019887)
open _root_.GD.N0232.N0720.N1316
  (d004471 d004472 d004476 d004477)
open _root_.GD.N0232.N0720.N1314
open _root_.GD.N0238.N0753

noncomputable section
variable {d : ℕ}

def d019947 (z : _root_.GD.N0232.N0719.N0977.d009764 d) : _root_.GD.N0232.N0719.N0977.d009765 d := WithLp.toLp 2 (fun i => z i.succ - z 0)

@[fun_prop] theorem d019948 : Continuous (_root_.GD.N0211.N0459.d019947 (d := d)) := by
  unfold _root_.GD.N0211.N0459.d019947
  fun_prop

def d019949 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (z : _root_.GD.N0232.N0719.N0977.d009764 d) : ℝ :=
  z 0 + _root_.GD.N0232.N0720.N1341.d004418 h (_root_.GD.N0211.N0459.d019947 z)

@[fun_prop] theorem d019950 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hh : Measurable h) :
    Measurable (_root_.GD.N0211.N0459.d019949 h) :=
  (measurable_pi_apply 0).add ((_root_.GD.N0232.N0720.N1326.d019884 hh).comp _root_.GD.N0211.N0459.d019948.measurable)

theorem d019951 (z : _root_.GD.N0232.N0719.N0977.d009764 d) (c a : ℝ) :
    _root_.GD.N0211.N0459.d019947 (_root_.GD.N0232.N0719.N0977.d009774 d c a z) = a • _root_.GD.N0211.N0459.d019947 z := by
  ext i
  simp only [_root_.GD.N0211.N0459.d019947, _root_.GD.N0232.N0719.N0977.d009774, PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem d019952 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) : _root_.GD.N0232.N0719.N0977.d009783 d (_root_.GD.N0211.N0459.d019949 h) := by
  intro c a ha z
  unfold _root_.GD.N0211.N0459.d019949
  rw [_root_.GD.N0211.N0459.d019951, _root_.GD.N0232.N0720.N1341.d004419 h a ha]
  simp only [_root_.GD.N0232.N0719.N0977.d009774, smul_eq_mul]
  ring

@[simp] theorem d019953 (u : _root_.GD.N0232.N0720.N1341.d004415 d) : _root_.GD.N0211.N0459.d019947 (_root_.GD.N0232.N0719.N0977.d009773 d u) = u := by
  ext i
  simp [_root_.GD.N0211.N0459.d019947, _root_.GD.N0232.N0719.N0977.d009773]

@[simp] theorem d019954 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    _root_.GD.N0211.N0459.d019949 h (_root_.GD.N0232.N0719.N0977.d009773 d u) = h u := by
  rw [_root_.GD.N0211.N0459.d019949, _root_.GD.N0211.N0459.d019953, _root_.GD.N0232.N0720.N1341.d004420]
  simp [_root_.GD.N0232.N0719.N0977.d009773]

@[simp] theorem d019955 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (c : ℝ) (v : _root_.GD.N0232.N0719.N0977.d009765 d) :
    _root_.GD.N0211.N0459.d019949 h (_root_.GD.N0232.N0719.N0977.d009768 d (c, v)) = c + _root_.GD.N0232.N0720.N1341.d004418 h v := by
  have hdiff : _root_.GD.N0211.N0459.d019947 (_root_.GD.N0232.N0719.N0977.d009768 d (c, v)) = v := by
    ext i
    simp [_root_.GD.N0211.N0459.d019947, _root_.GD.N0232.N0719.N0977.d009769]
  rw [_root_.GD.N0211.N0459.d019949, hdiff]
  simp [_root_.GD.N0232.N0719.N0977.d009769]



theorem d019956 {f g : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ}
    (hfg : f =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 d] g) :
    _root_.GD.N0211.N0459.d019949 f =ᵐ[(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d))] _root_.GD.N0211.N0459.d019949 g := by
  have hdiff := _root_.GD.N0232.N0720.N1326.d019886 hfg
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)))).ae hdiff
  have hchart : ∀ᵐ p : ℝ × _root_.GD.N0232.N0719.N0977.d009765 d ∂volume,
      _root_.GD.N0211.N0459.d019949 f (_root_.GD.N0232.N0719.N0977.d009768 d p) = _root_.GD.N0211.N0459.d019949 g (_root_.GD.N0232.N0719.N0977.d009768 d p) := by
    rw [Measure.volume_eq_prod]
    filter_upwards [hprod] with p hp
    change _root_.GD.N0232.N0720.N1341.d004418 f p.2 = _root_.GD.N0232.N0720.N1341.d004418 g p.2 at hp
    change _root_.GD.N0211.N0459.d019949 f (_root_.GD.N0232.N0719.N0977.d009768 d (p.1, p.2)) =
      _root_.GD.N0211.N0459.d019949 g (_root_.GD.N0232.N0719.N0977.d009768 d (p.1, p.2))
    rw [_root_.GD.N0211.N0459.d019955, _root_.GD.N0211.N0459.d019955, hp]
  have hback := MeasurePreserving.symm (_root_.GD.N0232.N0719.N0977.d009768 d) (_root_.GD.N0232.N0719.N0977.d009770 d)
  have h := hback.quasiMeasurePreserving.ae hchart
  filter_upwards [h] with x hx
  simpa only [MeasurableEquiv.apply_symm_apply] using hx

theorem d019957 (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ) (hf : _root_.GD.N0232.N0719.N0977.d009783 d f) :
    _root_.GD.N0211.N0459.d019949 (fun u => f (_root_.GD.N0232.N0719.N0977.d009773 d u)) = f := by
  have hhom : _root_.GD.N0238.N0753.d004397 (fun v : _root_.GD.N0232.N0719.N0977.d009765 d => f (Fin.cons 0 (fun i => v i))) := by
    intro a ha v
    change f (Fin.cons 0 (fun i => (a • v) i)) = a * f (Fin.cons 0 (fun i => v i))
    have hz : Fin.cons 0 (fun i => (a • v) i) =
        _root_.GD.N0232.N0719.N0977.d009774 d 0 a (Fin.cons 0 (fun i => v i)) := by
      funext i
      cases i using Fin.cases <;> simp [_root_.GD.N0232.N0719.N0977.d009774]
    rw [hz, hf 0 a ha]
    simp
  have hrestr := _root_.GD.N0232.N0720.N1326.d019887 _ hhom
  funext z
  change z 0 + _root_.GD.N0232.N0720.N1341.d004418 (fun u : _root_.GD.N0232.N0720.N1341.d004415 d => f (Fin.cons 0 (fun i => u.val i)))
    (_root_.GD.N0211.N0459.d019947 z) = f z
  rw [hrestr]
  have hz : _root_.GD.N0232.N0719.N0977.d009774 d (z 0) 1 (Fin.cons 0 (fun i => (_root_.GD.N0211.N0459.d019947 z) i)) = z := by
    funext i
    cases i using Fin.cases <;> simp [_root_.GD.N0232.N0719.N0977.d009774, _root_.GD.N0211.N0459.d019947]
  simpa only [one_mul] using (hf (z 0) 1 zero_lt_one (Fin.cons 0 (fun i => (_root_.GD.N0211.N0459.d019947 z) i))).symm.trans
    (congrArg f hz)

theorem d019958 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ)
    (hh : ∀ u, |h u| ≤ 1) (v : _root_.GD.N0232.N0719.N0977.d009765 d) : |_root_.GD.N0232.N0720.N1341.d004418 h v| ≤ ‖v‖ := by
  by_cases hv : v = 0
  · subst v
    simp [_root_.GD.N0232.N0720.N1341.d004418, _root_.GD.N0238.N0753.d004402]
  · let u : _root_.GD.N0232.N0720.N1341.d004415 d := ⟨‖v‖⁻¹ • v, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
    have heq : v = ‖v‖ • (u : _root_.GD.N0232.N0719.N0977.d009765 d) := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
    conv_lhs => rw [heq]
    rw [_root_.GD.N0232.N0720.N1341.d004419 _ _ (norm_pos_iff.mpr hv), _root_.GD.N0232.N0720.N1341.d004420]
    simpa only [smul_eq_mul, abs_mul, abs_norm, mul_one] using
      mul_le_mul_of_nonneg_left (hh u) (norm_nonneg v)

theorem d019959 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ)
    (hh : ∀ u, |h u| ≤ 1) (z : _root_.GD.N0232.N0719.N0977.d009764 d) :
    |_root_.GD.N0211.N0459.d019949 h z| ≤ |z 0| + ‖_root_.GD.N0211.N0459.d019947 z‖ := by
  apply (abs_add_le _ _).trans
  exact add_le_add le_rfl (_root_.GD.N0211.N0459.d019958 h hh _)

theorem d019960 (u : _root_.GD.N0232.N0720.N1341.d004415 d) (i : Fin (d + 2)) : |_root_.GD.N0232.N0719.N0977.d009773 d u i| ≤ 1 := by
  cases i using Fin.cases
  · simp [_root_.GD.N0232.N0719.N0977.d009773]
  · rename_i i
    have h := PiLp.norm_apply_le (u : _root_.GD.N0232.N0719.N0977.d009765 d) i
    simpa only [_root_.GD.N0232.N0719.N0977.d009773, Fin.cons_succ, Real.norm_eq_abs,
      mem_sphere_zero_iff_norm.mp u.property] using h

theorem d019961 (tau : _root_.GD.N0232.N0719.N0976.d019733 d) (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    _root_.GD.N0232.N0719.N0976.d019734 tau u ∈ Icc (-1 : ℝ) 1 := by
  have hT := _root_.GD.N0232.N0719.N0977.d009779 d tau.val tau.property
  unfold _root_.GD.N0232.N0719.N0976.d019734 _root_.GD.N0230.N0615.d000152
  constructor
  · apply (le_div_iff₀ hT).2
    calc
      -1 * _root_.GD.N0230.N0615.d000151 tau.val =
          ∑ i, tau.val i * (-1) := by
        simp [_root_.GD.N0230.N0615.d000151, Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (abs_le.mp (_root_.GD.N0211.N0459.d019960 u i)).1 (tau.property i).le
  · apply (div_le_iff₀ hT).2
    calc
      _ ≤ ∑ i, tau.val i * 1 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (abs_le.mp (_root_.GD.N0211.N0459.d019960 u i)).2 (tau.property i).le
      _ = _ := by simp [_root_.GD.N0230.N0615.d000151]

def d019962 (x : ℝ) : ℝ := max (-1) (min 1 x)

@[fun_prop] theorem d019963 : Continuous _root_.GD.N0211.N0459.d019962 := by
  unfold _root_.GD.N0211.N0459.d019962
  fun_prop

theorem d019964 (x : ℝ) : |_root_.GD.N0211.N0459.d019962 x| ≤ 1 := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem d019965 (x c : ℝ) (hc : c ∈ Icc (-1 : ℝ) 1) :
    (_root_.GD.N0211.N0459.d019962 x - c) ^ 2 ≤ (x - c) ^ 2 := by
  have h := _root_.GD.N0232.N0719.N0980.d009705 hc.1 hc.2 (a := x)
  simpa only [sq_abs, _root_.GD.N0211.N0459.d019962] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 h

def d019966 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) (u : _root_.GD.N0232.N0720.N1341.d004415 d) : ℝ :=
  _root_.GD.N0211.N0459.d019962 (_root_.GD.N0232.N0719.N0976.d019748 ref u (h u))

@[fun_prop] theorem d019967 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    Measurable (_root_.GD.N0211.N0459.d019966 ref h) := by
  have hh : Measurable (fun u : _root_.GD.N0232.N0720.N1341.d004415 d => h u) := (Lp.stronglyMeasurable h).measurable
  unfold _root_.GD.N0211.N0459.d019966 _root_.GD.N0232.N0719.N0976.d019748
  exact _root_.GD.N0211.N0459.d019963.measurable.comp
    ((_root_.GD.N0232.N0719.N0976.d019741 ref).continuous.measurable.add
      (hh.div ((_root_.GD.N0232.N0719.N0976.d019742 ref).continuous.measurable.sqrt)))

theorem d019968 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    |_root_.GD.N0211.N0459.d019966 ref h u| ≤ 1 := _root_.GD.N0211.N0459.d019964 _

theorem d019969 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    _root_.GD.N0232.N0719.N0976.d019735 tau u * (_root_.GD.N0211.N0459.d019966 ref h u - _root_.GD.N0232.N0719.N0976.d019734 tau u) ^ 2 ≤
      _root_.GD.N0232.N0719.N0976.d019735 tau u * (_root_.GD.N0232.N0719.N0976.d019748 ref u (h u) - _root_.GD.N0232.N0719.N0976.d019734 tau u) ^ 2 :=
  mul_le_mul_of_nonneg_left
    (_root_.GD.N0211.N0459.d019965 _ _ (_root_.GD.N0211.N0459.d019961 tau u)) (_root_.GD.N0232.N0719.N0976.d019736 tau u).le

abbrev d019970 (d : ℕ) := _root_.GD.N0232.N0720.N1341.d004414 (d + 1)

def d019971 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (x : _root_.GD.N0211.N0459.d019970 d) : ℝ :=
  _root_.GD.N0211.N0459.d019949 h (fun i => x i)

@[fun_prop] theorem d019972 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hh : Measurable h) :
    Measurable (_root_.GD.N0211.N0459.d019971 h) :=
  (_root_.GD.N0211.N0459.d019950 h hh).comp (by fun_prop)

theorem d019973 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) :
    _root_.GD.N0238.N0753.d004397 (_root_.GD.N0211.N0459.d019971 h) := by
  intro a ha x
  have heq : (fun i => (a • x) i) = _root_.GD.N0232.N0719.N0977.d009774 d 0 a (fun i => x i) := by
    funext i
    simp [_root_.GD.N0232.N0719.N0977.d009774]
  change _root_.GD.N0211.N0459.d019949 h (fun i => (a • x) i) = _
  rw [heq, _root_.GD.N0211.N0459.d019952 h 0 a ha]
  simp [_root_.GD.N0211.N0459.d019971]

def d019974 : C(_root_.GD.N0232.N0720.N1341.d004415 (d + 1), ℝ) where
  toFun u := |u.val 0| + ‖_root_.GD.N0211.N0459.d019947 (fun i => u.val i)‖
  continuous_toFun := by
    apply Continuous.add
    · fun_prop
    · exact (_root_.GD.N0211.N0459.d019948.comp (by fun_prop)).norm

theorem d019975 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hh : ∀ u, |h u| ≤ 1)
    (u : _root_.GD.N0232.N0720.N1341.d004415 (d + 1)) :
    ‖_root_.GD.N0211.N0459.d019971 h u‖ ≤ ‖(_root_.GD.N0211.N0459.d019974 : C(_root_.GD.N0232.N0720.N1341.d004415 (d + 1), ℝ))‖ := by
  calc
    _ ≤ _root_.GD.N0211.N0459.d019974 u := _root_.GD.N0211.N0459.d019959 h hh _
    _ ≤ ‖_root_.GD.N0211.N0459.d019974 u‖ := le_abs_self _
    _ ≤ _ := ContinuousMap.norm_coe_le_norm _ _

def d019976 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hm : Measurable h) (hb : ∀ u, |h u| ≤ 1) :
    _root_.GD.N0232.N0720.N1341.d004417 (d + 1) :=
  _root_.GD.N0232.N0720.N1326.d019889
    (_root_.GD.N0211.N0459.d019971 h) (_root_.GD.N0211.N0459.d019972 h hm) ‖_root_.GD.N0211.N0459.d019974‖
    (_root_.GD.N0211.N0459.d019975 h hb)

theorem d019977 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hm : Measurable h)
    (hb : ∀ u, |h u| ≤ 1) :
    _root_.GD.N0232.N0720.N1341.d004418 (_root_.GD.N0211.N0459.d019976 h hm hb) =ᵐ[volume] _root_.GD.N0211.N0459.d019971 h :=
  _root_.GD.N0232.N0720.N1326.d019891
    _ _ (_root_.GD.N0211.N0459.d019973 h) _ (_root_.GD.N0211.N0459.d019975 h hb)

theorem d019978
    (q : _root_.GD.N0232.N0720.N1316.d004440 (d + 1))
    (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hm : Measurable h) (hb : ∀ u, |h u| ≤ 1) :
    Integrable (fun x : _root_.GD.N0211.N0459.d019970 d => (_root_.GD.N0211.N0459.d019971 h x - q.1) ^ 2 *
      _root_.GD.N0232.N0720.N1316.d004445 q x) := by
  apply (_root_.GD.N0232.N0720.N1316.d004468 q
    (_root_.GD.N0211.N0459.d019976 h hm hb)).congr
  filter_upwards [_root_.GD.N0211.N0459.d019977 h hm hb] with x hx
  rw [hx]

def d019979 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hm : Measurable h) (hb : ∀ u, |h u| ≤ 1) : _root_.GD.N0232.N0720.N1341.d004417 d :=
  (MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ hb)).toLp h

theorem d019980 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hm : Measurable h) (hb : ∀ u, |h u| ≤ 1) :
    _root_.GD.N0211.N0459.d019979 h hm hb =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 d] h :=
  (MemLp.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ hb)).coeFn_toLp

def d019981 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) : C(_root_.GD.N0232.N0720.N1341.d004415 d, ℝ) where
  toFun u := Real.sqrt (_root_.GD.N0232.N0719.N0976.d019735 ref u)
  continuous_toFun := (_root_.GD.N0232.N0719.N0976.d019742 ref).continuous.sqrt

def d019982 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) : _root_.GD.N0232.N0720.N1341.d004417 d :=
  _root_.GD.N0232.N0720.N1316.d004471 (_root_.GD.N0211.N0459.d019981 ref)
    (h - ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 d) ℝ (_root_.GD.N0232.N0719.N0976.d019741 ref))

theorem d019983 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    _root_.GD.N0211.N0459.d019982 ref h =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 d]
      (fun u => Real.sqrt (_root_.GD.N0232.N0719.N0976.d019735 ref u) * (h u - _root_.GD.N0232.N0719.N0976.d019734 ref u)) := by
  filter_upwards [_root_.GD.N0232.N0720.N1316.d004472 (_root_.GD.N0211.N0459.d019981 ref)
    (h - ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 d) ℝ (_root_.GD.N0232.N0719.N0976.d019741 ref)),
    Lp.coeFn_sub h (ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 d) ℝ (_root_.GD.N0232.N0719.N0976.d019741 ref)),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (_root_.GD.N0232.N0720.N1341.d004416 d) (_root_.GD.N0232.N0719.N0976.d019741 ref)] with u hu hs hc
  unfold _root_.GD.N0211.N0459.d019982
  rw [hu, hs, Pi.sub_apply, hc]
  rfl

theorem d019984 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    (fun u => _root_.GD.N0232.N0719.N0976.d019748 ref u (_root_.GD.N0211.N0459.d019982 ref h u)) =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 d] h := by
  filter_upwards [_root_.GD.N0211.N0459.d019983 ref h] with u hu
  rw [hu]
  unfold _root_.GD.N0232.N0719.N0976.d019748
  rw [mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr (_root_.GD.N0232.N0719.N0976.d019736 ref u)).ne']
  ring

theorem d019985 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    Integrable (fun u => _root_.GD.N0232.N0719.N0976.d019745 ref tau u * h u ^ 2 -
      2 * _root_.GD.N0232.N0719.N0976.d019746 ref tau u * h u) (_root_.GD.N0232.N0720.N1341.d004416 d) := by
  have hquad := (Lp.memLp h).integrable_sq.bdd_mul
    (_root_.GD.N0232.N0719.N0976.d019745 ref tau).continuous.measurable.aestronglyMeasurable
    (ae_of_all _ (ContinuousMap.norm_coe_le_norm (_root_.GD.N0232.N0719.N0976.d019745 ref tau)))
  have hlin := ((Lp.memLp h).integrable (by norm_num)).bdd_mul
    (_root_.GD.N0232.N0719.N0976.d019746 ref tau).continuous.measurable.aestronglyMeasurable
    (ae_of_all _ (ContinuousMap.norm_coe_le_norm (_root_.GD.N0232.N0719.N0976.d019746 ref tau)))
  apply (hquad.sub (hlin.const_mul 2)).congr
  exact ae_of_all _ fun u => by
    change _root_.GD.N0232.N0719.N0976.d019745 ref tau u * h u ^ 2 - 2 * (_root_.GD.N0232.N0719.N0976.d019746 ref tau u * h u) =
      _root_.GD.N0232.N0719.N0976.d019745 ref tau u * h u ^ 2 - 2 * _root_.GD.N0232.N0719.N0976.d019746 ref tau u * h u
    ring

theorem d019986 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    _root_.GD.N0232.N0719.N0976.d019747 ref tau h = ∫ u, (_root_.GD.N0232.N0719.N0976.d019745 ref tau u * h u ^ 2 -
      2 * _root_.GD.N0232.N0719.N0976.d019746 ref tau u * h u) ∂_root_.GD.N0232.N0720.N1341.d004416 d := by
  have hquad := (Lp.memLp h).integrable_sq.mul_bdd
    (_root_.GD.N0232.N0719.N0976.d019745 ref tau).continuous.measurable.aestronglyMeasurable
    (ae_of_all _ (ContinuousMap.norm_coe_le_norm (_root_.GD.N0232.N0719.N0976.d019745 ref tau)))
  have hlin := ((Lp.memLp h).integrable (by norm_num)).mul_bdd
    (_root_.GD.N0232.N0719.N0976.d019746 ref tau).continuous.measurable.aestronglyMeasurable
    (ae_of_all _ (ContinuousMap.norm_coe_le_norm (_root_.GD.N0232.N0719.N0976.d019746 ref tau)))
  unfold _root_.GD.N0232.N0719.N0976.d019747 _root_.GD.N0232.N0720.N1314.d019689
  rw [_root_.GD.N0232.N0720.N1316.d004476, _root_.GD.N0232.N0720.N1316.d004477,
    ← integral_const_mul, ← integral_sub hquad (hlin.const_mul 2)]
  apply integral_congr_ae
  exact ae_of_all _ fun u => by ring

def d019987 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) : _root_.GD.N0232.N0720.N1341.d004417 d :=
  _root_.GD.N0211.N0459.d019982 ref (_root_.GD.N0211.N0459.d019979 (_root_.GD.N0211.N0459.d019966 ref h)
    (_root_.GD.N0211.N0459.d019967 ref h) (_root_.GD.N0211.N0459.d019968 ref h))

theorem d019988 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    (fun u => _root_.GD.N0232.N0719.N0976.d019748 ref u (_root_.GD.N0211.N0459.d019987 ref h u)) =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 d]
      _root_.GD.N0211.N0459.d019966 ref h :=
  (_root_.GD.N0211.N0459.d019984 ref _).trans (_root_.GD.N0211.N0459.d019980 _ _ _)




theorem d019989 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    _root_.GD.N0232.N0719.N0976.d019747 ref tau (_root_.GD.N0211.N0459.d019987 ref h) ≤ _root_.GD.N0232.N0719.N0976.d019747 ref tau h := by
  rw [_root_.GD.N0211.N0459.d019986, _root_.GD.N0211.N0459.d019986]
  apply integral_mono_ae (_root_.GD.N0211.N0459.d019985 _ _ _) (_root_.GD.N0211.N0459.d019985 _ _ _)
  filter_upwards [_root_.GD.N0211.N0459.d019988 ref h] with u hu
  rw [_root_.GD.N0232.N0719.N0976.d019752, _root_.GD.N0232.N0719.N0976.d019752, hu]
  exact sub_le_sub_right (_root_.GD.N0211.N0459.d019969 ref tau h u) _

abbrev d019990 (d : ℕ) := Fin (d + 2) → Ioo (0 : ℝ) 1

def d019991 (v : _root_.GD.N0211.N0459.d019990 d) : _root_.GD.N0232.N0719.N0976.d019733 d :=
  ⟨fun i => 1 / (v i : ℝ), fun i => one_div_pos.mpr (v i).property.1⟩

def d019992 (v : _root_.GD.N0211.N0459.d019990 d) :
    _root_.GD.N0232.N0720.N1316.d004440 (d + 1) := (0, v)

theorem d019993 (v : _root_.GD.N0211.N0459.d019990 d) (x : _root_.GD.N0211.N0459.d019970 d) :
    _root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0211.N0459.d019992 v) x =
      _root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0211.N0459.d019992 v) *
        Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 d (_root_.GD.N0211.N0459.d019991 v).val (fun i => x i)) := by
  unfold _root_.GD.N0232.N0720.N1316.d004445
  congr 2
  simp only [_root_.GD.N0211.N0459.d019992, sub_zero, _root_.GD.N0232.N0719.N0977.d009777, _root_.GD.N0211.N0459.d019991,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d019994 (v : _root_.GD.N0211.N0459.d019990 d)
    (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hm : Measurable h) (hb : ∀ u, |h u| ≤ 1) :
    Integrable (fun z : _root_.GD.N0232.N0719.N0977.d009764 d => _root_.GD.N0211.N0459.d019949 h z ^ 2 *
      Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 d (_root_.GD.N0211.N0459.d019991 v).val z)) := by
  have hi := _root_.GD.N0211.N0459.d019978 (_root_.GD.N0211.N0459.d019992 v) h hm hb
  have hic : Integrable (fun x : _root_.GD.N0211.N0459.d019970 d =>
      _root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0211.N0459.d019992 v) *
        (_root_.GD.N0211.N0459.d019971 h x ^ 2 *
          Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 d (_root_.GD.N0211.N0459.d019991 v).val (fun i => x i)))) := by
    apply hi.congr
    exact ae_of_all _ fun x => by
      dsimp only
      rw [_root_.GD.N0211.N0459.d019993]
      simp only [_root_.GD.N0211.N0459.d019992, sub_zero]
      ring
  have hi' := (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
    (_root_.GD.N0232.N0720.N1316.d004446 (_root_.GD.N0211.N0459.d019992 v)).ne') _).mp hic
  exact ((PiLp.volume_preserving_toLp (Fin (d + 2))).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).measurableEmbedding).mpr hi'

def d019995 (v : _root_.GD.N0211.N0459.d019990 d) (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) : ℝ :=
  ∫ z : _root_.GD.N0232.N0719.N0977.d009764 d, _root_.GD.N0211.N0459.d019949 h z ^ 2 * Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 d (_root_.GD.N0211.N0459.d019991 v).val z)

def d019996 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 d) (u : _root_.GD.N0232.N0720.N1341.d004415 d) : ℝ :=
  Real.sqrt (2 * Real.pi * (1 /
    _root_.GD.N0230.N0615.d000151 tau.val)) *
    ((1 / _root_.GD.N0230.N0615.d000151 tau.val) *
      _root_.GD.N0232.N0719.N0985.d009755 (d : ℝ) (_root_.GD.N0232.N0719.N0977.d009778 d tau.val u)) +
    _root_.GD.N0232.N0719.N0976.d019735 tau u * (_root_.GD.N0232.N0719.N0976.d019734 ref u - _root_.GD.N0232.N0719.N0976.d019734 tau u) ^ 2

def d019997 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 d) : C(_root_.GD.N0232.N0720.N1341.d004415 d, ℝ) where
  toFun := _root_.GD.N0211.N0459.d019996 ref tau
  continuous_toFun := by
    have hQ : Continuous (fun u : _root_.GD.N0232.N0720.N1341.d004415 d => _root_.GD.N0232.N0719.N0977.d009778 d tau.val u) :=
      _root_.GD.N0232.N0719.N0976.d019739.comp (continuous_const.prodMk continuous_id)
    have hiQ : Continuous (fun u : _root_.GD.N0232.N0720.N1341.d004415 d => 1 / _root_.GD.N0232.N0719.N0977.d009778 d tau.val u) :=
      continuous_const.div hQ (fun u => (_root_.GD.N0232.N0719.N0977.d009780 d tau.val tau.property u).ne')
    have hr := hiQ.rpow_const (p := ((d : ℝ) + 1) / 2)
      (fun u => Or.inl (one_div_ne_zero (_root_.GD.N0232.N0719.N0977.d009780 d tau.val tau.property u).ne'))
    unfold _root_.GD.N0211.N0459.d019996 _root_.GD.N0232.N0719.N0985.d009755
    exact (continuous_const.mul (continuous_const.mul
      ((continuous_const.mul hr).mul continuous_const))).add
        ((_root_.GD.N0232.N0719.N0976.d019742 tau).continuous.mul (((_root_.GD.N0232.N0719.N0976.d019741 ref).continuous.sub
          (_root_.GD.N0232.N0719.N0976.d019741 tau).continuous).pow 2))

theorem d019998 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 d) :
    Integrable (_root_.GD.N0211.N0459.d019996 ref tau) (_root_.GD.N0232.N0720.N1341.d004416 d) :=
  (MemLp.of_bound (_root_.GD.N0211.N0459.d019997 ref tau).continuous.measurable.aestronglyMeasurable
    ‖_root_.GD.N0211.N0459.d019997 ref tau‖ (ae_of_all _ (ContinuousMap.norm_coe_le_norm (_root_.GD.N0211.N0459.d019997 ref tau))) :
      MemLp (_root_.GD.N0211.N0459.d019996 ref tau) 1 (_root_.GD.N0232.N0720.N1341.d004416 d)).integrable le_rfl

theorem d019999 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (v : _root_.GD.N0211.N0459.d019990 d)
    (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hm : Measurable h) (hb : ∀ u, |h u| ≤ 1) :
    _root_.GD.N0211.N0459.d019995 v h =
      _root_.GD.N0232.N0719.N0976.d019747 ref (_root_.GD.N0211.N0459.d019991 v) (_root_.GD.N0211.N0459.d019982 ref (_root_.GD.N0211.N0459.d019979 h hm hb)) +
        ∫ u, _root_.GD.N0211.N0459.d019996 ref (_root_.GD.N0211.N0459.d019991 v) u ∂_root_.GD.N0232.N0720.N1341.d004416 d := by
  unfold _root_.GD.N0211.N0459.d019995
  rw [_root_.GD.N0232.N0719.N0977.d009786 d (_root_.GD.N0211.N0459.d019991 v).val
    (_root_.GD.N0211.N0459.d019991 v).property (_root_.GD.N0211.N0459.d019949 h) (_root_.GD.N0211.N0459.d019952 h)
    (_root_.GD.N0211.N0459.d019994 v h hm hb)]
  rw [_root_.GD.N0211.N0459.d019986,
    ← integral_add (_root_.GD.N0211.N0459.d019985 _ _ _) (_root_.GD.N0211.N0459.d019998 _ _)]
  apply integral_congr_ae
  filter_upwards [(_root_.GD.N0211.N0459.d019984 ref (_root_.GD.N0211.N0459.d019979 h hm hb)).trans
    (_root_.GD.N0211.N0459.d019980 h hm hb)] with u hu
  rw [_root_.GD.N0211.N0459.d019954, _root_.GD.N0232.N0719.N0976.d019752, hu]
  unfold _root_.GD.N0211.N0459.d019996 _root_.GD.N0232.N0719.N0976.d019735 _root_.GD.N0232.N0719.N0976.d019734
  ring



theorem d020000 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (v : _root_.GD.N0211.N0459.d019990 d)
    (f g : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∀ u, |f u| ≤ 1) (hgb : ∀ u, |g u| ≤ 1) :
    _root_.GD.N0211.N0459.d019995 v f ≤ _root_.GD.N0211.N0459.d019995 v g ↔
      _root_.GD.N0232.N0719.N0976.d019747 ref (_root_.GD.N0211.N0459.d019991 v) (_root_.GD.N0211.N0459.d019982 ref (_root_.GD.N0211.N0459.d019979 f hfm hfb)) ≤
        _root_.GD.N0232.N0719.N0976.d019747 ref (_root_.GD.N0211.N0459.d019991 v) (_root_.GD.N0211.N0459.d019982 ref (_root_.GD.N0211.N0459.d019979 g hgm hgb)) := by
  rw [_root_.GD.N0211.N0459.d019999, _root_.GD.N0211.N0459.d019999]
  exact add_le_add_iff_right _

theorem d020001 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (v : _root_.GD.N0211.N0459.d019990 d)
    (f g : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∀ u, |f u| ≤ 1) (hgb : ∀ u, |g u| ≤ 1) :
    _root_.GD.N0211.N0459.d019995 v f < _root_.GD.N0211.N0459.d019995 v g ↔
      _root_.GD.N0232.N0719.N0976.d019747 ref (_root_.GD.N0211.N0459.d019991 v) (_root_.GD.N0211.N0459.d019982 ref (_root_.GD.N0211.N0459.d019979 f hfm hfb)) <
        _root_.GD.N0232.N0719.N0976.d019747 ref (_root_.GD.N0211.N0459.d019991 v) (_root_.GD.N0211.N0459.d019982 ref (_root_.GD.N0211.N0459.d019979 g hgm hgb)) := by
  rw [_root_.GD.N0211.N0459.d019999, _root_.GD.N0211.N0459.d019999]
  exact add_lt_add_iff_right _





theorem d020002
    {Θ : Type*} (v : Θ → _root_.GD.N0211.N0459.d019990 d) (ref : _root_.GD.N0232.N0719.N0976.d019733 d)
    (f : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hfm : Measurable f) (hfb : ∀ u, |f u| ≤ 1)
    (hraw : ¬ ∃ g : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ, Measurable g ∧ (∀ u, |g u| ≤ 1) ∧
      (∀ q, _root_.GD.N0211.N0459.d019995 (v q) g ≤ _root_.GD.N0211.N0459.d019995 (v q) f) ∧
      ∃ q, _root_.GD.N0211.N0459.d019995 (v q) g < _root_.GD.N0211.N0459.d019995 (v q) f) :
    _root_.GD.N0230.N0556.d000031
      (fun q => _root_.GD.N0232.N0719.N0976.d019747 ref (_root_.GD.N0211.N0459.d019991 (v q)))
      (_root_.GD.N0211.N0459.d019982 ref (_root_.GD.N0211.N0459.d019979 f hfm hfb)) := by
  rintro ⟨g, hweak, q, hstrict⟩
  apply hraw
  refine ⟨_root_.GD.N0211.N0459.d019966 ref g, _root_.GD.N0211.N0459.d019967 ref g, _root_.GD.N0211.N0459.d019968 ref g, ?_, q, ?_⟩
  · intro p
    apply (_root_.GD.N0211.N0459.d020000 ref (v p) _ _ _ _ _ _).mpr
    exact (_root_.GD.N0211.N0459.d019989 ref (_root_.GD.N0211.N0459.d019991 (v p)) g).trans (hweak p)
  · apply (_root_.GD.N0211.N0459.d020001 ref (v q) _ _ _ _ _ _).mpr
    exact (_root_.GD.N0211.N0459.d019989 ref (_root_.GD.N0211.N0459.d019991 (v q)) g).trans_lt hstrict

section Physical
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0988
open _root_.GD.N0232.N0719.N0996
open _root_.GD.N0107 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0900 (d009095)

variable {k : ℕ} (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 2)

def d020003 : _root_.GD.N0232.N0719.N0997.d019804 sizes ≃ᵐ _root_.GD.N0232.N0719.N0977.d009764 d :=
  (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).trans (MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).symm

@[simp] theorem d020004 (z : _root_.GD.N0232.N0719.N0977.d009764 d) (i : Fin k) (j : Fin (sizes i)) :
    (_root_.GD.N0211.N0459.d020003 sizes hdim).symm z i j = z (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i, j⟩) := rfl

theorem d020005 (c a : ℝ) (z : _root_.GD.N0232.N0719.N0977.d009764 d) :
    (_root_.GD.N0211.N0459.d020003 sizes hdim).symm (_root_.GD.N0232.N0719.N0977.d009774 d c a z) =
      _root_.GD.N0232.N0719.N0900.d009095 k sizes c a ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm z) := by
  funext i j
  rfl

theorem d020006 (c a : ℝ) (z : _root_.GD.N0232.N0719.N0997.d019804 sizes) :
    _root_.GD.N0211.N0459.d020003 sizes hdim (_root_.GD.N0232.N0719.N0900.d009095 k sizes c a z) =
      _root_.GD.N0232.N0719.N0977.d009774 d c a (_root_.GD.N0211.N0459.d020003 sizes hdim z) := by
  apply (_root_.GD.N0211.N0459.d020003 sizes hdim).symm.injective
  rw [MeasurableEquiv.symm_apply_apply, _root_.GD.N0211.N0459.d020005,
    MeasurableEquiv.symm_apply_apply]

def d020007 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (z : _root_.GD.N0232.N0719.N0997.d019804 sizes) : ℝ :=
  _root_.GD.N0211.N0459.d019949 h (_root_.GD.N0211.N0459.d020003 sizes hdim z)

@[fun_prop] theorem d020008 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hm : Measurable h) :
    Measurable (_root_.GD.N0211.N0459.d020007 sizes hdim h) :=
  (_root_.GD.N0211.N0459.d019950 h hm).comp (_root_.GD.N0211.N0459.d020003 sizes hdim).measurable

theorem d020009 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (c a : ℝ) (ha : 0 < a)
    (z : _root_.GD.N0232.N0719.N0997.d019804 sizes) :
    _root_.GD.N0211.N0459.d020007 sizes hdim h (_root_.GD.N0232.N0719.N0900.d009095 k sizes c a z) =
      c + a * _root_.GD.N0211.N0459.d020007 sizes hdim h z := by
  unfold _root_.GD.N0211.N0459.d020007
  rw [_root_.GD.N0211.N0459.d020006, _root_.GD.N0211.N0459.d019952 h c a ha]

abbrev d020010 (k : ℕ) := Fin k → Ioo (0 : ℝ) 1

def d020011 (v : _root_.GD.N0211.N0459.d020010 k) : _root_.GD.N0211.N0459.d019990 d :=
  fun j => v (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim j)

def d020012 (v : _root_.GD.N0211.N0459.d020010 k) : _root_.GD.N0232.N0719.N0976.d019733 d :=
  _root_.GD.N0211.N0459.d019991 (_root_.GD.N0211.N0459.d020011 sizes hdim v)

@[fun_prop] theorem d020013 :
    Continuous (_root_.GD.N0211.N0459.d020012 sizes hdim) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact continuous_const.div (((continuous_apply (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim j))).subtype_val)
    (fun v => (v (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim j)).property.1.ne')

def d020014 : _root_.GD.N0211.N0459.d020010 k := fun _ => ⟨1 / 2, by constructor <;> norm_num⟩

def d020015 (v : _root_.GD.N0211.N0459.d020010 k) : _root_.GD.N0232.N0719.N0859.d010809 k :=
  _root_.GD.N0232.N0719.N0996.d019935 (0, v)

theorem d020016 (v : _root_.GD.N0211.N0459.d019990 d) (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) :
    (∫ x : _root_.GD.N0211.N0459.d019970 d, _root_.GD.N0211.N0459.d019971 h x ^ 2 *
      _root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0211.N0459.d019992 v) x) =
      _root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0211.N0459.d019992 v) *
        _root_.GD.N0211.N0459.d019995 v h := by
  simp_rw [_root_.GD.N0211.N0459.d019993]
  rw [show (fun x : _root_.GD.N0211.N0459.d019970 d => _root_.GD.N0211.N0459.d019971 h x ^ 2 *
      (_root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0211.N0459.d019992 v) *
        Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 d (_root_.GD.N0211.N0459.d019991 v).val (fun i => x i)))) =
      (fun x => _root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0211.N0459.d019992 v) *
        (_root_.GD.N0211.N0459.d019971 h x ^ 2 *
          Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 d (_root_.GD.N0211.N0459.d019991 v).val (fun i => x i)))) by
      funext x; ring, integral_const_mul]
  congr 1
  exact ((PiLp.volume_preserving_toLp (Fin (d + 2))).integral_comp
    (MeasurableEquiv.toLp 2 (Fin (d + 2) → ℝ)).measurableEmbedding _).symm

theorem d020017 (v : _root_.GD.N0211.N0459.d020010 k) (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ)
    (hm : Measurable h) (hb : ∀ u, |h u| ≤ 1) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0211.N0459.d020015 v) (_root_.GD.N0211.N0459.d020007 sizes hdim h) =
      ENNReal.ofReal
        (_root_.GD.N0232.N0720.N1316.d004443
          (_root_.GD.N0211.N0459.d019992 (_root_.GD.N0211.N0459.d020011 sizes hdim v)) *
            _root_.GD.N0211.N0459.d019995 (_root_.GD.N0211.N0459.d020011 sizes hdim v) h) := by
  have hmeas := _root_.GD.N0211.N0459.d019972 h hm
  change (∫⁻ z, ENNReal.ofReal ((_root_.GD.N0211.N0459.d019971 h (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim z) - (0 : ℝ)) ^ 2)
    ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (_root_.GD.N0232.N0719.N0997.d019811 (0, v))) = _
  rw [_root_.GD.N0232.N0719.N0997.d019815 sizes hdim (0, v) _ hmeas]
  rw [lintegral_withDensity_eq_lintegral_mul _ (by
    unfold _root_.GD.N0232.N0720.N1316.d004445
    fun_prop) (by fun_prop)]
  rw [← _root_.GD.N0211.N0459.d020016]
  have hi := _root_.GD.N0211.N0459.d019978 (_root_.GD.N0211.N0459.d019992 (_root_.GD.N0211.N0459.d020011 sizes hdim v)) h hm hb
  simp only [_root_.GD.N0211.N0459.d019992, sub_zero] at hi ⊢
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x =>
    mul_nonneg (sq_nonneg _) (mul_nonneg
      (_root_.GD.N0232.N0720.N1316.d004446 _).le (Real.exp_pos _).le))]
  apply lintegral_congr
  intro x
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (show 0 ≤
    _root_.GD.N0232.N0720.N1316.d004445
      (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (0, v)) x from
        mul_nonneg (_root_.GD.N0232.N0720.N1316.d004446 _).le
          (Real.exp_pos _).le), mul_comm]
  rfl

theorem d020018 (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hm : Measurable h)
    (mu : ℝ) (sigma : Fin k → ℝ) (b a : ℝ) (ha : 0 < a) :
    (∫⁻ z, ENNReal.ofReal ((_root_.GD.N0211.N0459.d020007 sizes hdim h z - (b + a * mu)) ^ 2)
      ∂_root_.GD.N0232.N0719.d009176 k sizes (b + a * mu) (fun i => a * sigma i)) =
      ENNReal.ofReal (a ^ 2) *
        ∫⁻ z, ENNReal.ofReal ((_root_.GD.N0211.N0459.d020007 sizes hdim h z - mu) ^ 2)
          ∂_root_.GD.N0232.N0719.d009176 k sizes mu sigma := by
  rw [← _root_.GD.N0232.N0719.d009188 k sizes b a mu sigma,
    lintegral_map (by fun_prop) (by fun_prop)]
  simp_rw [_root_.GD.N0211.N0459.d020009 sizes hdim h b a ha,
    show ∀ x : ℝ, b + a * x - (b + a * mu) = a * (x - mu) by intro x; ring,
    mul_pow, ENNReal.ofReal_mul (sq_nonneg a)]
  exact lintegral_const_mul _ (by fun_prop)

theorem d020019 (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) (hm : Measurable h) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0211.N0459.d020007 sizes hdim h) =
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0988.d019796 theta.scale ^ 2) *
        _root_.GD.N0232.N0719.N0859.d010840 k sizes
          (_root_.GD.N0211.N0459.d020015 (_root_.GD.N0232.N0719.N0988.d019799 0 theta.scale theta.scale_pos).2)
          (_root_.GD.N0211.N0459.d020007 sizes hdim h) := by
  let q := _root_.GD.N0232.N0719.N0988.d019799 0 theta.scale theta.scale_pos
  have hloc : q.1 = 0 := by simp [q, _root_.GD.N0232.N0719.N0988.d019799]
  have hscale : (fun i => _root_.GD.N0232.N0719.N0988.d019796 theta.scale * _root_.GD.N0232.N0719.N0997.d019811 (0, q.2) i) = theta.scale := by
    funext i
    exact _root_.GD.N0232.N0719.N0988.d019802 0 theta.scale theta.scale_pos i
  have hr := _root_.GD.N0211.N0459.d020018 sizes hdim h hm 0 (_root_.GD.N0232.N0719.N0997.d019811 (0, q.2))
    theta.location (_root_.GD.N0232.N0719.N0988.d019796 theta.scale) (_root_.GD.N0232.N0719.N0988.d019797 theta.scale)
  simp only [mul_zero, add_zero, hscale] at hr
  exact hr

theorem d020020 (v : _root_.GD.N0211.N0459.d019990 d) (h : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ) :
    0 ≤ _root_.GD.N0211.N0459.d019995 v h :=
  integral_nonneg fun _z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem d020021 (f g : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ)
    (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∀ u, |f u| ≤ 1) (hgb : ∀ u, |g u| ≤ 1)
    (hweak : ∀ v : _root_.GD.N0211.N0459.d020010 k,
      _root_.GD.N0211.N0459.d019995 (_root_.GD.N0211.N0459.d020011 sizes hdim v) f ≤
        _root_.GD.N0211.N0459.d019995 (_root_.GD.N0211.N0459.d020011 sizes hdim v) g)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0211.N0459.d020007 sizes hdim f) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0211.N0459.d020007 sizes hdim g) := by
  rw [_root_.GD.N0211.N0459.d020019 sizes hdim theta f hfm,
    _root_.GD.N0211.N0459.d020019 sizes hdim theta g hgm,
    _root_.GD.N0211.N0459.d020017 sizes hdim _ f hfm hfb,
    _root_.GD.N0211.N0459.d020017 sizes hdim _ g hgm hgb]
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (hweak _)
    (_root_.GD.N0232.N0720.N1316.d004446 _).le

theorem d020022 (f g : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ)
    (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∀ u, |f u| ≤ 1) (hgb : ∀ u, |g u| ≤ 1) (v : _root_.GD.N0211.N0459.d020010 k)
    (hstrict : _root_.GD.N0211.N0459.d019995 (_root_.GD.N0211.N0459.d020011 sizes hdim v) f <
      _root_.GD.N0211.N0459.d019995 (_root_.GD.N0211.N0459.d020011 sizes hdim v) g) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0211.N0459.d020015 v) (_root_.GD.N0211.N0459.d020007 sizes hdim f) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0211.N0459.d020015 v) (_root_.GD.N0211.N0459.d020007 sizes hdim g) := by
  rw [_root_.GD.N0211.N0459.d020017 sizes hdim _ f hfm hfb,
    _root_.GD.N0211.N0459.d020017 sizes hdim _ g hgm hgb]
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg
    (_root_.GD.N0232.N0720.N1316.d004446 _).le
    (_root_.GD.N0211.N0459.d020020 _ _))).mpr
  exact mul_lt_mul_of_pos_left hstrict
    (_root_.GD.N0232.N0720.N1316.d004446 _)

theorem d020023 {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ}
    (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    _root_.GD.N0232.N0719.N0977.d009783 d (s ∘ (_root_.GD.N0211.N0459.d020003 sizes hdim).symm) := by
  intro c a ha z
  let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨c, Real.log a⟩
  have hinput : g • ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm z) =
      _root_.GD.N0232.N0719.N0900.d009095 k sizes c a ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm z) := by
    funext i j
    change c + Real.exp (Real.log a) * _ = c + a * _
    rw [Real.exp_log ha]
  have he := hs.2.1 g ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm z)
  change s (g • ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm z)) =
    g • s ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm z) at he
  rw [hinput] at he
  simpa only [Function.comp_apply, _root_.GD.N0211.N0459.d020005,
    _root_.GD.N0232.N0719.N0946.d009229.d009244, g,
    _root_.GD.N0232.N0719.N0946.d009229.d009239, Real.exp_log ha] using he





theorem d020024
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s)
    (hbound : ∀ u : _root_.GD.N0232.N0720.N1341.d004415 d,
      |s ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm (_root_.GD.N0232.N0719.N0977.d009773 d u))| ≤ 1) :
    ∃ h : _root_.GD.N0232.N0720.N1341.d004417 d,
      _root_.GD.N0230.N0556.d000031
        (fun v : _root_.GD.N0211.N0459.d020010 k => _root_.GD.N0232.N0719.N0976.d019747
          (_root_.GD.N0211.N0459.d020012 sizes hdim _root_.GD.N0211.N0459.d020014) (_root_.GD.N0211.N0459.d020012 sizes hdim v)) h ∧
      (∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, _root_.GD.N0232.N0719.N0976.d019748
        (_root_.GD.N0211.N0459.d020012 sizes hdim _root_.GD.N0211.N0459.d020014) u (h u) =
          s ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm (_root_.GD.N0232.N0719.N0977.d009773 d u))) := by
  let f : _root_.GD.N0232.N0720.N1341.d004415 d → ℝ := fun u => s ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm (_root_.GD.N0232.N0719.N0977.d009773 d u))
  have hfm : Measurable f := hs.1.comp
    ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm.measurable.comp _root_.GD.N0232.N0719.N0976.d019737.measurable)
  let ref := _root_.GD.N0211.N0459.d020012 sizes hdim _root_.GD.N0211.N0459.d020014
  refine ⟨_root_.GD.N0211.N0459.d019982 ref (_root_.GD.N0211.N0459.d019979 f hfm hbound), ?_,
    (_root_.GD.N0211.N0459.d019984 ref _).trans (_root_.GD.N0211.N0459.d019980 f hfm hbound)⟩
  have hrep : _root_.GD.N0211.N0459.d020007 sizes hdim f = s := by
    have he := _root_.GD.N0211.N0459.d019957 _ (_root_.GD.N0211.N0459.d020023 sizes hdim hs)
    change _root_.GD.N0211.N0459.d019949 f = s ∘ (_root_.GD.N0211.N0459.d020003 sizes hdim).symm at he
    funext z
    change _root_.GD.N0211.N0459.d019949 f (_root_.GD.N0211.N0459.d020003 sizes hdim z) = s z
    rw [he]
    simp
  apply _root_.GD.N0211.N0459.d020002
    (_root_.GD.N0211.N0459.d020011 sizes hdim) ref f hfm hbound
  rintro ⟨g, hgm, hgb, hweak, v, hstrict⟩
  have hdom := _root_.GD.N0211.N0459.d020021 sizes hdim g f hgm hfm hgb hbound hweak
  have hlt := _root_.GD.N0211.N0459.d020022 sizes hdim g f hgm hfm hgb hbound v hstrict
  rw [hrep] at hdom hlt
  have heq := hs.2.2.2 (_root_.GD.N0211.N0459.d020007 sizes hdim g) (_root_.GD.N0211.N0459.d020008 sizes hdim g hgm) hdom
    (_root_.GD.N0211.N0459.d020015 v)
  rw [_root_.GD.N0232.N0719.N0896.d011094 k sizes (_root_.GD.N0211.N0459.d020015 v) heq] at hlt
  exact lt_irrefl _ hlt

end Physical

end
end GD.N0211.N0459

#print axioms _root_.GD.N0211.N0459.d019957
#print axioms _root_.GD.N0211.N0459.d019969
#print axioms _root_.GD.N0211.N0459.d019989
#print axioms _root_.GD.N0211.N0459.d019999
#print axioms _root_.GD.N0211.N0459.d020024
