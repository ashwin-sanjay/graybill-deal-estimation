import GD.Module0804










set_option autoImplicit false
set_option warningAsError true

open Filter MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0232.N0719.N0843

noncomputable section

open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0961
open _root_.GD.N0230.N0602 _root_.GD.N0230.N0633
open _root_.GD.N0230.N0709
open _root_.GD.N0230.N0710
open _root_.GD.N0230.N0664
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229


structure d012215 (k : ℕ) where
  value : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ
  positive : ∀ theta, 0 < value theta
  character : ∀ (g : _root_.GD.N0232.N0719.N0946.d009229) theta,
    value (_root_.GD.N0232.N0719.N0896.d011104 k g theta) = g.d009239 ^ 2 * value theta

variable (k : ℕ) (sizes : Fin k → ℕ) (γ : _root_.GD.N0232.N0719.N0843.d012215 k)


def d012216 (C : ℝ) : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :=
  {p | ∀ theta, _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p ≤ ENNReal.ofReal (C * γ.value theta)}

theorem d012217 (C : ℝ) : IsClosed (_root_.GD.N0232.N0719.N0843.d012216 k sizes γ C) := by
  simpa [_root_.GD.N0232.N0719.N0843.d012216, _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes) (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun theta ↦ ENNReal.ofReal (C * γ.value theta))
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes))

theorem d012218 (C : ℝ) : Convex ℝ (_root_.GD.N0232.N0719.N0843.d012216 k sizes γ C) := by
  simpa [_root_.GD.N0232.N0719.N0843.d012216, _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes) (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun theta ↦ ENNReal.ofReal (C * γ.value theta))
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes))

theorem d012219 {C : ℝ}
    {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)} (hp : p ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C) :
    _root_.GD.N0232.N0719.N0896.d011103 k sizes p := by
  intro theta
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hp theta)

theorem d012220 {C : ℝ} (hC : 0 ≤ C)
    {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)} (hp : p ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C) :
    ‖p‖ ^ 2 ≤ C * γ.value (_root_.GD.N0232.N0719.N0859.d010810 k) := by
  have href := hp (_root_.GD.N0232.N0719.N0859.d010810 k)
  rw [_root_.GD.N0232.N0719.N0859.d010829 k sizes] at href
  simp only [zero_sub, norm_neg] at href
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC ((γ.positive (_root_.GD.N0232.N0719.N0859.d010810 k)).le))).mp href

theorem d012221 {C : ℝ} (hC : 0 ≤ C)
    {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)} (hp : p ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C) :
    ‖p‖ ≤ Real.sqrt (C * γ.value (_root_.GD.N0232.N0719.N0859.d010810 k)) := by
  have hs := Real.sq_sqrt
    (mul_nonneg hC ((γ.positive (_root_.GD.N0232.N0719.N0859.d010810 k)).le))
  have hb := _root_.GD.N0232.N0719.N0843.d012220 k sizes γ hC hp
  nlinarith [norm_nonneg p,
    Real.sqrt_nonneg (C * γ.value (_root_.GD.N0232.N0719.N0859.d010810 k))]


def d012222 (C : ℝ) : Set (WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))) :=
  toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) '' _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C

theorem d012223 {C : ℝ} (hC : 0 ≤ C) :
    IsCompact (_root_.GD.N0232.N0719.N0843.d012222 k sizes γ C) := by
  exact _root_.GD.N0230.N0633.d001201
    (Real.sqrt (C * γ.value (_root_.GD.N0232.N0719.N0859.d010810 k)))
    (_root_.GD.N0232.N0719.N0843.d012218 k sizes γ C) (_root_.GD.N0232.N0719.N0843.d012217 k sizes γ C)
    (fun p hp ↦ _root_.GD.N0232.N0719.N0843.d012221 k sizes γ hC hp)

theorem d012224 (C : ℝ) : Convex ℝ (_root_.GD.N0232.N0719.N0843.d012222 k sizes γ C) := by
  exact (_root_.GD.N0232.N0719.N0843.d012218 k sizes γ C).linear_image (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))).toLinearMap

theorem d012225 (C : ℝ)
    (p : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))) :
    p ∈ _root_.GD.N0232.N0719.N0843.d012222 k sizes γ C ↔
      (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))).symm p ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro hp
    exact ⟨_, hp, by simp⟩

theorem d012226 {C : ℝ} (_hC : 0 ≤ C)
    (g : _root_.GD.N0232.N0719.N0946.d009229) {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)}
    (hp : p ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C) :
    _root_.GD.N0232.N0719.N0896.d011109 k sizes g p (_root_.GD.N0232.N0719.N0843.d012219 k sizes γ hp) ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C := by
  intro eta
  let theta := _root_.GD.N0232.N0719.N0845.d010881
    (_root_.GD.N0232.N0719.N0842.d010906 g.shift g.d009239) g.d009239⁻¹ (inv_pos.mpr g.d009240) eta
  have heta : _root_.GD.N0232.N0719.N0896.d011104 k g theta = eta :=
    _root_.GD.N0232.N0719.N0842.d010919 g.shift g.d009239 g.d009240 eta
  rw [← heta, _root_.GD.N0232.N0719.N0896.d011110, γ.character]
  calc
    ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p ≤
        ENNReal.ofReal (g.d009239 ^ 2) *
          ENNReal.ofReal (C * γ.value theta) := mul_le_mul' le_rfl (hp theta)
    _ = ENNReal.ofReal (C * (g.d009239 ^ 2 * γ.value theta)) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg g.d009239)]
      congr 1
      ring


def d012227 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) : _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C → _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C :=
  fun p ↦ ⟨_root_.GD.N0232.N0719.N0896.d011109 k sizes g p.1 (_root_.GD.N0232.N0719.N0843.d012219 k sizes γ p.2),
    _root_.GD.N0232.N0719.N0843.d012226 k sizes γ hC g p.2⟩

theorem d012228 (C : ℝ) (hC : 0 ≤ C) (p : _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C) :
    _root_.GD.N0232.N0719.N0843.d012227 k sizes γ C hC 1 p = p := by
  apply Subtype.ext
  exact _root_.GD.N0232.N0719.N0963.d012158 k sizes
    p.1 (_root_.GD.N0232.N0719.N0843.d012219 k sizes γ p.2)

theorem d012229 (C : ℝ) (hC : 0 ≤ C) (g h : _root_.GD.N0232.N0719.N0946.d009229) (p : _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C) :
    _root_.GD.N0232.N0719.N0843.d012227 k sizes γ C hC g (_root_.GD.N0232.N0719.N0843.d012227 k sizes γ C hC h p) = _root_.GD.N0232.N0719.N0843.d012227 k sizes γ C hC (g * h) p := by
  apply Subtype.ext
  exact _root_.GD.N0232.N0719.N0963.d012160 k sizes
    g h p.1 (_root_.GD.N0232.N0719.N0843.d012219 k sizes γ p.2)


def d012230 (C : ℝ) : _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C ≃ _root_.GD.N0232.N0719.N0843.d012222 k sizes γ C where
  toFun p := ⟨toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) p.1, ⟨p.1, p.2, rfl⟩⟩
  invFun p := ⟨(toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))).symm p.1,
    (_root_.GD.N0232.N0719.N0843.d012225 k sizes γ C p.1).mp p.2⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp

def d012231 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0719.N0843.d012222 k sizes γ C → _root_.GD.N0232.N0719.N0843.d012222 k sizes γ C :=
  fun p ↦ _root_.GD.N0232.N0719.N0843.d012230 k sizes γ C (_root_.GD.N0232.N0719.N0843.d012227 k sizes γ C hC g ((_root_.GD.N0232.N0719.N0843.d012230 k sizes γ C).symm p))



theorem d012232 (C : ℝ)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
      ENNReal.ofReal (C * γ.value theta)) :
    ∃ p ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C, ∀ theta, _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p = _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d := by
  have hdLp : MemLp d 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    _root_.GD.N0232.N0719.N0896.d011095 k sizes d hd
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound (_root_.GD.N0232.N0719.N0859.d010810 k)))
  refine ⟨hdLp.toLp d, ?_, ?_⟩
  · intro theta
    rw [← _root_.GD.N0232.N0719.N0859.d010841 k sizes theta d hdLp]
    exact hbound theta
  · intro theta
    exact (_root_.GD.N0232.N0719.N0859.d010841 k sizes theta d hdLp).symm


def d012233 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (x : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))) :
    WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) := by
  classical
  exact if hx : x ∈ _root_.GD.N0232.N0719.N0843.d012222 k sizes γ C then
    (_root_.GD.N0232.N0719.N0843.d012231 k sizes γ C hC g ⟨x, hx⟩).1 else x

theorem d012234 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0232.N0719.N0843.d012222 k sizes γ C) :
    _root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC g p.1 = (_root_.GD.N0232.N0719.N0843.d012231 k sizes γ C hC g p).1 := by
  simp [_root_.GD.N0232.N0719.N0843.d012233, p.2]

theorem d012235 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (x : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)))
    (hx : x ∈ _root_.GD.N0232.N0719.N0843.d012222 k sizes γ C) :
    _root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC g x = toWeakSpace ℝ _
      (_root_.GD.N0232.N0719.N0896.d011109 k sizes g ((toWeakSpace ℝ _).symm x)
        (_root_.GD.N0232.N0719.N0843.d012219 k sizes γ ((_root_.GD.N0232.N0719.N0843.d012225 k sizes γ C x).mp hx))) := by
  simp [_root_.GD.N0232.N0719.N0843.d012233, hx, _root_.GD.N0232.N0719.N0843.d012231, _root_.GD.N0232.N0719.N0843.d012230, _root_.GD.N0232.N0719.N0843.d012227]

theorem d012236 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    MapsTo (_root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC g) (_root_.GD.N0232.N0719.N0843.d012222 k sizes γ C) (_root_.GD.N0232.N0719.N0843.d012222 k sizes γ C) := by
  intro x hx
  rw [show _root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC g x =
      (_root_.GD.N0232.N0719.N0843.d012231 k sizes γ C hC g ⟨x, hx⟩).1 from
        _root_.GD.N0232.N0719.N0843.d012234 k sizes γ C hC g ⟨x, hx⟩]
  exact (_root_.GD.N0232.N0719.N0843.d012231 k sizes γ C hC g ⟨x, hx⟩).2

theorem d012237 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    Continuous (_root_.GD.N0232.N0719.N0843.d012231 k sizes γ C hC g) := by
  apply _root_.GD.N0232.N0719.N0961.d012140 k sizes (_root_.GD.N0232.N0719.N0843.d012222 k sizes γ C) (_root_.GD.N0232.N0719.N0843.d012223 k sizes γ hC)
    (fun x hx ↦ _root_.GD.N0232.N0719.N0843.d012219 k sizes γ ((_root_.GD.N0232.N0719.N0843.d012225 k sizes γ C x).mp hx)) g
  intro p
  rfl

theorem d012238 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    ContinuousOn (_root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC g) (_root_.GD.N0232.N0719.N0843.d012222 k sizes γ C) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hc := continuous_subtype_val.comp (_root_.GD.N0232.N0719.N0843.d012237 k sizes γ C hC g)
  convert hc using 1
  funext p
  exact _root_.GD.N0232.N0719.N0843.d012234 k sizes γ C hC g p

theorem d012239 (C : ℝ) (hC : 0 ≤ C) (g h : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0232.N0719.N0843.d012222 k sizes γ C) :
    _root_.GD.N0232.N0719.N0843.d012231 k sizes γ C hC g (_root_.GD.N0232.N0719.N0843.d012231 k sizes γ C hC h p) =
      _root_.GD.N0232.N0719.N0843.d012231 k sizes γ C hC (g * h) p := by
  simp only [_root_.GD.N0232.N0719.N0843.d012231, Equiv.symm_apply_apply, _root_.GD.N0232.N0719.N0843.d012229]

theorem d012240 (C : ℝ) (hC : 0 ≤ C) (g h : _root_.GD.N0232.N0719.N0946.d009229)
    (x : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)))
    (hx : x ∈ _root_.GD.N0232.N0719.N0843.d012222 k sizes γ C) :
    _root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC g (_root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC h x) =
      _root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC (g * h) x := by
  let p : _root_.GD.N0232.N0719.N0843.d012222 k sizes γ C := ⟨x, hx⟩
  change _root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC g (_root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC h p.1) =
    _root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC (g * h) p.1
  simp only [_root_.GD.N0232.N0719.N0843.d012234]
  exact congrArg Subtype.val (_root_.GD.N0232.N0719.N0843.d012239 k sizes γ C hC g h p)

theorem d012241
    (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0230.N0710.d001232 (_root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC g) (_root_.GD.N0232.N0719.N0843.d012222 k sizes γ C) := by
  intro x hx y hy a b ha hb hab
  have hxy := _root_.GD.N0232.N0719.N0843.d012224 k sizes γ C hx hy ha hb hab
  rw [_root_.GD.N0232.N0719.N0843.d012235 k sizes γ C hC g _ hxy,
    _root_.GD.N0232.N0719.N0843.d012235 k sizes γ C hC g x hx,
    _root_.GD.N0232.N0719.N0843.d012235 k sizes γ C hC g y hy]
  have h := _root_.GD.N0232.N0719.N0963.d012168 k sizes g
    ((toWeakSpace ℝ _).symm x) ((toWeakSpace ℝ _).symm y)
    (_root_.GD.N0232.N0719.N0843.d012219 k sizes γ ((_root_.GD.N0232.N0719.N0843.d012225 k sizes γ C x).mp hx))
    (_root_.GD.N0232.N0719.N0843.d012219 k sizes γ ((_root_.GD.N0232.N0719.N0843.d012225 k sizes γ C y).mp hy)) hab
    (_root_.GD.N0232.N0719.N0843.d012219 k sizes γ (_root_.GD.N0232.N0719.N0843.d012218 k sizes γ C
      ((_root_.GD.N0232.N0719.N0843.d012225 k sizes γ C x).mp hx)
      ((_root_.GD.N0232.N0719.N0843.d012225 k sizes γ C y).mp hy) ha hb hab))
  simpa only [map_add, map_smul] using congrArg (toWeakSpace ℝ _) h

theorem d012242 (C : ℝ) (hC : 0 ≤ C) :
    _root_.GD.N0230.N0709.d001221 (_root_.GD.N0232.N0719.N0843.d012222 k sizes γ C) := by
  apply (Metric.isBounded_closedBall (x := (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)))
    (r := Real.sqrt (C * γ.value (_root_.GD.N0232.N0719.N0859.d010810 k)))).subset
  rintro p ⟨x, hx, rfl⟩
  have hb := _root_.GD.N0232.N0719.N0843.d012221 k sizes γ hC ((_root_.GD.N0232.N0719.N0843.d012225 k sizes γ C x).mp hx)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hb


theorem d012243
    (C : ℝ) (hC : 0 ≤ C)
    (hne : (_root_.GD.N0232.N0719.N0843.d012216 k sizes γ C).Nonempty) :
    ∃ p, ∃ hp : p ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C,
      ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
        _root_.GD.N0232.N0719.N0896.d011109 k sizes g p (_root_.GD.N0232.N0719.N0843.d012219 k sizes γ hp) = p := by
  obtain ⟨x, hx, hfix⟩ := _root_.GD.N0230.N0664.d001257
    (fun b r ↦ _root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC ⟨b, r⟩) (_root_.GD.N0232.N0719.N0843.d012222 k sizes γ C)
    (_root_.GD.N0232.N0719.N0843.d012223 k sizes γ hC) (_root_.GD.N0232.N0719.N0843.d012224 k sizes γ C)
    (hne.image (toWeakSpace ℝ _)) (_root_.GD.N0232.N0719.N0843.d012242 k sizes γ C hC)
    (fun b r ↦ _root_.GD.N0232.N0719.N0843.d012236 k sizes γ C hC ⟨b, r⟩)
    (fun b r ↦ _root_.GD.N0232.N0719.N0843.d012238 k sizes γ C hC ⟨b, r⟩)
    (fun b r ↦ _root_.GD.N0232.N0719.N0843.d012241 k sizes γ C hC ⟨b, r⟩)
    (fun b r c s x hx ↦ _root_.GD.N0232.N0719.N0843.d012240 k sizes γ C hC ⟨b, r⟩ ⟨c, s⟩ x hx)
  refine ⟨(toWeakSpace ℝ _).symm x, (_root_.GD.N0232.N0719.N0843.d012225 k sizes γ C x).mp hx, ?_⟩
  intro g
  have hg : _root_.GD.N0232.N0719.N0843.d012233 k sizes γ C hC g x = x := by
    cases g with
    | mk b r => exact hfix b r
  rw [_root_.GD.N0232.N0719.N0843.d012235 k sizes γ C hC g x hx] at hg
  exact (toWeakSpace ℝ _).injective (hg.trans (by simp))



theorem d012244
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (C : ℝ) (hC : 0 ≤ C)
    (hne : (_root_.GD.N0232.N0719.N0843.d012216 k sizes γ C).Nonempty) :
    ∃ e : _root_.GD.N0232.N0719.d009173 k sizes → ℝ,
      Measurable e ∧
      (∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ omega, e (g • omega) = g • e omega) ∧
      ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤
        ENNReal.ofReal (C * γ.value theta) := by
  obtain ⟨p, hp, hfix⟩ := _root_.GD.N0232.N0719.N0843.d012243 k sizes γ C hC hne
  obtain ⟨e, he, heae, hequiv⟩ :=
    _root_.GD.N0232.N0719.N0896.d011125 k sizes hk hsizes p
      (_root_.GD.N0232.N0719.N0843.d012219 k sizes γ hp) hfix
  refine ⟨e, he, hequiv, ?_⟩
  intro theta
  rw [_root_.GD.N0232.N0719.N0896.d011094 k sizes theta (heae theta), _root_.GD.N0232.N0719.N0896.d011093]
  exact hp theta



theorem d012245
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (C : ℝ) (hC : 0 ≤ C)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
      ENNReal.ofReal (C * γ.value theta)) :
    ∃ e : _root_.GD.N0232.N0719.d009173 k sizes → ℝ,
      Measurable e ∧
      (∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ omega, e (g • omega) = g • e omega) ∧
      ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤
        ENNReal.ofReal (C * γ.value theta) := by
  obtain ⟨p, hp, _⟩ := _root_.GD.N0232.N0719.N0843.d012232 k sizes γ C d hd hbound
  exact _root_.GD.N0232.N0719.N0843.d012244 k sizes γ hk hsizes C hC ⟨p, hp⟩

end
end GD.N0232.N0719.N0843

#print axioms _root_.GD.N0232.N0719.N0843.d012223
#print axioms _root_.GD.N0232.N0719.N0843.d012245
