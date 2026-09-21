import GD.Module0091
import GD.Module0798
import GD.Module0744















set_option autoImplicit false
set_option warningAsError true

open Filter MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0232.N0719.N0963

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0633
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (k : ℕ) (sizes : Fin k → ℕ)


def d012141 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  _root_.GD.N0232.N0719.N0838.d012097 sizes theta

theorem d012142 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 ≤ _root_.GD.N0232.N0719.N0963.d012141 k sizes theta := by
  unfold _root_.GD.N0232.N0719.N0963.d012141 _root_.GD.N0232.N0719.N0838.d012097
    _root_.GD.N0232.N0719.N0838.d012096
  positivity

theorem d012143 (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0963.d012141 k sizes theta :=
  _root_.GD.N0232.N0719.N0838.d012099 hk sizes hsizes theta

@[simp] theorem d012144 :
    _root_.GD.N0232.N0719.N0963.d012141 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) = (∑ i, (sizes i : ℝ))⁻¹ := by
  simp [_root_.GD.N0232.N0719.N0963.d012141, _root_.GD.N0232.N0719.N0838.d012097,
    _root_.GD.N0232.N0719.N0838.d012096, _root_.GD.N0232.N0719.N0859.d010810]

theorem d012145 (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0963.d012141 k sizes (_root_.GD.N0232.N0719.N0896.d011104 k g theta) =
      g.d009239 ^ 2 * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta := by
  unfold _root_.GD.N0232.N0719.N0963.d012141 _root_.GD.N0232.N0719.N0838.d012097 _root_.GD.N0232.N0719.N0896.d011104
  rw [_root_.GD.N0232.N0719.N0838.d012100]
  simp only [mul_inv_rev, inv_inv]
  ring


def d012146 (C : ℝ) : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :=
  {p | ∀ theta, _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta)}

theorem d012147 (C : ℝ) : IsClosed (_root_.GD.N0232.N0719.N0963.d012146 k sizes C) := by
  simpa [_root_.GD.N0232.N0719.N0963.d012146, _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes) (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun theta ↦ ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta))
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes))

theorem d012148 (C : ℝ) : Convex ℝ (_root_.GD.N0232.N0719.N0963.d012146 k sizes C) := by
  simpa [_root_.GD.N0232.N0719.N0963.d012146, _root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes) (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
      (fun theta ↦ ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta))
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes))

theorem d012149 {C : ℝ}
    {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)} (hp : p ∈ _root_.GD.N0232.N0719.N0963.d012146 k sizes C) :
    _root_.GD.N0232.N0719.N0896.d011103 k sizes p := by
  intro theta
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hp theta)

theorem d012150 {C : ℝ} (hC : 0 ≤ C)
    {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)} (hp : p ∈ _root_.GD.N0232.N0719.N0963.d012146 k sizes C) :
    ‖p‖ ^ 2 ≤ C * _root_.GD.N0232.N0719.N0963.d012141 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) := by
  have href := hp (_root_.GD.N0232.N0719.N0859.d010810 k)
  rw [_root_.GD.N0232.N0719.N0859.d010829 k sizes] at href
  simp only [zero_sub, norm_neg] at href
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (_root_.GD.N0232.N0719.N0963.d012142 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)))).mp href

theorem d012151 {C : ℝ} (hC : 0 ≤ C)
    {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)} (hp : p ∈ _root_.GD.N0232.N0719.N0963.d012146 k sizes C) :
    ‖p‖ ≤ Real.sqrt (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)) := by
  have hs := Real.sq_sqrt
    (mul_nonneg hC (_root_.GD.N0232.N0719.N0963.d012142 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)))
  have hb := _root_.GD.N0232.N0719.N0963.d012150 k sizes hC hp
  nlinarith [norm_nonneg p,
    Real.sqrt_nonneg (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k))]


def d012152 (C : ℝ) : Set (WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))) :=
  toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) '' _root_.GD.N0232.N0719.N0963.d012146 k sizes C

theorem d012153 {C : ℝ} (hC : 0 ≤ C) :
    IsCompact (_root_.GD.N0232.N0719.N0963.d012152 k sizes C) := by
  exact _root_.GD.N0230.N0633.d001201
    (Real.sqrt (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)))
    (_root_.GD.N0232.N0719.N0963.d012148 k sizes C) (_root_.GD.N0232.N0719.N0963.d012147 k sizes C)
    (fun p hp ↦ _root_.GD.N0232.N0719.N0963.d012151 k sizes hC hp)

theorem d012154 (C : ℝ) : Convex ℝ (_root_.GD.N0232.N0719.N0963.d012152 k sizes C) := by
  exact (_root_.GD.N0232.N0719.N0963.d012148 k sizes C).linear_image (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))).toLinearMap

theorem d012155 (C : ℝ)
    (p : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))) :
    p ∈ _root_.GD.N0232.N0719.N0963.d012152 k sizes C ↔
      (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))).symm p ∈ _root_.GD.N0232.N0719.N0963.d012146 k sizes C := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro hp
    exact ⟨_, hp, by simp⟩

theorem d012156 {C : ℝ} (_hC : 0 ≤ C)
    (g : _root_.GD.N0232.N0719.N0946.d009229) {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)}
    (hp : p ∈ _root_.GD.N0232.N0719.N0963.d012146 k sizes C) :
    _root_.GD.N0232.N0719.N0896.d011109 k sizes g p (_root_.GD.N0232.N0719.N0963.d012149 k sizes hp) ∈ _root_.GD.N0232.N0719.N0963.d012146 k sizes C := by
  intro eta
  let theta := _root_.GD.N0232.N0719.N0845.d010881
    (_root_.GD.N0232.N0719.N0842.d010906 g.shift g.d009239) g.d009239⁻¹ (inv_pos.mpr g.d009240) eta
  have heta : _root_.GD.N0232.N0719.N0896.d011104 k g theta = eta :=
    _root_.GD.N0232.N0719.N0842.d010919 g.shift g.d009239 g.d009240 eta
  rw [← heta, _root_.GD.N0232.N0719.N0896.d011110, _root_.GD.N0232.N0719.N0963.d012145]
  calc
    ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p ≤
        ENNReal.ofReal (g.d009239 ^ 2) *
          ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta) := mul_le_mul' le_rfl (hp theta)
    _ = ENNReal.ofReal (C * (g.d009239 ^ 2 * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta)) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg g.d009239)]
      congr 1
      ring



theorem d012157
    (g : _root_.GD.N0232.N0719.N0946.d009229) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    _root_.GD.N0232.N0719.N0896.d011103 k sizes (_root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp) := by
  intro eta
  let theta := _root_.GD.N0232.N0719.N0845.d010881
    (_root_.GD.N0232.N0719.N0842.d010906 g.shift g.d009239) g.d009239⁻¹ (inv_pos.mpr g.d009240) eta
  have heta : _root_.GD.N0232.N0719.N0896.d011104 k g theta = eta :=
    _root_.GD.N0232.N0719.N0842.d010919 g.shift g.d009239 g.d009240 eta
  rw [← heta, _root_.GD.N0232.N0719.N0896.d011110]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hp theta)

@[simp] theorem d012158
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    _root_.GD.N0232.N0719.N0896.d011109 k sizes 1 p hp = p := by
  unfold _root_.GD.N0232.N0719.N0896.d011109
  simpa only [_root_.GD.N0232.N0719.N0946.d009229.d009233, _root_.GD.N0232.N0719.N0946.d009229.d009242, _root_.GD.N0232.N0719.N0842.d010914] using
    _root_.GD.N0232.N0719.N0896.d011092 k sizes p

theorem d012159
    (g : _root_.GD.N0232.N0719.N0946.d009229) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    _root_.GD.N0232.N0719.N0896.d011088 k sizes (_root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp)
      =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
        _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) := by
  exact (_root_.GD.N0232.N0719.N0896.d011090 k sizes
    (_root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp)).trans
      (_root_.GD.N0232.N0719.N0896.d011108 k sizes g p hp).coeFn_toLp

theorem d012160
    (g h : _root_.GD.N0232.N0719.N0946.d009229) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    _root_.GD.N0232.N0719.N0896.d011109 k sizes g
      (_root_.GD.N0232.N0719.N0896.d011109 k sizes h p hp)
      (_root_.GD.N0232.N0719.N0963.d012157 k sizes h p hp) =
        _root_.GD.N0232.N0719.N0896.d011109 k sizes (g * h) p hp := by
  apply MemLp.toLp_congr
  have hfirst := _root_.GD.N0232.N0719.N0896.d011120 k sizes g
    (_root_.GD.N0232.N0719.N0963.d012159 k sizes h p hp)
  have hcomp :
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes h.shift h.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)) =
      _root_.GD.N0232.N0719.N0842.d010911 k sizes (g * h).shift (g * h).d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) := by
    simpa only [_root_.GD.N0232.N0719.N0946.d009229.d009235, _root_.GD.N0232.N0719.N0946.d009229.d009243, _root_.GD.N0232.N0719.N0946.d009229.d009239, _root_.GD.N0232.N0719.N0946.d009229.d009236, Real.exp_add] using
      _root_.GD.N0232.N0719.N0842.d010916 k sizes g.shift g.d009239 h.shift h.d009239
        g.d009241 h.d009241 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)
  exact hfirst.trans (Filter.Eventually.of_forall (congrFun hcomp))


def d012161 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) : _root_.GD.N0232.N0719.N0963.d012146 k sizes C → _root_.GD.N0232.N0719.N0963.d012146 k sizes C :=
  fun p ↦ ⟨_root_.GD.N0232.N0719.N0896.d011109 k sizes g p.1 (_root_.GD.N0232.N0719.N0963.d012149 k sizes p.2),
    _root_.GD.N0232.N0719.N0963.d012156 k sizes hC g p.2⟩

theorem d012162 (C : ℝ) (hC : 0 ≤ C) (p : _root_.GD.N0232.N0719.N0963.d012146 k sizes C) :
    _root_.GD.N0232.N0719.N0963.d012161 k sizes C hC 1 p = p := by
  apply Subtype.ext
  exact _root_.GD.N0232.N0719.N0963.d012158 k sizes
    p.1 (_root_.GD.N0232.N0719.N0963.d012149 k sizes p.2)

theorem d012163 (C : ℝ) (hC : 0 ≤ C) (g h : _root_.GD.N0232.N0719.N0946.d009229) (p : _root_.GD.N0232.N0719.N0963.d012146 k sizes C) :
    _root_.GD.N0232.N0719.N0963.d012161 k sizes C hC g (_root_.GD.N0232.N0719.N0963.d012161 k sizes C hC h p) = _root_.GD.N0232.N0719.N0963.d012161 k sizes C hC (g * h) p := by
  apply Subtype.ext
  exact _root_.GD.N0232.N0719.N0963.d012160 k sizes
    g h p.1 (_root_.GD.N0232.N0719.N0963.d012149 k sizes p.2)


def d012164 (C : ℝ) : _root_.GD.N0232.N0719.N0963.d012146 k sizes C ≃ _root_.GD.N0232.N0719.N0963.d012152 k sizes C where
  toFun p := ⟨toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) p.1, ⟨p.1, p.2, rfl⟩⟩
  invFun p := ⟨(toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))).symm p.1,
    (_root_.GD.N0232.N0719.N0963.d012155 k sizes C p.1).mp p.2⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp

def d012165 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0719.N0963.d012152 k sizes C → _root_.GD.N0232.N0719.N0963.d012152 k sizes C :=
  fun p ↦ _root_.GD.N0232.N0719.N0963.d012164 k sizes C (_root_.GD.N0232.N0719.N0963.d012161 k sizes C hC g ((_root_.GD.N0232.N0719.N0963.d012164 k sizes C).symm p))


theorem d012166
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) (a b : ℝ) :
    _root_.GD.N0232.N0719.N0896.d011088 k sizes (a • p + b • q) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
      fun omega => a • _root_.GD.N0232.N0719.N0896.d011088 k sizes p omega + b • _root_.GD.N0232.N0719.N0896.d011088 k sizes q omega := by
  filter_upwards [_root_.GD.N0232.N0719.N0896.d011090 k sizes (a • p + b • q),
    _root_.GD.N0232.N0719.N0896.d011090 k sizes p, _root_.GD.N0232.N0719.N0896.d011090 k sizes q,
    Lp.coeFn_add (a • p) (b • q), Lp.coeFn_smul a p, Lp.coeFn_smul b q] with
      omega hcombo hp hq hadd hsmulP hsmulQ
  rw [hcombo]
  simp only [hadd, hsmulP, hsmulQ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp, hq]

theorem d012167
    (g : _root_.GD.N0232.N0719.N0946.d009229) (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    {a b : ℝ} (hab : a + b = 1) :
    _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes (a • p + b • q))
      =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] fun omega =>
        a • _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) omega +
        b • _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes q) omega := by
  have hfirst := _root_.GD.N0232.N0719.N0896.d011120 k sizes g
    (_root_.GD.N0232.N0719.N0963.d012166 k sizes p q a b)
  filter_upwards [hfirst] with omega homega
  rw [homega]
  dsimp only [_root_.GD.N0232.N0719.N0842.d010911]
  simp only [smul_eq_mul]
  linear_combination -g.shift * hab



theorem d012168
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) (hq : _root_.GD.N0232.N0719.N0896.d011103 k sizes q)
    {a b : ℝ} (hab : a + b = 1)
    (hpq : _root_.GD.N0232.N0719.N0896.d011103 k sizes (a • p + b • q)) :
    _root_.GD.N0232.N0719.N0896.d011109 k sizes g (a • p + b • q) hpq =
      a • _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp +
        b • _root_.GD.N0232.N0719.N0896.d011109 k sizes g q hq := by
  let fp := _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes p)
  let fq := _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes q)
  let fsum := _root_.GD.N0232.N0719.N0842.d010911 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0896.d011088 k sizes (a • p + b • q))
  let hpLp : MemLp fp 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := _root_.GD.N0232.N0719.N0896.d011108 k sizes g p hp
  let hqLp : MemLp fq 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := _root_.GD.N0232.N0719.N0896.d011108 k sizes g q hq
  let hsumLp : MemLp fsum 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    _root_.GD.N0232.N0719.N0896.d011108 k sizes g (a • p + b • q) hpq
  let hrawsum : MemLp (fun omega ↦ a • fp omega + b • fq omega) 2
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := (hpLp.const_smul a).add (hqLp.const_smul b)
  have hraw : fsum =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] fun omega ↦ a • fp omega + b • fq omega := by
    exact _root_.GD.N0232.N0719.N0963.d012167 k sizes g p q hab
  change MemLp.toLp fsum hsumLp = a • MemLp.toLp fp hpLp + b • MemLp.toLp fq hqLp
  calc
    MemLp.toLp fsum hsumLp =
        MemLp.toLp (fun omega ↦ a • fp omega + b • fq omega) hrawsum :=
      MemLp.toLp_congr hsumLp hrawsum hraw
    _ = MemLp.toLp (a • fp) (hpLp.const_smul a) +
        MemLp.toLp (b • fq) (hqLp.const_smul b) :=
      MemLp.toLp_add (hpLp.const_smul a) (hqLp.const_smul b)
    _ = a • MemLp.toLp fp hpLp + b • MemLp.toLp fq hqLp := by
      rw [MemLp.toLp_const_smul, MemLp.toLp_const_smul]

theorem d012169
    (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p q : _root_.GD.N0232.N0719.N0963.d012146 k sizes C) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (_root_.GD.N0232.N0719.N0963.d012161 k sizes C hC g
      ⟨a • p.1 + b • q.1, _root_.GD.N0232.N0719.N0963.d012148 k sizes C p.2 q.2 ha hb hab⟩).1 =
      a • (_root_.GD.N0232.N0719.N0963.d012161 k sizes C hC g p).1 + b • (_root_.GD.N0232.N0719.N0963.d012161 k sizes C hC g q).1 := by
  exact _root_.GD.N0232.N0719.N0963.d012168 k sizes g p.1 q.1
    (_root_.GD.N0232.N0719.N0963.d012149 k sizes p.2) (_root_.GD.N0232.N0719.N0963.d012149 k sizes q.2) hab
    (_root_.GD.N0232.N0719.N0963.d012149 k sizes (_root_.GD.N0232.N0719.N0963.d012148 k sizes C p.2 q.2 ha hb hab))



theorem d012170 (C : ℝ)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta)) :
    ∃ p ∈ _root_.GD.N0232.N0719.N0963.d012146 k sizes C, ∀ theta, _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p = _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d := by
  have hdLp : MemLp d 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    _root_.GD.N0232.N0719.N0896.d011095 k sizes d hd
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound (_root_.GD.N0232.N0719.N0859.d010810 k)))
  refine ⟨hdLp.toLp d, ?_, ?_⟩
  · intro theta
    rw [← _root_.GD.N0232.N0719.N0859.d010841 k sizes theta d hdLp]
    exact hbound theta
  · intro theta
    exact (_root_.GD.N0232.N0719.N0859.d010841 k sizes theta d hdLp).symm

end
end GD.N0232.N0719.N0963

#print axioms _root_.GD.N0232.N0719.N0963.d012145
#print axioms _root_.GD.N0232.N0719.N0963.d012153
#print axioms _root_.GD.N0232.N0719.N0963.d012156
#print axioms _root_.GD.N0232.N0719.N0963.d012163
#print axioms _root_.GD.N0232.N0719.N0963.d012168
#print axioms _root_.GD.N0232.N0719.N0963.d012170
