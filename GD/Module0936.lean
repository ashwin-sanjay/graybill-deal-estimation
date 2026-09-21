import GD.Module0820
import GD.Module0912
import GD.Module0004











open MeasureTheory Set
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1387

open _root_.GD.N0232.N0720.N1393 _root_.GD.N0232.N0720.N1372
open _root_.GD.N0232.N0720.N1388 _root_.GD.N0232.N0720.N1389
open _root_.GD.N0107 _root_.GD.N0137
open _root_.GD.N0230.N0556

noncomputable section

abbrev d014681 := _root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2

abbrev d014682 := _root_.GD.N0232.N0720.N1080.d014168

def d014683 (c : ℝ) : _root_.GD.N0232.N0720.N1387.d014681 → _root_.GD.N0232.N0720.N1387.d014681 :=
  _root_.GD.N0107.d009024 2 2 0 c c

@[fun_prop]
theorem d014684 (c : ℝ) : Measurable (_root_.GD.N0232.N0720.N1387.d014683 c) :=
  _root_.GD.N0107.d009026 2 2 0 c c

theorem d014685 (m s t c : ℝ) :
    (_root_.GD.N0107.d009030 2 2 m s t).map (_root_.GD.N0232.N0720.N1387.d014683 c) =
      _root_.GD.N0107.d009030 2 2 (c * m) (c * s) (c * t) := by
  unfold _root_.GD.N0107.d009030
  rw [Measure.map_map (_root_.GD.N0232.N0720.N1387.d014684 c) (_root_.GD.N0107.d009026 2 2 m s t)]
  congr 1
  funext x
  apply Prod.ext <;> funext i <;>
    simp only [Function.comp_apply, _root_.GD.N0232.N0720.N1387.d014683, _root_.GD.N0107.d009024, _root_.GD.N0107.d009018, zero_add] <;>
    ring

theorem d014686 (x : _root_.GD.N0232.N0720.N1387.d014681) :
    _root_.GD.N0232.N0720.N1389.d012529 x = WithLp.toLp 2
      ![(x.1 0 + x.1 1) / 2, (x.1 0 - x.1 1) / 2,
        (x.2 0 + x.2 1) / 2, (x.2 0 - x.2 1) / 2] := by
  apply _root_.GD.N0232.N0720.N1389.d012508.symm.injective
  simp only [_root_.GD.N0232.N0720.N1389.d012529, _root_.GD.N0232.N0720.N1389.d012508.symm_apply_apply, _root_.GD.N0232.N0720.N1389.d012509]
  rfl

theorem d014687 (c : ℝ) (x : _root_.GD.N0232.N0720.N1387.d014681) :
    _root_.GD.N0232.N0720.N1389.d012529 (_root_.GD.N0232.N0720.N1387.d014683 c x) = c • _root_.GD.N0232.N0720.N1389.d012529 x := by
  ext i
  fin_cases i <;>
    simp [_root_.GD.N0232.N0720.N1387.d014686, _root_.GD.N0232.N0720.N1387.d014683, _root_.GD.N0107.d009024, _root_.GD.N0107.d009018,
      PiLp.smul_apply] <;> ring

theorem d014688 (h : _root_.GD.N0232.N0720.N1393.d004495) {c : ℝ} (hc : 0 < c) (x : _root_.GD.N0232.N0720.N1387.d014681) :
    _root_.GD.N0232.N0720.N1389.d012534 h (_root_.GD.N0232.N0720.N1387.d014683 c x) = c * _root_.GD.N0232.N0720.N1389.d012534 h x := by
  unfold _root_.GD.N0232.N0720.N1389.d012534
  rw [_root_.GD.N0232.N0720.N1387.d014687]
  simpa only [smul_eq_mul] using _root_.GD.N0232.N0720.N1393.d004497 h c hc (_root_.GD.N0232.N0720.N1389.d012529 x)

theorem d014689 (h : _root_.GD.N0232.N0720.N1393.d004495) (m s t : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫⁻ x, ENNReal.ofReal ((_root_.GD.N0232.N0720.N1389.d012534 h x - c * m) ^ 2)
      ∂_root_.GD.N0107.d009030 2 2 (c * m) (c * s) (c * t)) =
    ENNReal.ofReal (c ^ 2) *
      ∫⁻ x, ENNReal.ofReal ((_root_.GD.N0232.N0720.N1389.d012534 h x - m) ^ 2) ∂_root_.GD.N0107.d009030 2 2 m s t := by
  rw [← _root_.GD.N0232.N0720.N1387.d014685,
    lintegral_map (by fun_prop) (_root_.GD.N0232.N0720.N1387.d014684 c)]
  simp_rw [_root_.GD.N0232.N0720.N1387.d014688 h hc,
    ← mul_sub, mul_pow, ENNReal.ofReal_mul (sq_nonneg c)]
  exact lintegral_const_mul _ (by fun_prop)

def d014690 (θ : _root_.GD.N0232.N0720.N1387.d014682) : ℝ := θ.scale₁ ^ 2 + θ.scale₂ ^ 2

theorem d014691 (θ : _root_.GD.N0232.N0720.N1387.d014682) : 0 < _root_.GD.N0232.N0720.N1387.d014690 θ := by
  exact add_pos (sq_pos_of_pos θ.scale₁_pos) (sq_pos_of_pos θ.scale₂_pos)

def d014692 (θ : _root_.GD.N0232.N0720.N1387.d014682) : ℝ := Real.sqrt (_root_.GD.N0232.N0720.N1387.d014690 θ / 2)

theorem d014693 (θ : _root_.GD.N0232.N0720.N1387.d014682) : 0 < _root_.GD.N0232.N0720.N1387.d014692 θ :=
  Real.sqrt_pos.2 (div_pos (_root_.GD.N0232.N0720.N1387.d014691 θ) (by norm_num))

theorem d014694 (θ : _root_.GD.N0232.N0720.N1387.d014682) : _root_.GD.N0232.N0720.N1387.d014692 θ ^ 2 = _root_.GD.N0232.N0720.N1387.d014690 θ / 2 :=
  Real.sq_sqrt (div_nonneg (_root_.GD.N0232.N0720.N1387.d014691 θ).le (by norm_num))

def d014695 (θ : _root_.GD.N0232.N0720.N1387.d014682) : Ioo (0 : ℝ) 1 :=
  ⟨θ.scale₁ ^ 2 / _root_.GD.N0232.N0720.N1387.d014690 θ,
    div_pos (sq_pos_of_pos θ.scale₁_pos) (_root_.GD.N0232.N0720.N1387.d014691 θ),
    (div_lt_one (_root_.GD.N0232.N0720.N1387.d014691 θ)).2 (by
      unfold _root_.GD.N0232.N0720.N1387.d014690
      linarith [sq_pos_of_pos θ.scale₂_pos])⟩

def d014696 (θ : _root_.GD.N0232.N0720.N1387.d014682) : _root_.GD.N0232.N0720.N1372.d004518 :=
  (θ.location / _root_.GD.N0232.N0720.N1387.d014692 θ, _root_.GD.N0232.N0720.N1387.d014695 θ)

theorem d014697 (θ : _root_.GD.N0232.N0720.N1387.d014682) :
    _root_.GD.N0232.N0720.N1387.d014692 θ * (_root_.GD.N0232.N0720.N1387.d014696 θ).1 = θ.location := by
  exact mul_div_cancel₀ _ (_root_.GD.N0232.N0720.N1387.d014693 θ).ne'

theorem d014698 (θ : _root_.GD.N0232.N0720.N1387.d014682) :
    _root_.GD.N0232.N0720.N1387.d014692 θ * _root_.GD.N0232.N0720.N1389.d012523 (_root_.GD.N0232.N0720.N1387.d014696 θ) = θ.scale₁ := by
  apply (sq_eq_sq₀ (mul_pos (_root_.GD.N0232.N0720.N1387.d014693 θ) (_root_.GD.N0232.N0720.N1389.d012525 _)).le
    θ.scale₁_pos.le).mp
  rw [mul_pow, _root_.GD.N0232.N0720.N1387.d014694]
  unfold _root_.GD.N0232.N0720.N1389.d012523
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) (_root_.GD.N0232.N0720.N1387.d014696 θ).2.2.1.le)]
  change _root_.GD.N0232.N0720.N1387.d014690 θ / 2 * (2 * (θ.scale₁ ^ 2 / _root_.GD.N0232.N0720.N1387.d014690 θ)) = θ.scale₁ ^ 2
  field_simp [(_root_.GD.N0232.N0720.N1387.d014691 θ).ne'] <;> ring

theorem d014699 (θ : _root_.GD.N0232.N0720.N1387.d014682) :
    _root_.GD.N0232.N0720.N1387.d014692 θ * _root_.GD.N0232.N0720.N1389.d012524 (_root_.GD.N0232.N0720.N1387.d014696 θ) = θ.scale₂ := by
  apply (sq_eq_sq₀ (mul_pos (_root_.GD.N0232.N0720.N1387.d014693 θ) (_root_.GD.N0232.N0720.N1389.d012526 _)).le
    θ.scale₂_pos.le).mp
  rw [mul_pow, _root_.GD.N0232.N0720.N1387.d014694]
  unfold _root_.GD.N0232.N0720.N1389.d012524
  rw [Real.sq_sqrt (mul_nonneg (by norm_num)
    (sub_pos.mpr (_root_.GD.N0232.N0720.N1387.d014696 θ).2.2.2).le)]
  change _root_.GD.N0232.N0720.N1387.d014690 θ / 2 *
    (2 * (1 - θ.scale₁ ^ 2 / _root_.GD.N0232.N0720.N1387.d014690 θ)) = θ.scale₂ ^ 2
  field_simp [(_root_.GD.N0232.N0720.N1387.d014691 θ).ne'] <;> dsimp [_root_.GD.N0232.N0720.N1387.d014690] <;> ring


theorem d014700 (θ : _root_.GD.N0232.N0720.N1387.d014682) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1080.d014197 2 2 θ (_root_.GD.N0232.N0720.N1389.d012534 h) =
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1387.d014692 θ ^ 2) * ENNReal.ofReal (_root_.GD.N0232.N0720.N1372.d004546 (_root_.GD.N0232.N0720.N1387.d014696 θ) h) := by
  have hr := _root_.GD.N0232.N0720.N1387.d014689 h (_root_.GD.N0232.N0720.N1387.d014696 θ).1
    (_root_.GD.N0232.N0720.N1389.d012523 (_root_.GD.N0232.N0720.N1387.d014696 θ)) (_root_.GD.N0232.N0720.N1389.d012524 (_root_.GD.N0232.N0720.N1387.d014696 θ))
    (_root_.GD.N0232.N0720.N1387.d014693 θ)
  rw [_root_.GD.N0232.N0720.N1387.d014697, _root_.GD.N0232.N0720.N1387.d014698, _root_.GD.N0232.N0720.N1387.d014699,
    _root_.GD.N0232.N0720.N1389.d012536] at hr
  exact hr

def d014701 (q : _root_.GD.N0232.N0720.N1372.d004518) : _root_.GD.N0232.N0720.N1387.d014682 where
  location := q.1
  scale₁ := _root_.GD.N0232.N0720.N1389.d012523 q
  scale₂ := _root_.GD.N0232.N0720.N1389.d012524 q
  scale₁_pos := _root_.GD.N0232.N0720.N1389.d012525 q
  scale₂_pos := _root_.GD.N0232.N0720.N1389.d012526 q

theorem d014702 (q : _root_.GD.N0232.N0720.N1372.d004518) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1080.d014197 2 2 (_root_.GD.N0232.N0720.N1387.d014701 q) (_root_.GD.N0232.N0720.N1389.d012534 h) =
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1372.d004546 q h) :=
  _root_.GD.N0232.N0720.N1389.d012536 q h

theorem d014703 (q : _root_.GD.N0232.N0720.N1372.d004518) (h : _root_.GD.N0232.N0720.N1393.d004495) : 0 ≤ _root_.GD.N0232.N0720.N1372.d004546 q h := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (sq_nonneg _) (_root_.GD.N0232.N0720.N1389.d012532 q x)




theorem d014704 (h : _root_.GD.N0232.N0720.N1393.d004495)
    (hraw : ¬ ∃ d : _root_.GD.N0232.N0720.N1387.d014681 → ℝ, Measurable d ∧
      (∀ θ : _root_.GD.N0232.N0720.N1387.d014682, _root_.GD.N0232.N0720.N1080.d014197 2 2 θ d ≤
        _root_.GD.N0232.N0720.N1080.d014197 2 2 θ (_root_.GD.N0232.N0720.N1389.d012534 h)) ∧
      ∃ θ : _root_.GD.N0232.N0720.N1387.d014682, _root_.GD.N0232.N0720.N1080.d014197 2 2 θ d <
        _root_.GD.N0232.N0720.N1080.d014197 2 2 θ (_root_.GD.N0232.N0720.N1389.d012534 h)) :
    _root_.GD.N0230.N0556.d000031 _root_.GD.N0232.N0720.N1372.d004546 h := by
  rintro ⟨g, hweak, q, hstrict⟩
  apply hraw
  refine ⟨_root_.GD.N0232.N0720.N1389.d012534 g, _root_.GD.N0232.N0720.N1389.d012535 g, ?_, ?_⟩
  · intro θ
    rw [_root_.GD.N0232.N0720.N1387.d014700, _root_.GD.N0232.N0720.N1387.d014700]
    exact mul_le_mul_left' (ENNReal.ofReal_le_ofReal (hweak _)) _
  · refine ⟨_root_.GD.N0232.N0720.N1387.d014701 q, ?_⟩
    rw [_root_.GD.N0232.N0720.N1387.d014702, _root_.GD.N0232.N0720.N1387.d014702]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (_root_.GD.N0232.N0720.N1387.d014703 q g)).2 hstrict

end

end GD.N0232.N0720.N1387

#print axioms _root_.GD.N0232.N0720.N1387.d014700
#print axioms _root_.GD.N0232.N0720.N1387.d014704
