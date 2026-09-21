import GD.Module1123
import GD.Module1163
































open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1106

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1148
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1047
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0719.N0946



section Scaling

variable {Θ H : Type*}


def d018677 (risk : Θ → H → ℝ≥0∞) (c : Θ → ℝ≥0∞) : Θ → H → ℝ≥0∞ :=
  fun θ d => risk θ d * c θ

theorem d018678 (risk : Θ → H → ℝ≥0∞) (c : Θ → ℝ≥0∞)
    (hc0 : ∀ θ, c θ ≠ 0) (hct : ∀ θ, c θ ≠ ⊤) (e d : H) :
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1106.d018677 risk c) e d ↔ _root_.GD.N0230.N0608.d000672 risk e d := by
  unfold _root_.GD.N0230.N0608.d000672 _root_.GD.N0232.N0720.N1106.d018677
  exact forall_congr' fun θ => ENNReal.mul_le_mul_iff_left (hc0 θ) (hct θ)

theorem d018679 (risk : Θ → H → ℝ≥0∞) (c : Θ → ℝ≥0∞)
    (hc0 : ∀ θ, c θ ≠ 0) (hct : ∀ θ, c θ ≠ ⊤) (d : H) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1106.d018677 risk c) d ↔ _root_.GD.N0230.N0608.d000674 risk d := by
  unfold _root_.GD.N0230.N0608.d000674
  exact forall_congr' fun e =>
    imp_congr (_root_.GD.N0232.N0720.N1106.d018678 risk c hc0 hct e d) Iff.rfl

theorem d018680 (risk : Θ → H → ℝ≥0∞) (c : Θ → ℝ≥0∞)
    (hc0 : ∀ θ, c θ ≠ 0) (hct : ∀ θ, c θ ≠ ⊤) (e d : H) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1106.d018677 risk c) e d ↔
      _root_.GD.N0230.N0608.d000675 risk e d := by
  unfold _root_.GD.N0230.N0608.d000675 _root_.GD.N0232.N0720.N1106.d018677
  refine forall_congr' fun θ => ?_
  rw [lt_iff_not_ge, lt_iff_not_ge, ENNReal.mul_le_mul_iff_left (hc0 θ) (hct θ)]

end Scaling

variable (m n : ℕ)




theorem d018681 (c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ≥0∞)
    (hc0 : ∀ θ, c θ ≠ 0) (hct : ∀ θ, c θ ≠ ⊤) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    _root_.GD.N0232.N0720.N1159.d014660 m n d ↔
      (Measurable d ∧
        _root_.GD.N0230.N0644.d000297
          (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) => g • ω)
          (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) => g • y) d ∧
        (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
          _root_.GD.N0232.N0720.N1080.d014197 m n θ d * c θ <
            _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) * c θ) ∧
        (∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e →
          (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
            _root_.GD.N0232.N0720.N1080.d014197 m n θ e * c θ ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ d * c θ) →
          ∀ θ : _root_.GD.N0232.N0720.N1080.d014168, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] d)) := by
  unfold _root_.GD.N0232.N0720.N1159.d014660
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_))
  · refine forall_congr' fun θ => ?_
    rw [lt_iff_not_ge, lt_iff_not_ge, ENNReal.mul_le_mul_iff_left (hc0 θ) (hct θ)]
  · refine forall_congr' fun e => imp_congr Iff.rfl (imp_congr ?_ Iff.rfl)
    exact forall_congr' fun θ => (ENNReal.mul_le_mul_iff_left (hc0 θ) (hct θ)).symm




def d018682 (ρ : ℝ) (hρ : 0 < ρ) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := 0
  scale₁ := 1
  scale₂ := ρ
  scale₁_pos := one_pos
  scale₂_pos := hρ


def d018683 (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0719.N0946.d009229 where
  shift := θ.location
  logScale := Real.log θ.scale₁

theorem d018684 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1106.d018683 θ).d009239 = θ.scale₁ := by
  simp [_root_.GD.N0232.N0719.N0946.d009229.d009239, _root_.GD.N0232.N0720.N1106.d018683, Real.exp_log θ.scale₁_pos]

theorem d018685 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1106.d018683 θ).shift = θ.location := rfl


theorem d018686 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1215.d014272 (_root_.GD.N0232.N0720.N1106.d018683 θ)
        (_root_.GD.N0232.N0720.N1106.d018682 (θ.scale₂ / θ.scale₁) (div_pos θ.scale₂_pos θ.scale₁_pos)) = θ := by
  have h1 : θ.scale₁ ≠ 0 := θ.scale₁_pos.ne'
  apply _root_.GD.N0232.N0720.N1215.d014277
  · simp [_root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0720.N1106.d018685, _root_.GD.N0232.N0720.N1106.d018682]
  · simp [_root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0720.N1106.d018684, _root_.GD.N0232.N0720.N1106.d018682]
  · simp only [_root_.GD.N0232.N0720.N1215.d014275, _root_.GD.N0232.N0720.N1106.d018684, _root_.GD.N0232.N0720.N1106.d018682]
    field_simp


theorem d018687
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n θ p =
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 (θ.scale₂ / θ.scale₁)
          (div_pos θ.scale₂_pos θ.scale₁_pos)) p *
        ENNReal.ofReal (θ.scale₁ ^ 2) := by
  conv_lhs => rw [← _root_.GD.N0232.N0720.N1106.d018686 θ]
  rw [hp (_root_.GD.N0232.N0720.N1106.d018683 θ) _, _root_.GD.N0232.N0720.N1106.d018684, mul_comm]

theorem d018688 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    ENNReal.ofReal (θ.scale₁ ^ 2) ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (pow_pos θ.scale₁_pos 2)).ne'



theorem d018689
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p) (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p q ↔
      ∀ (ρ : ℝ) (hρ : 0 < ρ),
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) p < _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) q := by
  constructor
  · intro h ρ hρ
    exact h _
  · intro h θ
    rw [_root_.GD.N0232.N0720.N1106.d018687 m n p hp θ,
      _root_.GD.N0232.N0720.N1106.d018687 m n q hq θ]
    exact ENNReal.mul_lt_mul_left (_root_.GD.N0232.N0720.N1106.d018688 θ) ENNReal.ofReal_ne_top (h _ _)



theorem d018690
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014638 m n p) (hq : _root_.GD.N0232.N0720.N1159.d014638 m n q) :
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) p q ↔
      ∀ (ρ : ℝ) (hρ : 0 < ρ),
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) p ≤ _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) q := by
  constructor
  · intro h ρ hρ
    exact h _
  · intro h θ
    rw [_root_.GD.N0232.N0720.N1106.d018687 m n p hp θ,
      _root_.GD.N0232.N0720.N1106.d018687 m n q hq θ]
    exact (ENNReal.mul_le_mul_iff_left (_root_.GD.N0232.N0720.N1106.d018688 θ)
      ENNReal.ofReal_ne_top).mpr (h _ _)





theorem d018691
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        (∀ (ρ : ℝ) (hρ : 0 < ρ),
          _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) s.value <
            _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1106.d018682 ρ hρ) (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) ∧
        _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hs, ht⟩
    exact ⟨s, (_root_.GD.N0232.N0720.N1106.d018689 m n _ _ s.riskCharacter
      (_root_.GD.N0232.N0720.N1047.d018647 m n hm hn)).1 hs, ht⟩
  · rintro ⟨s, hs, ht⟩
    exact ⟨s, (_root_.GD.N0232.N0720.N1106.d018689 m n _ _ s.riskCharacter
      (_root_.GD.N0232.N0720.N1047.d018647 m n hm hn)).2 hs, ht⟩



theorem d018692 (g : _root_.GD.N0232.N0719.N0946.d009229) : (g⁻¹).d009239 = (g.d009239)⁻¹ := by
  simp [_root_.GD.N0232.N0719.N0946.d009229.d009239, Real.exp_neg]


theorem d018693 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    _root_.GD.N0232.N0720.N1159.d014645 m n s g⁻¹ (_root_.GD.N0232.N0720.N1159.d014645 m n s g p) = p := by
  apply Subtype.ext
  have h := _root_.GD.N0232.N0720.N1482.d015161
    (m := m) (n := n) g⁻¹ g p.1 (_root_.GD.N0232.N0720.N1159.d014644 m n s p.1 p.2)
  rw [inv_mul_cancel, _root_.GD.N0232.N0720.N1482.d015159] at h
  exact h



theorem d018694 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 ↔ _root_.GD.N0232.N0720.N1159.d014647 m n s g⁻¹ = 0 := by
  rw [_root_.GD.N0232.N0720.N1159.d014651, _root_.GD.N0232.N0720.N1159.d014651]
  constructor
  · intro h
    have hinv := _root_.GD.N0232.N0720.N1106.d018693 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)
    rwa [h] at hinv
  · intro h
    have hinv := _root_.GD.N0232.N0720.N1106.d018693 m n s g⁻¹ (_root_.GD.N0232.N0720.N1159.d014646 m n s)
    rwa [h, inv_inv] at hinv




theorem d018695
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
        ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 * g.d009239 ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1106.d018694,
    _root_.GD.N0232.N0720.N1148.d018038, inv_inv,
    _root_.GD.N0232.N0720.N1106.d018692, inv_pow, div_inv_eq_mul]



def d018696 : _root_.GD.N0232.N0720.N1080.d014168 where
  location := 0
  scale₁ := 2
  scale₂ := 2
  scale₁_pos := two_pos
  scale₂_pos := two_pos

def d018697 : _root_.GD.N0232.N0720.N1080.d014168 where
  location := 1
  scale₁ := 3
  scale₂ := 3
  scale₁_pos := three_pos
  scale₂_pos := three_pos

theorem d018698 :
    _root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015130 _root_.GD.N0232.N0720.N1080.d014169 = _root_.GD.N0232.N0720.N1106.d018696 := by
  apply _root_.GD.N0232.N0720.N1215.d014277 <;>
    simp [_root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0720.N1080.d014169, _root_.GD.N0232.N0720.N1106.d018696, _root_.GD.N0232.N0720.N1148.d018027,
      _root_.GD.N0232.N0720.N1148.d018029]

theorem d018699 :
    _root_.GD.N0232.N0720.N1215.d014272 _root_.GD.N0232.N0720.N1482.d015131 _root_.GD.N0232.N0720.N1080.d014169 = _root_.GD.N0232.N0720.N1106.d018697 := by
  apply _root_.GD.N0232.N0720.N1215.d014277 <;>
    simp [_root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0720.N1080.d014169, _root_.GD.N0232.N0720.N1106.d018697,
      _root_.GD.N0232.N0720.N1148.d018028, _root_.GD.N0232.N0720.N1148.d018030]


theorem d018700
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1106.d018696 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
          ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 * 4) ∧
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1106.d018697 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
          ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 * 9) := by
  rw [_root_.GD.N0232.N0720.N1482.d015172
    (m := m) (n := n) hm hn]
  have h2 : ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
      _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 = 0 ↔
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1106.d018696 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
          ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 * 4) := by
    intro s
    rw [_root_.GD.N0232.N0720.N1106.d018695,
      _root_.GD.N0232.N0720.N1106.d018698, _root_.GD.N0232.N0720.N1148.d018029]
    norm_num
  have h3 : ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
      _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 = 0 ↔
        _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1106.d018697 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
          ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 * 9) := by
    intro s
    rw [_root_.GD.N0232.N0720.N1106.d018695,
      _root_.GD.N0232.N0720.N1106.d018699, _root_.GD.N0232.N0720.N1148.d018030]
    norm_num
  constructor
  · rintro ⟨s, hs, hTwo, hThree⟩
    exact ⟨s, hs, (h2 s).1 hTwo, (h3 s).1 hThree⟩
  · rintro ⟨s, hs, hTwo, hThree⟩
    exact ⟨s, hs, (h2 s).2 hTwo, (h3 s).2 hThree⟩





theorem d018701
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) ≤
        ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 / g.d009239 ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1148.d018037 s g]
  have hdil : (0 : ℝ) < g.d009239 ^ 2 := pow_pos g.d009240 2
  have hnn := _root_.GD.N0232.N0720.N1159.d014650 m n s g
  constructor
  · intro h
    rw [h, zero_add]
  · intro h
    rw [ENNReal.ofReal_le_ofReal_iff (div_nonneg (sq_nonneg _) hdil.le)] at h
    have h' := mul_le_mul_of_nonneg_right h hdil.le
    rw [div_mul_cancel₀ _ hdil.ne', div_mul_cancel₀ _ hdil.ne'] at h'
    linarith


theorem d018702
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 ↔
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) ≤
        ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 * g.d009239 ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1106.d018694,
    _root_.GD.N0232.N0720.N1106.d018701, inv_inv,
    _root_.GD.N0232.N0720.N1106.d018692, inv_pow, div_inv_eq_mul]



theorem d018703 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (hs : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value)
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) s.value =
      ENNReal.ofReal (‖s.value‖ ^ 2 / g.d009239 ^ 2) := by
  have hzero := _root_.GD.N0232.N0720.N1409.d018609 s hs g
  have hsat := (_root_.GD.N0232.N0720.N1148.d018038 s g).1 hzero
  rwa [(_root_.GD.N0232.N0720.N1159.d014635 m n s.value).2 hs] at hsat

end

end N1106
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1106.d018679
#print axioms _root_.GD.N0232.N0720.N1106.d018681
#print axioms _root_.GD.N0232.N0720.N1106.d018689
#print axioms _root_.GD.N0232.N0720.N1106.d018691
#print axioms _root_.GD.N0232.N0720.N1106.d018694
#print axioms _root_.GD.N0232.N0720.N1106.d018700
#print axioms _root_.GD.N0232.N0720.N1106.d018701
#print axioms _root_.GD.N0232.N0720.N1106.d018703
