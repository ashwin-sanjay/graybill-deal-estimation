import GD.Module1867
import GD.Module1885

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0082.N0329

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0230.N0602
open _root_.GD.N0076.N0313
open _root_.GD.N0081.N0326 _root_.GD.N0082.N0335
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0117
open _root_.GD.N0232.N0720.N1425

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

include hm hn in
theorem d030731 (H : ℝ → ℝ) (b a : ℝ) (ha : 0 < a)
    (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0082.N0335.d030724 m n H (_root_.GD.N0107.d009024 m n b a a ω) = b + a * _root_.GD.N0082.N0335.d030724 m n H ω := by
  have hmy := _root_.GD.N0107.d009086 (by omega : 0 < n) b a ω.2
  have hx := _root_.GD.N0117.d014148 hm b a ω.1
  have hy := _root_.GD.N0117.d014148 hn b a ω.2
  have hD := _root_.GD.N0117.d014149 hm hn b a ω
  simp only [_root_.GD.N0082.N0335.d030724, _root_.GD.N0232.N0720.N1425.d014720]
  rw [hD]
  simp only [_root_.GD.N0107.d009024, _root_.GD.N0107.d009084]
  rw [hmy, hx, hy, _root_.GD.N0117.d014150 hm hn ha.ne']
  ring

include hm hn in
theorem d030732 (H : ℝ → ℝ) (hH : Measurable H)
    (hHI : ∀ u, H u ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0082.N0335.d030724 m n H ∈ _root_.GD.N0232.N0720.N1256.d015552 m n :=
  ⟨⟨_root_.GD.N0082.N0335.d030725 m n H hH, _root_.GD.N0082.N0329.d030731 m n hm hn H⟩,
    (_root_.GD.N0082.N0335.d030729 m n hm hn H hH hHI).2⟩

theorem d030733 (d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n) (he : e ∈ _root_.GD.N0232.N0720.N1256.d015551 m n)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ (fun z => a * d z + b * e z) ≤
      ENNReal.ofReal a * _root_.GD.N0232.N0720.N1080.d014197 m n θ d +
        ENNReal.ofReal b * _root_.GD.N0232.N0720.N1080.d014197 m n θ e := by
  have hmd := _root_.GD.N0232.N0720.N1215.d014285 m n d hd.1 (hd.2 _root_.GD.N0232.N0720.N1080.d014169)
  have hme := _root_.GD.N0232.N0720.N1215.d014285 m n e he.1 (he.2 _root_.GD.N0232.N0720.N1080.d014169)
  have hmc := (hmd.const_smul a).add (hme.const_smul b)
  change _root_.GD.N0232.N0720.N1080.d014197 m n θ (a • d + b • e) ≤ _
  rw [_root_.GD.N0232.N0720.N1080.d014198 m n θ _ hmc,
    _root_.GD.N0232.N0720.N1080.d014198 m n θ d hmd, _root_.GD.N0232.N0720.N1080.d014198 m n θ e hme]
  change _root_.GD.N0232.N0720.N1080.d014182 m n θ (a • hmd.toLp d + b • hme.toLp e) ≤ _
  exact _root_.GD.N0230.N0602.d000121 (_root_.GD.N0232.N0720.N1080.d014173 m n θ) θ.location
    (hmd.toLp d) (hme.toLp e) ha hb hab

theorem d030734 (d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015552 m n) (he : e ∈ _root_.GD.N0232.N0720.N1256.d015552 m n)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (fun z => a * d z + b * e z) ∈ _root_.GD.N0232.N0720.N1256.d015552 m n := by
  refine ⟨⟨(hd.1.1.const_mul a).add (he.1.1.const_mul b), ?_⟩, ?_⟩
  · intro c s hs z
    dsimp only
    rw [hd.1.2 c s hs z, he.1.2 c s hs z]
    calc
      _ = (a + b) * c + s * (a * d z + b * e z) := by ring
      _ = _ := by rw [hab]; ring
  · intro θ
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hd.2 θ),
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (he.2 θ)⟩)
      (_root_.GD.N0082.N0329.d030733 m n d e ⟨hd.1.1, hd.2⟩ ⟨he.1.1, he.2⟩ a b ha hb hab θ)

theorem d030735
    (d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015552 m n) (he : e ∈ _root_.GD.N0232.N0720.N1256.d015552 m n)
    (τ : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hτ : ∀ θ, τ θ ∈ Ioo (0 : ℝ) 1)
    (p q : ℝ → ℝ)
    (hp0 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ p t)
    (hq0 : ∀ t ∈ Ioo (0 : ℝ) 1, 0 ≤ q t)
    (hpcont : ContinuousOn p (Ioo 0 1))
    (hp : ∀ t ∈ Ioo (0 : ℝ) 1, p t < 1)
    (hqcont : ContinuousOn q (Icc 0 1))
    (hqleft : q 0 < 1) (hqright : q 1 < 1)
    (hpd : ∀ θ, _root_.GD.N0076.N0313.d030568 m n hm hn θ d ≤ ENNReal.ofReal (p (τ θ)))
    (hqe : ∀ θ, _root_.GD.N0076.N0313.d030568 m n hm hn θ e ≤ ENNReal.ofReal (q (τ θ))) :
    ∃ (J : ℕ) (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ), 1 ≤ J ∧ f ∈ _root_.GD.N0232.N0720.N1256.d015552 m n ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ f ≤
        ENNReal.ofReal (_root_.GD.N0082.d030598 J) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ := by
  obtain ⟨ε, γ, hε, hε1, hγ, hmix⟩ := _root_.GD.N0081.N0326.d005152
    p q hpcont hp hqcont hqleft hqright
  obtain ⟨J, hJ, hJcap⟩ := _root_.GD.N0082.d030601 (show 1 - γ < 1 by linarith)
  have ha : 0 ≤ 1 - ε := (sub_pos.mpr hε1).le
  refine ⟨J, (fun z => (1 - ε) * d z + ε * e z), hJ,
    _root_.GD.N0082.N0329.d030734 m n d e hd he _ _ ha hε.le (by ring), ?_⟩
  intro θ
  have hpd' := (ENNReal.div_le_iff (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn θ)
    (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ)).mp (hpd θ)
  have hqe' := (ENNReal.div_le_iff (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn θ)
    (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ)).mp (hqe θ)
  calc
    _ ≤ ENNReal.ofReal (1 - ε) * _root_.GD.N0232.N0720.N1080.d014197 m n θ d +
        ENNReal.ofReal ε * _root_.GD.N0232.N0720.N1080.d014197 m n θ e :=
      _root_.GD.N0082.N0329.d030733 m n d e ⟨hd.1.1, hd.2⟩ ⟨he.1.1, he.2⟩ _ _ ha hε.le (by ring) θ
    _ ≤ ENNReal.ofReal (1 - ε) *
          (ENNReal.ofReal (p (τ θ)) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ) +
        ENNReal.ofReal ε *
          (ENNReal.ofReal (q (τ θ)) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ) :=
      add_le_add (mul_le_mul' le_rfl hpd') (mul_le_mul' le_rfl hqe')
    _ = ENNReal.ofReal ((1 - ε) * p (τ θ) + ε * q (τ θ)) *
        _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ := by
      rw [ENNReal.ofReal_add (mul_nonneg ha (hp0 _ (hτ θ)))
        (mul_nonneg hε.le (hq0 _ (hτ θ))),
        ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hε.le, add_mul]
      simp only [mul_assoc]
    _ ≤ ENNReal.ofReal (_root_.GD.N0082.d030598 J) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal ((hmix _ (hτ θ)).trans hJcap.le)) le_rfl

end
end GD.N0082.N0329

#print axioms _root_.GD.N0082.N0329.d030731
#print axioms _root_.GD.N0082.N0329.d030732
#print axioms _root_.GD.N0082.N0329.d030733
#print axioms _root_.GD.N0082.N0329.d030734
#print axioms _root_.GD.N0082.N0329.d030735
