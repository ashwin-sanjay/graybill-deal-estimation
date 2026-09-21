import GD.Module0970
import GD.Module0973
import GD.Module1066






























open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1105

noncomputable section

open _root_.GD.N0232.N0720.N1028
open _root_.GD.N0232.N0720.N1029
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0668
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1102
open _root_.GD.N0232.N0720.N1128
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482

variable (m n : ℕ)





def d017112
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∀ (g : _root_.GD.N0232.N0720.N1482.d015118) (theta : _root_.GD.N0232.N0720.N1080.d014168),
    _root_.GD.N0232.N0720.N1028.d015328 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) p q =
      ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1028.d015328 m n theta p q


theorem d017113
    {p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (htax : _root_.GD.N0232.N0720.N1105.d017112 m n p q)
    (g : _root_.GD.N0232.N0720.N1482.d015118) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1128.d017098 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) p q =
      g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1128.d017098 m n theta p q := by
  unfold _root_.GD.N0232.N0720.N1128.d017098
  rw [htax g theta, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _)]





theorem d017114
    (lambda : ℝ) (r s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hr : _root_.GD.N0232.N0720.N1159.d014637 m n r) (hs : _root_.GD.N0232.N0720.N1159.d014637 m n s)
    (hcr : _root_.GD.N0232.N0720.N1159.d014638 m n r)
    (hcs : _root_.GD.N0232.N0720.N1159.d014638 m n s)
    (htax : _root_.GD.N0232.N0720.N1105.d017112 m n r s) :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0230.N0668.d001343 lambda r s) := by
  intro g theta
  have hfinRepair := _root_.GD.N0232.N0720.N1128.d017096 m n lambda r s hr hs
  have hid₁ := _root_.GD.N0232.N0720.N1128.d017103 m n lambda r s hr hs theta
  have hid₂ := _root_.GD.N0232.N0720.N1128.d017103 m n lambda r s hr hs
    (_root_.GD.N0232.N0720.N1215.d014272 g theta)
  have hrCharReal : (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) r).toReal =
      g.d009239 ^ 2 * (_root_.GD.N0232.N0720.N1080.d014182 m n theta r).toReal := by
    rw [hcr g theta, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg _)]
  have hsCharReal : (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) s).toReal =
      g.d009239 ^ 2 * (_root_.GD.N0232.N0720.N1080.d014182 m n theta s).toReal := by
    rw [hcs g theta, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg _)]
  have htaxReal :=
    _root_.GD.N0232.N0720.N1105.d017113 m n htax g theta
  have hcombine :
      (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
        (_root_.GD.N0230.N0668.d001343 lambda r s)).toReal =
      g.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0668.d001343 lambda r s)).toReal := by
    have h1 : (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
        (_root_.GD.N0230.N0668.d001343 lambda r s)).toReal =
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) s).toReal +
          (1 - lambda) *
            (((_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) r).toReal -
              (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) s).toReal) -
              lambda *
                _root_.GD.N0232.N0720.N1128.d017098 m n
                  (_root_.GD.N0232.N0720.N1215.d014272 g theta) r s) := by
      linarith [hid₂]
    have h2 : (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0668.d001343 lambda r s)).toReal =
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta s).toReal +
          (1 - lambda) *
            (((_root_.GD.N0232.N0720.N1080.d014182 m n theta r).toReal - (_root_.GD.N0232.N0720.N1080.d014182 m n theta s).toReal) -
              lambda * _root_.GD.N0232.N0720.N1128.d017098 m n theta r s) := by
      linarith [hid₁]
    rw [h1, hrCharReal, hsCharReal, htaxReal, h2]
    ring
  calc _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) (_root_.GD.N0230.N0668.d001343 lambda r s)
      = ENNReal.ofReal
          ((_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
            (_root_.GD.N0230.N0668.d001343 lambda r s)).toReal) :=
        (ENNReal.ofReal_toReal (hfinRepair _)).symm
    _ = ENNReal.ofReal (g.d009239 ^ 2 *
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0668.d001343 lambda r s)).toReal) := by
        rw [hcombine]
    _ = ENNReal.ofReal (g.d009239 ^ 2) *
          ENNReal.ofReal
            ((_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0668.d001343 lambda r s)).toReal) :=
        ENNReal.ofReal_mul (sq_nonneg _)
    _ = ENNReal.ofReal (g.d009239 ^ 2) *
          _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0230.N0668.d001343 lambda r s) := by
        rw [ENNReal.ofReal_toReal (hfinRepair _)]




noncomputable def d017115 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hchar : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (htax : _root_.GD.N0232.N0720.N1105.d017112 m n p s.value) :
    _root_.GD.N0232.N0720.N1159.d014639 m n where
  value := _root_.GD.N0230.N0668.d001343 2⁻¹ p s.value
  finiteRisk := _root_.GD.N0232.N0720.N1128.d017096 m n 2⁻¹ p s.value
    (_root_.GD.N0232.N0720.N1159.d014644 m n s p hp) s.finiteRisk
  riskCharacter := _root_.GD.N0232.N0720.N1105.d017114
    m n 2⁻¹ p s.value
    (_root_.GD.N0232.N0720.N1159.d014644 m n s p hp) s.finiteRisk
    hchar s.riskCharacter htax

theorem d017116 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hchar : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (htax : _root_.GD.N0232.N0720.N1105.d017112 m n p s.value) :
    (_root_.GD.N0232.N0720.N1105.d017115 m n s p hp hchar htax).value ∈
      _root_.GD.N0232.N0720.N1159.d014630 m n s.value := by
  have hs : s.value ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
  exact (_root_.GD.N0232.N0720.N1159.d014632 m n s.value) hp hs
    (by norm_num) (by norm_num) (by norm_num)

theorem d017117 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hchar : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (htax : _root_.GD.N0232.N0720.N1105.d017112 m n p s.value) :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1105.d017115 m n s p hp hchar htax).value :=
  _root_.GD.N0232.N0720.N1105.d017116 m n s p hp hchar htax




theorem d017118
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (t : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (ht : t ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n t‖ ^ 2 := by
  have hmem : _root_.GD.N0232.N0720.N1159.d014633 m n t ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    _root_.GD.N0230.N0608.d000678 (_root_.GD.N0232.N0720.N1080.d014182 m n) ht
      (_root_.GD.N0232.N0720.N1159.d014634 m n t).1
  have hmin := (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.2 _ hmem
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at hmin
  simp only [zero_sub, norm_neg] at hmin
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp hmin




theorem d017119 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hchar : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (htax : _root_.GD.N0232.N0720.N1105.d017112 m n p s.value) :
    _root_.GD.N0232.N0720.N1201.d015333 m n
        (_root_.GD.N0232.N0720.N1105.d017115 m n s p hp hchar htax) ≤
      _root_.GD.N0232.N0720.N1201.d015333 m n s / 2 +
        (‖p‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) / 2 -
        ‖p - s.value‖ ^ 2 / 4 := by
  have hmono := _root_.GD.N0232.N0720.N1105.d017118
    m n s _ (_root_.GD.N0232.N0720.N1105.d017116 m n s p hp hchar htax)
  have hmid : _root_.GD.N0230.N0668.d001343 (2⁻¹ : ℝ) p s.value =
      (2⁻¹ : ℝ) • (p + s.value) := by
    unfold _root_.GD.N0230.N0668.d001343
    rw [smul_add]
    congr 1
    norm_num
  have hsq : ‖_root_.GD.N0230.N0668.d001343 (2⁻¹ : ℝ) p s.value‖ ^ 2 =
      ‖p + s.value‖ ^ 2 / 4 := by
    rw [hmid, norm_smul, mul_pow]
    rw [Real.norm_eq_abs]
    norm_num
    ring
  have hadd := @norm_add_sq_real (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) _ _ p s.value
  have hsub := @norm_sub_sq_real (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) _ _ p s.value
  have hpar : ‖_root_.GD.N0230.N0668.d001343 (2⁻¹ : ℝ) p s.value‖ ^ 2 =
      ‖p‖ ^ 2 / 2 + ‖s.value‖ ^ 2 / 2 - ‖p - s.value‖ ^ 2 / 4 := by
    rw [hsq]
    linarith
  show ‖_root_.GD.N0230.N0668.d001343 (2⁻¹ : ℝ) p s.value‖ ^ 2 -
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n
        (_root_.GD.N0232.N0720.N1105.d017115 m n s p hp hchar htax).value‖ ^ 2 ≤ _
  have hgapS : _root_.GD.N0232.N0720.N1201.d015333 m n s =
      ‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := rfl
  linarith





def d017120 (kappa : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
    p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value ∧
    _root_.GD.N0232.N0720.N1159.d014638 m n p ∧
    _root_.GD.N0232.N0720.N1105.d017112 m n p s.value ∧
    ‖p‖ ^ 2 ≤ ‖s.value‖ ^ 2 - kappa * _root_.GD.N0232.N0720.N1201.d015333 m n s



theorem d017121 (kappa : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hcap : 0 < _root_.GD.N0232.N0720.N1201.d015333 m n s →
      _root_.GD.N0232.N0720.N1105.d017120 m n kappa s) :
    ∃ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value t.value ∧
      _root_.GD.N0232.N0720.N1201.d015333 m n t ≤
        (1 - kappa / 2) * _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  rcases (_root_.GD.N0232.N0720.N1201.d015334 m n s).lt_or_eq with hpos | hzero
  · obtain ⟨p, hp, hchar, htax, hnorm⟩ := hcap hpos
    refine ⟨_root_.GD.N0232.N0720.N1105.d017115 m n s p hp hchar htax,
      _root_.GD.N0232.N0720.N1105.d017117 m n s p hp hchar htax, ?_⟩
    have hhalv := _root_.GD.N0232.N0720.N1105.d017119 m n s p hp hchar htax
    have hdist : (0 : ℝ) ≤ ‖p - s.value‖ ^ 2 / 4 := by positivity
    have hgapS : _root_.GD.N0232.N0720.N1201.d015333 m n s =
        ‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := rfl
    linarith
  · refine ⟨s, _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value, ?_⟩
    rw [← hzero, mul_zero]





theorem d017122
    (hm : 2 ≤ m) (hn : 2 ≤ n) (s₀ : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s₀.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (kappa : ℝ) (hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (hcap : ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s₀.value s.value →
      0 < _root_.GD.N0232.N0720.N1201.d015333 m n s →
      _root_.GD.N0232.N0720.N1105.d017120 m n kappa s) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let Carrier := {s : _root_.GD.N0232.N0720.N1159.d014639 m n //
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s₀.value s.value}
  let step : Carrier → Carrier := fun s =>
    ⟨Classical.choose (_root_.GD.N0232.N0720.N1105.d017121 m n kappa s.1
        (fun hpos => hcap s.1 s.2 hpos)),
      _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (Classical.choose_spec (_root_.GD.N0232.N0720.N1105.d017121 m n kappa s.1
          (fun hpos => hcap s.1 s.2 hpos))).1 s.2⟩
  let chain : ℕ → Carrier := fun j =>
    Nat.rec ⟨s₀, _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s₀.value⟩
      (fun _ prev => step prev) j
  have hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      ((chain j).1).value ((chain (j + 1)).1).value := by
    intro j
    exact (Classical.choose_spec
      (_root_.GD.N0232.N0720.N1105.d017121 m n kappa (chain j).1
        (fun hpos => hcap (chain j).1 (chain j).2 hpos))).1
  have hfactor0 : (0 : ℝ) ≤ 1 - kappa / 2 := by linarith
  have hfactor1 : 1 - kappa / 2 < 1 := by linarith
  have hbound : ∀ j, _root_.GD.N0232.N0720.N1201.d015333 m n (chain j).1 ≤
      (1 - kappa / 2) ^ j * _root_.GD.N0232.N0720.N1201.d015333 m n s₀ := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, one_mul]
      exact le_rfl
    | succ j ih =>
      have hstep := (Classical.choose_spec
        (_root_.GD.N0232.N0720.N1105.d017121 m n kappa (chain j).1
          (fun hpos => hcap (chain j).1 (chain j).2 hpos))).2
      calc _root_.GD.N0232.N0720.N1201.d015333 m n (chain (j + 1)).1
          ≤ (1 - kappa / 2) *
              _root_.GD.N0232.N0720.N1201.d015333 m n (chain j).1 := hstep
        _ ≤ (1 - kappa / 2) *
              ((1 - kappa / 2) ^ j *
                _root_.GD.N0232.N0720.N1201.d015333 m n s₀) :=
            mul_le_mul_of_nonneg_left ih hfactor0
        _ = (1 - kappa / 2) ^ (j + 1) *
              _root_.GD.N0232.N0720.N1201.d015333 m n s₀ := by ring
  have hgapTend : Tendsto
      (fun j => _root_.GD.N0232.N0720.N1201.d015333 m n (chain j).1)
      atTop (nhds 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hfactor0 hfactor1
    have hmul := hpow.mul_const (_root_.GD.N0232.N0720.N1201.d015333 m n s₀)
    rw [zero_mul] at hmul
    exact squeeze_zero
      (fun j => _root_.GD.N0232.N0720.N1201.d015334 m n (chain j).1)
      hbound hmul
  exact _root_.GD.N0232.N0720.N1102.d015437 m n hm hn
    (fun j => (chain j).1) hdesc hgapTend hstrict



theorem d017123
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (kappa : ℝ) (hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (hcap : ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) s.value →
      0 < _root_.GD.N0232.N0720.N1201.d015333 m n s →
      _root_.GD.N0232.N0720.N1105.d017120 m n kappa s) :
    _root_.GD.N0232.N0720.N1159.d014661 m n :=
  _root_.GD.N0232.N0720.N1105.d017122 m n hm hn
    (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)
    (_root_.GD.N0232.N0720.N1029.d015368 m n hm hn)
    kappa hk hk1 hcap

end

end N1105
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1105.d017114
#print axioms _root_.GD.N0232.N0720.N1105.d017119
#print axioms _root_.GD.N0232.N0720.N1105.d017121
#print axioms _root_.GD.N0232.N0720.N1105.d017122
#print axioms _root_.GD.N0232.N0720.N1105.d017123
