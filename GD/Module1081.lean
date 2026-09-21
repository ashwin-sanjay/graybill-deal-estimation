import GD.Module0244
import GD.Module0982
import GD.Module1077











set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0232.N0720.N1220

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1126 _root_.GD.N0232.N0720.N1125
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0632

variable (m n : ℕ)

theorem d017300
    (hm : 2 ≤ m) (hn : 2 ≤ n) (cap : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hcap : ∀ θ, 0 ≤ cap θ) :
    (∃ p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n), ∀ θ,
      _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ ENNReal.ofReal (cap θ)) ↔
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) → ∀ a : ℝ,
        (∀ p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n), _root_.GD.N0232.N0720.N1159.d014637 m n p →
          a ≤ ∑ θ ∈ F, w θ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ p).toReal) →
        a ≤ ∑ θ ∈ F, w θ * cap θ := by
  apply _root_.GD.N0230.N0632.d003536 (_root_.GD.N0232.N0720.N1080.d014182 m n)
    (fun θ p q a b ha hb hab => _root_.GD.N0230.N0602.d000121
      (_root_.GD.N0232.N0720.N1080.d014173 m n θ) θ.location p q ha hb hab)
    (anchor := _root_.GD.N0232.N0720.N1080.d014169)
  · intro θ c
    simpa [_root_.GD.N0230.N0602.d000118, _root_.GD.N0232.N0720.N1080.d014182] using _root_.GD.N0230.N0602.d000122 (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun _ : Unit => _root_.GD.N0232.N0720.N1080.d014171 m n θ) (fun _ => θ.location)
      (fun _ => ENNReal.ofReal c) (fun _ => _root_.GD.N0232.N0720.N1080.d014173 m n θ)
  · intro p
    simpa using _root_.GD.N0232.N0720.N1080.d014190 m n p
  · refine ⟨_root_.GD.N0232.N0720.N1080.d014181 m n hm hn, fun θ => ?_⟩
    rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn θ]
    exact ENNReal.ofReal_ne_top
  · exact hcap


def d017301 (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1125.d017250 (m := m) (n := n)
    (fun θ : F => θ.val) (fun θ => w θ.val)

theorem d017302
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤ ‖p‖ ^ 2 + ∑ θ ∈ F, w θ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ p).toReal := by
  classical
  have h := _root_.GD.N0232.N0720.N1125.d017255
    (m := m) (n := n) (fun θ : F => θ.val) (fun θ => w θ.val)
    (fun θ => hw θ.val θ.property) p (fun θ => hp θ.val)
  have hnonneg : 0 ≤ ∫ ω,
      _root_.GD.N0232.N0720.N1126.d016415 (fun θ : F => θ.val) (fun θ => w θ.val) ω *
        (p ω - _root_.GD.N0232.N0720.N1126.d016416 (fun θ : F => θ.val)
          (fun θ => w θ.val) ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    apply integral_nonneg
    intro ω
    apply mul_nonneg _ (sq_nonneg _)
    exact (_root_.GD.N0230.N0617.d000169
      (fun θ : F => w θ.val) (_root_.GD.N0232.N0720.N1126.d016413 (fun θ : F => θ.val))
      (fun θ => hw θ.val θ.property) (_root_.GD.N0232.N0720.N1126.d016419 _) ω).le
  simp only [_root_.GD.N0232.N0720.N1125.d017249] at h
  rw [Finset.sum_coe_sort F (fun θ => w θ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ p).toReal)] at h
  change _ = _ + _root_.GD.N0232.N0720.N1220.d017301 m n F w at h
  linarith

theorem d017303
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ) :
    ∃ p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n), _root_.GD.N0232.N0720.N1159.d014637 m n p ∧
      ‖p‖ ^ 2 + ∑ θ ∈ F, w θ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ p).toReal = _root_.GD.N0232.N0720.N1220.d017301 m n F w := by
  classical
  let packet : F → _root_.GD.N0232.N0720.N1080.d014168 := fun θ => θ.val
  let weight : F → ℝ := fun θ => w θ.val
  have hw' : ∀ θ, 0 ≤ weight θ := fun θ => hw θ.val θ.property
  let p := _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet weight hw'
  refine ⟨p, _root_.GD.N0232.N0720.N1126.d016428 packet weight hw', ?_⟩
  have h : ‖p‖ ^ 2 + (∑ θ : F, w θ.val * (_root_.GD.N0232.N0720.N1080.d014182 m n θ.val p).toReal) =
      _root_.GD.N0232.N0720.N1220.d017301 m n F w :=
    _root_.GD.N0232.N0720.N1125.d017257 (m := m) (n := n) packet weight hw'
  rw [Finset.sum_coe_sort F (fun θ => w θ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ p).toReal)] at h
  exact h

theorem d017304
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ) :
    0 ≤ _root_.GD.N0232.N0720.N1220.d017301 m n F w := by
  obtain ⟨p, _, heq⟩ := _root_.GD.N0232.N0720.N1220.d017303 m n F w hw
  rw [← heq]
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun θ hθ =>
    mul_nonneg (hw θ hθ) ENNReal.toReal_nonneg)



theorem d017305
    (hm : 2 ≤ m) (hn : 2 ≤ n) (cap : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hcap : ∀ θ, 0 ≤ cap θ) :
    (∃ p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n), ∀ θ,
      _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ ENNReal.ofReal (cap θ)) ↔
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
        _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤ cap _root_.GD.N0232.N0720.N1080.d014169 + ∑ θ ∈ F, w θ * cap θ := by
  constructor
  · rintro ⟨p, hp⟩ F w hw
    have hpF : _root_.GD.N0232.N0720.N1159.d014637 m n p := fun θ =>
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hp θ)
    apply (_root_.GD.N0232.N0720.N1220.d017302 m n F w hw p hpF).trans
    apply add_le_add
    · have hb := hp _root_.GD.N0232.N0720.N1080.d014169
      rw [_root_.GD.N0232.N0720.N1080.d014190 m n] at hb
      simpa using (ENNReal.ofReal_le_ofReal_iff (hcap _root_.GD.N0232.N0720.N1080.d014169)).mp hb
    · apply Finset.sum_le_sum
      intro θ hθ
      apply mul_le_mul_of_nonneg_left _ (hw θ hθ)
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hp θ)).trans_eq
        (ENNReal.toReal_ofReal (hcap θ))
  · intro htest
    apply (_root_.GD.N0232.N0720.N1220.d017300 m n hm hn cap hcap).mpr
    intro F w hw a ha
    by_contra hnot
    have hgap : 0 < a - ∑ θ ∈ F, w θ * cap θ := sub_pos.mpr (lt_of_not_ge hnot)
    let t := (cap _root_.GD.N0232.N0720.N1080.d014169 + 1) / (a - ∑ θ ∈ F, w θ * cap θ)
    have ht : 0 < t := div_pos (by linarith [hcap _root_.GD.N0232.N0720.N1080.d014169]) hgap
    have htw : ∀ θ ∈ F, 0 ≤ t * w θ := fun θ hθ => mul_nonneg ht.le (hw θ hθ)
    obtain ⟨p, hp, heq⟩ := _root_.GD.N0232.N0720.N1220.d017303 m n F
      (fun θ => t * w θ) htw
    have htest' := htest F (fun θ => t * w θ) htw
    have ha' := mul_le_mul_of_nonneg_left (ha p hp) ht.le
    have hsum (f : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) :
        (∑ θ ∈ F, (t * w θ) * f θ) = t * ∑ θ ∈ F, w θ * f θ := by
      simp only [mul_assoc, Finset.mul_sum]
    rw [hsum] at heq htest'
    have htgap : t * (a - ∑ θ ∈ F, w θ * cap θ) = cap _root_.GD.N0232.N0720.N1080.d014169 + 1 :=
      div_mul_cancel₀ _ hgap.ne'
    nlinarith [sq_nonneg ‖p‖]

theorem d017306
    (hm : 2 ≤ m) (hn : 2 ≤ n) (c : ℝ) (hc : 0 ≤ c) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≤ ENNReal.ofReal c ↔
      ∃ p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n), ∀ θ,
        _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ ENNReal.ofReal (c * _root_.GD.N0232.N0720.N1257.d015508 m n θ) := by
  constructor
  · intro hv
    obtain ⟨e, he, heq⟩ :=
      _root_.GD.N0232.N0720.N1222.d015570 m n hm hn
    have hb : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ e ≤ ENNReal.ofReal (c * _root_.GD.N0232.N0720.N1257.d015508 m n θ) := by
      intro θ
      apply (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) c hc θ e).mp
      have hh : _root_.GD.N0232.N0720.N1256.d015547 m n θ e ≤ _root_.GD.N0232.N0720.N1256.d015548 m n e :=
        le_iSup (fun η => _root_.GD.N0232.N0720.N1256.d015547 m n η e) θ
      exact hh.trans (heq.symm ▸ hv)
    obtain ⟨p, hp, _⟩ := _root_.GD.N0232.N0720.N1257.d015531 m n c e he.1.1 hb
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    apply (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 m n)
      (S := _root_.GD.N0232.N0720.N1256.d015545 m n) (d := _root_.GD.N0232.N0720.N1214.d014265 m n p)
      (_root_.GD.N0232.N0720.N1214.d014266 m n p)).trans
    apply iSup_le
    intro θ
    apply (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) c hc θ _).mpr
    rw [_root_.GD.N0232.N0720.N1215.d014286]
    exact hp θ



def d017307 (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1257.d015508 m n _root_.GD.N0232.N0720.N1080.d014169 + ∑ θ ∈ F, w θ * _root_.GD.N0232.N0720.N1257.d015508 m n θ

theorem d017308
    (hm : 2 ≤ m) (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ) : 0 < _root_.GD.N0232.N0720.N1220.d017307 m n F w := by
  apply add_pos_of_pos_of_nonneg (_root_.GD.N0232.N0720.N1257.d015510 m n (by omega) _root_.GD.N0232.N0720.N1080.d014169)
  exact Finset.sum_nonneg fun θ hθ => mul_nonneg (hw θ hθ) (_root_.GD.N0232.N0720.N1257.d015509 m n θ)



theorem d017309
    (hm : 2 ≤ m) (hn : 2 ≤ n) (c : ℝ) (hc : 0 ≤ c) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≤ ENNReal.ofReal c ↔
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
        _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤ c * _root_.GD.N0232.N0720.N1220.d017307 m n F w := by
  rw [_root_.GD.N0232.N0720.N1220.d017306 m n hm hn c hc,
    _root_.GD.N0232.N0720.N1220.d017305 m n hm hn
      (fun θ => c * _root_.GD.N0232.N0720.N1257.d015508 m n θ)
      (fun θ => mul_nonneg hc (_root_.GD.N0232.N0720.N1257.d015509 m n θ))]
  simp only [_root_.GD.N0232.N0720.N1220.d017307, mul_add, Finset.mul_sum, mul_left_comm]



def d017310 : ℝ≥0∞ :=
  ⨆ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (_ : ∀ θ ∈ F, 0 ≤ w θ),
    ENNReal.ofReal (_root_.GD.N0232.N0720.N1220.d017301 m n F w / _root_.GD.N0232.N0720.N1220.d017307 m n F w)



theorem d017311 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n = _root_.GD.N0232.N0720.N1220.d017310 m n := by
  apply le_antisymm
  · by_cases htop : _root_.GD.N0232.N0720.N1220.d017310 m n = ⊤
    · rw [htop]
      exact le_top
    have hcut : _root_.GD.N0232.N0720.N1256.d015549 m n ≤ ENNReal.ofReal (_root_.GD.N0232.N0720.N1220.d017310 m n).toReal := by
      apply (_root_.GD.N0232.N0720.N1220.d017309 m n hm hn _ ENNReal.toReal_nonneg).mpr
      intro F w hw
      have hb : ENNReal.ofReal (_root_.GD.N0232.N0720.N1220.d017301 m n F w / _root_.GD.N0232.N0720.N1220.d017307 m n F w) ≤
          _root_.GD.N0232.N0720.N1220.d017310 m n :=
        le_iSup_of_le F (le_iSup_of_le w (le_iSup_of_le hw le_rfl))
      rw [← ENNReal.ofReal_toReal htop] at hb
      have hr := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hb
      exact (div_le_iff₀ (_root_.GD.N0232.N0720.N1220.d017308 m n hm F w hw)).mp hr
    rwa [ENNReal.ofReal_toReal htop] at hcut
  · by_cases htop : _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤
    · rw [htop]
      exact le_top
    have hcut := (_root_.GD.N0232.N0720.N1220.d017309 m n hm hn
      (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal ENNReal.toReal_nonneg).mp
      (le_of_eq (ENNReal.ofReal_toReal htop).symm)
    apply iSup_le
    intro F
    apply iSup_le
    intro w
    apply iSup_le
    intro hw
    have hr := (div_le_iff₀ (_root_.GD.N0232.N0720.N1220.d017308 m n hm F w hw)).mpr (hcut F w hw)
    exact (ENNReal.ofReal_le_ofReal hr).trans_eq (ENNReal.ofReal_toReal htop)

theorem d017312 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015551 m n) = _root_.GD.N0232.N0720.N1220.d017310 m n := by
  rw [← _root_.GD.N0232.N0720.N1256.d015559 m n hm]
  exact _root_.GD.N0232.N0720.N1220.d017311 m n hm hn

theorem d017313 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015552 m n) = _root_.GD.N0232.N0720.N1220.d017310 m n := by
  rw [← _root_.GD.N0232.N0720.N1256.d015560 m n hm hn]
  exact _root_.GD.N0232.N0720.N1220.d017312 m n hm hn



theorem d017314
    (hm : 2 ≤ m) (hn : 2 ≤ n) (c : ℝ) (hc : 0 ≤ c) :
    ENNReal.ofReal c < _root_.GD.N0232.N0720.N1256.d015549 m n ↔
      ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ c * _root_.GD.N0232.N0720.N1220.d017307 m n F w < _root_.GD.N0232.N0720.N1220.d017301 m n F w := by
  classical
  have h := (_root_.GD.N0232.N0720.N1220.d017309 m n hm hn c hc).not
  push Not at h
  exact h




theorem d017315
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) →
          _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤ c * _root_.GD.N0232.N0720.N1220.d017307 m n F w := by
  constructor
  · intro hv
    refine ⟨(_root_.GD.N0232.N0720.N1256.d015549 m n).toReal, ENNReal.toReal_nonneg, ?_⟩
    apply (_root_.GD.N0232.N0720.N1220.d017309 m n hm hn _ ENNReal.toReal_nonneg).mp
    exact le_of_eq (ENNReal.ofReal_toReal hv).symm
  · rintro ⟨c, hc, hb⟩
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((_root_.GD.N0232.N0720.N1220.d017309 m n hm hn c hc).mpr hb)

end
end GD.N0232.N0720.N1220

#print axioms _root_.GD.N0232.N0720.N1220.d017300
#print axioms _root_.GD.N0232.N0720.N1220.d017305
#print axioms _root_.GD.N0232.N0720.N1220.d017309
#print axioms _root_.GD.N0232.N0720.N1220.d017311
#print axioms _root_.GD.N0232.N0720.N1220.d017312
#print axioms _root_.GD.N0232.N0720.N1220.d017313
#print axioms _root_.GD.N0232.N0720.N1220.d017314
#print axioms _root_.GD.N0232.N0720.N1220.d017315
