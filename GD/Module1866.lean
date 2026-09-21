import GD.Module1865

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0082

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0230.N0611
open _root_.GD.N0076.N0313

def d030598 (J : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ J

theorem d030599 (J : ℕ) : 0 ≤ _root_.GD.N0082.d030598 J := by
  unfold _root_.GD.N0082.d030598
  exact sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))

theorem d030600 (J : ℕ) : _root_.GD.N0082.d030598 J < 1 := by
  unfold _root_.GD.N0082.d030598
  exact sub_lt_self 1 (pow_pos (by norm_num) J)

theorem d030601 {c : ℝ} (hc : c < 1) :
    ∃ J : ℕ, 1 ≤ J ∧ c < _root_.GD.N0082.d030598 J := by
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (sub_pos.mpr hc)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨j + 1, by omega, ?_⟩
  have hpow : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ j := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) (by norm_num)
  unfold _root_.GD.N0082.d030598
  linarith

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d030602 : Prop :=
  ∀ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n, 1 ≤ _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) d

def d030603 : Prop :=
  ∃ J : ℕ, 1 ≤ J ∧ ∃ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable d ∧
    ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤
      ENNReal.ofReal (_root_.GD.N0082.d030598 J) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ

theorem d030604 : _root_.GD.N0082.d030602 m n hm hn ↔ 1 ≤ _root_.GD.N0076.N0313.d030569 m n hm hn := by
  constructor
  · intro h
    exact le_iInf fun d => le_iInf fun hd => h d hd
  · intro h d hd
    exact h.trans (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0076.N0313.d030568 m n hm hn) hd)

theorem d030605 : _root_.GD.N0082.d030602 m n hm hn ↔ _root_.GD.N0076.N0313.d030569 m n hm hn = 1 := by
  rw [_root_.GD.N0082.d030604]
  exact ⟨fun h => le_antisymm (_root_.GD.N0076.N0313.d030573 m n hm hn) h,
    fun h => h.symm.le⟩

theorem d030606 : ¬ _root_.GD.N0082.d030602 m n hm hn ↔ _root_.GD.N0076.N0313.d030569 m n hm hn < 1 := by
  rw [_root_.GD.N0082.d030604, not_le]

theorem d030607 {J : ℕ} {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : Measurable d)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤
      ENNReal.ofReal (_root_.GD.N0082.d030598 J) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ) :
    d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n := by
  refine ⟨hd, fun θ => ne_top_of_le_ne_top ?_ (hcap θ)⟩
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ)

theorem d030608 {J : ℕ} {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} :
    (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤
      ENNReal.ofReal (_root_.GD.N0082.d030598 J) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ) ↔
      _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) d ≤ ENNReal.ofReal (_root_.GD.N0082.d030598 J) := by
  rw [_root_.GD.N0230.N0611.d003519]
  apply forall_congr'
  intro θ
  unfold _root_.GD.N0076.N0313.d030568
  exact (ENNReal.div_le_iff (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn θ)
    (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ)).symm

theorem d030609 :
    _root_.GD.N0082.d030603 m n hm hn ↔ _root_.GD.N0076.N0313.d030569 m n hm hn < 1 := by
  constructor
  · rintro ⟨J, _hJ, d, hd, hcap⟩
    have hfinite := _root_.GD.N0082.d030607 m n hm hn hd hcap
    have hbound := (_root_.GD.N0082.d030608 m n hm hn).mp hcap
    exact (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0076.N0313.d030568 m n hm hn) hfinite).trans_lt
      (hbound.trans_lt (ENNReal.ofReal_lt_one.mpr (_root_.GD.N0082.d030600 J)))
  · intro hv
    have hreal : (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal < 1 :=
      ENNReal.toReal_lt_of_lt_ofReal (by simpa using hv)
    obtain ⟨J, hJ, hc⟩ := _root_.GD.N0082.d030601 hreal
    have hvc : _root_.GD.N0076.N0313.d030569 m n hm hn < ENNReal.ofReal (_root_.GD.N0082.d030598 J) := by
      rw [← ENNReal.ofReal_toReal (_root_.GD.N0076.N0313.d030574 m n hm hn)]
      exact (ENNReal.ofReal_lt_ofReal_iff
        (lt_of_le_of_lt ENNReal.toReal_nonneg hc)).mpr hc
    obtain ⟨p, hp⟩ := _root_.GD.N0076.N0313.d030584 m n hm hn _ (_root_.GD.N0082.d030599 J) hvc
    refine ⟨J, hJ, _root_.GD.N0232.N0720.N1214.d014265 m n p, _root_.GD.N0232.N0720.N1214.d014266 m n p, ?_⟩
    intro θ
    rw [_root_.GD.N0232.N0720.N1215.d014286]
    have h := hp θ
    rw [ENNReal.ofReal_mul (_root_.GD.N0082.d030599 J), _root_.GD.N0076.N0313.d030567] at h
    exact h

theorem d030610 :
    ¬ _root_.GD.N0082.d030602 m n hm hn ↔ _root_.GD.N0082.d030603 m n hm hn :=
  (_root_.GD.N0082.d030606 m n hm hn).trans
    (_root_.GD.N0082.d030609 m n hm hn).symm

theorem d030611 :
    _root_.GD.N0082.d030603 m n hm hn ↔
      ∃ J : ℕ, 1 ≤ J ∧ ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n,
        (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤
          ENNReal.ofReal (_root_.GD.N0082.d030598 J) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ) ∧
        _root_.GD.N0076.N0313.d030591 m n d ∧ ¬ _root_.GD.N0076.N0313.d030592 m n d ∧
        _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) d = _root_.GD.N0076.N0313.d030569 m n hm hn := by
  constructor
  · intro h
    have hv := (_root_.GD.N0082.d030609 m n hm hn).mp h
    have hreal : (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal < 1 :=
      ENNReal.toReal_lt_of_lt_ofReal (by simpa using hv)
    obtain ⟨J, hJ, hc⟩ := _root_.GD.N0082.d030601 hreal
    obtain ⟨d, hd, _hstrict, ht, hna, hvalue⟩ :=
      _root_.GD.N0076.N0313.d030596 m n hm hn
    refine ⟨J, hJ, d, hd, ?_, ht, hna, hvalue⟩
    apply (_root_.GD.N0082.d030608 m n hm hn).mpr
    rw [hvalue, ← ENNReal.ofReal_toReal (_root_.GD.N0076.N0313.d030574 m n hm hn)]
    exact ENNReal.ofReal_le_ofReal hc.le
  · rintro ⟨J, hJ, d, hd, hcap, _ht, _hna, _hvalue⟩
    exact ⟨J, hJ, d, hd.1, hcap⟩

theorem d030612 :
    (¬ _root_.GD.N0082.d030602 3 3 (by omega) (by omega) ↔ _root_.GD.N0082.d030603 3 3 (by omega) (by omega)) ∧
    (_root_.GD.N0082.d030602 3 3 (by omega) (by omega) ↔ _root_.GD.N0076.N0313.d030569 3 3 (by omega) (by omega) = 1) :=
  ⟨_root_.GD.N0082.d030610 3 3 (by omega) (by omega),
    _root_.GD.N0082.d030605 3 3 (by omega) (by omega)⟩

end

end GD.N0082

#print axioms _root_.GD.N0082.d030601
#print axioms _root_.GD.N0082.d030605
#print axioms _root_.GD.N0082.d030609
#print axioms _root_.GD.N0082.d030610
#print axioms _root_.GD.N0082.d030611
#print axioms _root_.GD.N0082.d030612
