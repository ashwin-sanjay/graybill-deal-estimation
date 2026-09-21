



























import Mathlib
import GD.Module0401
import GD.Module0405

set_option maxHeartbeats 64000000
set_option maxRecDepth 4096

namespace GD.N0155
open MeasureTheory

private theorem d006240 {f : ℝ → ℝ} {a b x : ℝ}
    (h : HasDerivAt f a x) (hab : a = b) : HasDerivAt f b x := hab ▸ h


noncomputable def d006241 (θ u : ℝ) : ℝ := 1 - u + θ * u

theorem d006242 (θ : ℝ) : Continuous (_root_.GD.N0155.d006241 θ) := by
  unfold _root_.GD.N0155.d006241; fun_prop

theorem d006243 {θ : ℝ} (hθ : 0 < θ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    0 < _root_.GD.N0155.d006241 θ u := by
  unfold _root_.GD.N0155.d006241
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]; norm_num
  · have h2 : 0 < θ * u := mul_pos hθ h
    have h3 : (0:ℝ) ≤ 1 - u := by linarith
    linarith

theorem d006244 (θ u : ℝ) : HasDerivAt (fun x => _root_.GD.N0155.d006241 θ x) (θ - 1) u := by
  unfold _root_.GD.N0155.d006241
  have h := ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)).add
    ((hasDerivAt_id u).const_mul θ)
  have hv : (0:ℝ) - 1 + θ * 1 = θ - 1 := by ring
  rw [hv] at h
  exact h

theorem d006245 {x : ℝ} (hx : x ∈ Set.uIcc (0:ℝ) 1) : 0 ≤ x ∧ x ≤ 1 := by
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
  exact ⟨hx.1, hx.2⟩


theorem d006246 {θ : ℝ} (hθ : 0 < θ) (ht1 : θ ≠ 1) (k : ℕ) :
    ∫ u in (0:ℝ)..1, _root_.GD.N0155.d006241 θ u ^ k
      = (θ ^ (k + 1) - 1) / ((k + 1 : ℝ) * (θ - 1)) := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hder : ∀ u ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x => _root_.GD.N0155.d006241 θ x ^ (k + 1) / ((k + 1 : ℝ) * (θ - 1)))
        (_root_.GD.N0155.d006241 θ u ^ k) u := by
    intro u _
    refine _root_.GD.N0155.d006240
      (((_root_.GD.N0155.d006244 θ u).pow (k + 1)).div_const ((k + 1 : ℝ) * (θ - 1))) ?_
    rw [Nat.add_sub_cancel]
    have ec : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
      first
        | exact Nat.cast_add_one k
        | exact Nat.cast_succ k
        | push_cast; ring
        | norm_cast
    try rw [ec]
    first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf
  have hint : IntervalIntegrable (fun u => _root_.GD.N0155.d006241 θ u ^ k) volume 0 1 :=
    ((_root_.GD.N0155.d006242 θ).pow k).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
  have e1 : _root_.GD.N0155.d006241 θ 1 = θ := by unfold _root_.GD.N0155.d006241; ring
  have e0 : _root_.GD.N0155.d006241 θ 0 = 1 := by unfold _root_.GD.N0155.d006241; ring
  rw [e1, e0, one_pow]
  first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf


theorem d006247 {θ : ℝ} (hθ : 0 < θ) (ht1 : θ ≠ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    ∫ u in (0:ℝ)..1, 1 / _root_.GD.N0155.d006241 θ u ^ n
      = (1 - 1 / θ ^ (n - 1)) / ((n - 1 : ℝ) * (θ - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hθ0 : θ ≠ 0 := ne_of_gt hθ
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hder : ∀ u ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x => -1 / (((m : ℝ) + 1) * (θ - 1)) * (_root_.GD.N0155.d006241 θ x ^ (m + 1))⁻¹)
        (1 / _root_.GD.N0155.d006241 θ u ^ (m + 2)) u := by
    intro u hu
    obtain ⟨hu0, hu1⟩ := _root_.GD.N0155.d006245 hu
    have hd : 0 < _root_.GD.N0155.d006241 θ u := _root_.GD.N0155.d006243 hθ hu0 hu1
    have hdne : _root_.GD.N0155.d006241 θ u ≠ 0 := ne_of_gt hd
    refine _root_.GD.N0155.d006240
      ((((_root_.GD.N0155.d006244 θ u).pow (m + 1)).inv (pow_ne_zero _ hdne)).const_mul
        (-1 / (((m : ℝ) + 1) * (θ - 1)))) ?_
    rw [Nat.add_sub_cancel]
    have ec : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
      first
        | exact Nat.cast_add_one m
        | exact Nat.cast_succ m
        | push_cast; ring
        | norm_cast
    try rw [ec]
    try simp only [Pi.pow_apply]
    first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf
  have hint : IntervalIntegrable (fun u => 1 / _root_.GD.N0155.d006241 θ u ^ (m + 2)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const ((_root_.GD.N0155.d006242 θ).pow (m + 2)).continuousOn
    intro x hx
    obtain ⟨hx0, hx1⟩ := _root_.GD.N0155.d006245 hx
    exact pow_ne_zero _ (ne_of_gt (_root_.GD.N0155.d006243 hθ hx0 hx1))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
  have e1 : _root_.GD.N0155.d006241 θ 1 = θ := by unfold _root_.GD.N0155.d006241; ring
  have e0 : _root_.GD.N0155.d006241 θ 0 = 1 := by unfold _root_.GD.N0155.d006241; ring
  rw [e1, e0, one_pow]
  have e2 : m + 2 - 1 = m + 1 := by omega
  rw [e2]
  have e3 : ((m + 2 : ℕ) : ℝ) - 1 = (m : ℝ) + 1 := by push_cast; ring
  rw [e3]
  first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf


theorem d006248 {θ : ℝ} (hθ : 0 < θ) (ht1 : θ ≠ 1) :
    ∫ u in (0:ℝ)..1, 1 / _root_.GD.N0155.d006241 θ u = Real.log θ / (θ - 1) := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hder : ∀ u ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun x => Real.log (_root_.GD.N0155.d006241 θ x) / (θ - 1)) (1 / _root_.GD.N0155.d006241 θ u) u := by
    intro u hu
    obtain ⟨hu0, hu1⟩ := _root_.GD.N0155.d006245 hu
    have hd : 0 < _root_.GD.N0155.d006241 θ u := _root_.GD.N0155.d006243 hθ hu0 hu1
    refine _root_.GD.N0155.d006240
      (((_root_.GD.N0155.d006244 θ u).log (ne_of_gt hd)).div_const (θ - 1)) ?_
    first | (field_simp; done) | (field_simp; ring)
  have hint : IntervalIntegrable (fun u => 1 / _root_.GD.N0155.d006241 θ u) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (_root_.GD.N0155.d006242 θ).continuousOn
    intro x hx
    obtain ⟨hx0, hx1⟩ := _root_.GD.N0155.d006245 hx
    exact ne_of_gt (_root_.GD.N0155.d006243 hθ hx0 hx1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
  have e1 : _root_.GD.N0155.d006241 θ 1 = θ := by unfold _root_.GD.N0155.d006241; ring
  have e0 : _root_.GD.N0155.d006241 θ 0 = 1 := by unfold _root_.GD.N0155.d006241; ring
  rw [e1, e0, Real.log_one]
  first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf

theorem d006249 {θ : ℝ} (hθ : 0 < θ) (c : ℝ) (n : ℕ) :
    IntervalIntegrable (fun u => c * (1 / _root_.GD.N0155.d006241 θ u ^ n)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.div continuousOn_const ((_root_.GD.N0155.d006242 θ).pow n).continuousOn
  intro x hx
  obtain ⟨hx0, hx1⟩ := _root_.GD.N0155.d006245 hx
  exact pow_ne_zero _ (ne_of_gt (_root_.GD.N0155.d006243 hθ hx0 hx1))

theorem d006250 {θ : ℝ} (hθ : 0 < θ) (c : ℝ) :
    IntervalIntegrable (fun u => c * (1 / _root_.GD.N0155.d006241 θ u)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.div continuousOn_const (_root_.GD.N0155.d006242 θ).continuousOn
  intro x hx
  obtain ⟨hx0, hx1⟩ := _root_.GD.N0155.d006245 hx
  exact ne_of_gt (_root_.GD.N0155.d006243 hθ hx0 hx1)

theorem d006251 {θ : ℝ} (c : ℝ) (k : ℕ) :
    IntervalIntegrable (fun u => c * _root_.GD.N0155.d006241 θ u ^ k) volume 0 1 :=
  (continuous_const.mul ((_root_.GD.N0155.d006242 θ).pow k)).intervalIntegrable 0 1

theorem d006252 (c : ℝ) (j : ℕ) :
    IntervalIntegrable (fun u : ℝ => c * u ^ j) volume 0 1 :=
  (continuous_const.mul (continuous_pow j)).intervalIntegrable 0 1


noncomputable def d006253 (θ u : ℝ) : ℝ :=
  u^6 * (1-u)^6 * ((1+θ)*u - 1)^2
    * (125*(1+θ)^2 - 280*(1+θ)*_root_.GD.N0155.d006241 θ u + 294*_root_.GD.N0155.d006241 θ u ^ 2) / _root_.GD.N0155.d006241 θ u ^ 8


noncomputable def d006254 (θ u : ℝ) : ℝ :=
  u^5 * (1-u)^5 * (2*u - 1) * ((1+θ)*u - 1)
    * (5/3*(1+θ) - 7/2*_root_.GD.N0155.d006241 θ u) / _root_.GD.N0155.d006241 θ u ^ 5


noncomputable def d006255 (θ : ℝ) : ℝ := 630 * θ^2 / 96 * ∫ u in (0:ℝ)..1, _root_.GD.N0155.d006253 θ u


noncomputable def d006256 (θ : ℝ) : ℝ :=
  θ / (1+θ) * 630 * (θ/2) * ∫ u in (0:ℝ)..1, _root_.GD.N0155.d006254 θ u

theorem d006257 {θ : ℝ} (ht1 : θ ≠ 1) {u : ℝ} (hd : _root_.GD.N0155.d006241 θ u ≠ 0) :
    _root_.GD.N0155.d006253 θ u =
      (((500 : ℝ) * θ^12 - (1000 : ℝ) * θ^10 + (500 : ℝ) * θ^8) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 8) + (((-3500 : ℝ) * θ^12 - (4620 : ℝ) * θ^11 + (8120 : ℝ) * θ^10 + (8120 : ℝ) * θ^9 - (4620 : ℝ) * θ^8 - (3500 : ℝ) * θ^7) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 7) + (((10625 : ℝ) * θ^12 + (32090 : ℝ) * θ^11 - (9449 : ℝ) * θ^10 - (66532 : ℝ) * θ^9 - (9449 : ℝ) * θ^8 + (32090 : ℝ) * θ^7 + (10625 : ℝ) * θ^6) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 6) + (((-18250 : ℝ) * θ^12 - (96550 : ℝ) * θ^11 - (75002 : ℝ) * θ^10 + (189802 : ℝ) * θ^9 + (189802 : ℝ) * θ^8 - (75002 : ℝ) * θ^7 - (96550 : ℝ) * θ^6 - (18250 : ℝ) * θ^5) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 5) + (((19375 : ℝ) * θ^12 + (164130 : ℝ) * θ^11 + (323570 : ℝ) * θ^10 - (157074 : ℝ) * θ^9 - (700002 : ℝ) * θ^8 - (157074 : ℝ) * θ^7 + (323570 : ℝ) * θ^6 + (164130 : ℝ) * θ^5 + (19375 : ℝ) * θ^4) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 4) + (((-13000 : ℝ) * θ^12 - (172150 : ℝ) * θ^11 - (608354 : ℝ) * θ^10 - (349190 : ℝ) * θ^9 + (1142694 : ℝ) * θ^8 + (1142694 : ℝ) * θ^7 - (349190 : ℝ) * θ^6 - (608354 : ℝ) * θ^5 - (172150 : ℝ) * θ^4 - (13000 : ℝ) * θ^3) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 3) + (((5375 : ℝ) * θ^12 + (113870 : ℝ) * θ^11 + (661600 : ℝ) * θ^10 + (1101574 : ℝ) * θ^9 - (649335 : ℝ) * θ^8 - (2466168 : ℝ) * θ^7 - (649335 : ℝ) * θ^6 + (1101574 : ℝ) * θ^5 + (661600 : ℝ) * θ^4 + (113870 : ℝ) * θ^3 + (5375 : ℝ) * θ^2) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 2) + (((-1250 : ℝ) * θ^12 - (46290 : ℝ) * θ^11 - (442126 : ℝ) * θ^10 - (1380738 : ℝ) * θ^9 - (695916 : ℝ) * θ^8 + (2566320 : ℝ) * θ^7 + (2566320 : ℝ) * θ^6 - (695916 : ℝ) * θ^5 - (1380738 : ℝ) * θ^4 - (442126 : ℝ) * θ^3 - (46290 : ℝ) * θ^2 - (1250 : ℝ) * θ) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u) + (((125 : ℝ) * θ^12 + (10550 : ℝ) * θ^11 + (179062 : ℝ) * θ^10 + (973978 : ℝ) * θ^9 + (1571793 : ℝ) * θ^8 - (961008 : ℝ) * θ^7 - (3549000 : ℝ) * θ^6 - (961008 : ℝ) * θ^5 + (1571793 : ℝ) * θ^4 + (973978 : ℝ) * θ^3 + (179062 : ℝ) * θ^2 + (10550 : ℝ) * θ + (125 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 0 + (((-1030 : ℝ) * θ^11 - (40270 : ℝ) * θ^10 - (401546 : ℝ) * θ^9 - (1292678 : ℝ) * θ^8 - (677916 : ℝ) * θ^7 + (2413440 : ℝ) * θ^6 + (2413440 : ℝ) * θ^5 - (677916 : ℝ) * θ^4 - (1292678 : ℝ) * θ^3 - (401546 : ℝ) * θ^2 - (40270 : ℝ) * θ - (1030 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 1 + (((3849 : ℝ) * θ^10 + (90070 : ℝ) * θ^9 + (563376 : ℝ) * θ^8 + (989966 : ℝ) * θ^7 - (549585 : ℝ) * θ^6 - (2195352 : ℝ) * θ^5 - (549585 : ℝ) * θ^4 + (989966 : ℝ) * θ^3 + (563376 : ℝ) * θ^2 + (90070 : ℝ) * θ + (3849 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 2 + (((-8464 : ℝ) * θ^9 - (128050 : ℝ) * θ^8 - (497222 : ℝ) * θ^7 - (317690 : ℝ) * θ^6 + (951426 : ℝ) * θ^5 + (951426 : ℝ) * θ^4 - (317690 : ℝ) * θ^3 - (497222 : ℝ) * θ^2 - (128050 : ℝ) * θ - (8464 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 3 + (((11885 : ℝ) * θ^8 + (117650 : ℝ) * θ^7 + (259030 : ℝ) * θ^6 - (110594 : ℝ) * θ^5 - (555942 : ℝ) * θ^4 - (110594 : ℝ) * θ^3 + (259030 : ℝ) * θ^2 + (117650 : ℝ) * θ + (11885 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 4 + (((-10830 : ℝ) * θ^7 - (67850 : ℝ) * θ^6 - (61422 : ℝ) * θ^5 + (140102 : ℝ) * θ^4 + (140102 : ℝ) * θ^3 - (61422 : ℝ) * θ^2 - (67850 : ℝ) * θ - (10830 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 5 + (((6215 : ℝ) * θ^6 + (22370 : ℝ) * θ^5 - (5039 : ℝ) * θ^4 - (47092 : ℝ) * θ^3 - (5039 : ℝ) * θ^2 + (22370 : ℝ) * θ + (6215 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 6 + (((-2044 : ℝ) * θ^5 - (3220 : ℝ) * θ^4 + (5264 : ℝ) * θ^3 + (5264 : ℝ) * θ^2 - (3220 : ℝ) * θ - (2044 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 7 + (((294 : ℝ) * θ^4 - (588 : ℝ) * θ^2 + (294 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 8 := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr ht1
  unfold _root_.GD.N0155.d006241 at hd
  unfold _root_.GD.N0155.d006253 _root_.GD.N0155.d006241
  have hkey : (u^6 * (1-u)^6 * ((1+θ)*u - 1)^2 * (125*(1+θ)^2 - 280*(1+θ)*(1 - u + θ * u) + 294*(1 - u + θ * u) ^ 2)) * (θ - 1) ^ 16 =
      ((500 : ℝ) * θ^12 - (1000 : ℝ) * θ^10 + (500 : ℝ) * θ^8) * (1 - u + θ * u) ^ 0 + ((-3500 : ℝ) * θ^12 - (4620 : ℝ) * θ^11 + (8120 : ℝ) * θ^10 + (8120 : ℝ) * θ^9 - (4620 : ℝ) * θ^8 - (3500 : ℝ) * θ^7) * (1 - u + θ * u) ^ 1 + ((10625 : ℝ) * θ^12 + (32090 : ℝ) * θ^11 - (9449 : ℝ) * θ^10 - (66532 : ℝ) * θ^9 - (9449 : ℝ) * θ^8 + (32090 : ℝ) * θ^7 + (10625 : ℝ) * θ^6) * (1 - u + θ * u) ^ 2 + ((-18250 : ℝ) * θ^12 - (96550 : ℝ) * θ^11 - (75002 : ℝ) * θ^10 + (189802 : ℝ) * θ^9 + (189802 : ℝ) * θ^8 - (75002 : ℝ) * θ^7 - (96550 : ℝ) * θ^6 - (18250 : ℝ) * θ^5) * (1 - u + θ * u) ^ 3 + ((19375 : ℝ) * θ^12 + (164130 : ℝ) * θ^11 + (323570 : ℝ) * θ^10 - (157074 : ℝ) * θ^9 - (700002 : ℝ) * θ^8 - (157074 : ℝ) * θ^7 + (323570 : ℝ) * θ^6 + (164130 : ℝ) * θ^5 + (19375 : ℝ) * θ^4) * (1 - u + θ * u) ^ 4 + ((-13000 : ℝ) * θ^12 - (172150 : ℝ) * θ^11 - (608354 : ℝ) * θ^10 - (349190 : ℝ) * θ^9 + (1142694 : ℝ) * θ^8 + (1142694 : ℝ) * θ^7 - (349190 : ℝ) * θ^6 - (608354 : ℝ) * θ^5 - (172150 : ℝ) * θ^4 - (13000 : ℝ) * θ^3) * (1 - u + θ * u) ^ 5 + ((5375 : ℝ) * θ^12 + (113870 : ℝ) * θ^11 + (661600 : ℝ) * θ^10 + (1101574 : ℝ) * θ^9 - (649335 : ℝ) * θ^8 - (2466168 : ℝ) * θ^7 - (649335 : ℝ) * θ^6 + (1101574 : ℝ) * θ^5 + (661600 : ℝ) * θ^4 + (113870 : ℝ) * θ^3 + (5375 : ℝ) * θ^2) * (1 - u + θ * u) ^ 6 + ((-1250 : ℝ) * θ^12 - (46290 : ℝ) * θ^11 - (442126 : ℝ) * θ^10 - (1380738 : ℝ) * θ^9 - (695916 : ℝ) * θ^8 + (2566320 : ℝ) * θ^7 + (2566320 : ℝ) * θ^6 - (695916 : ℝ) * θ^5 - (1380738 : ℝ) * θ^4 - (442126 : ℝ) * θ^3 - (46290 : ℝ) * θ^2 - (1250 : ℝ) * θ) * (1 - u + θ * u) ^ 7 + ((125 : ℝ) * θ^12 + (10550 : ℝ) * θ^11 + (179062 : ℝ) * θ^10 + (973978 : ℝ) * θ^9 + (1571793 : ℝ) * θ^8 - (961008 : ℝ) * θ^7 - (3549000 : ℝ) * θ^6 - (961008 : ℝ) * θ^5 + (1571793 : ℝ) * θ^4 + (973978 : ℝ) * θ^3 + (179062 : ℝ) * θ^2 + (10550 : ℝ) * θ + (125 : ℝ)) * (1 - u + θ * u) ^ 8 + ((-1030 : ℝ) * θ^11 - (40270 : ℝ) * θ^10 - (401546 : ℝ) * θ^9 - (1292678 : ℝ) * θ^8 - (677916 : ℝ) * θ^7 + (2413440 : ℝ) * θ^6 + (2413440 : ℝ) * θ^5 - (677916 : ℝ) * θ^4 - (1292678 : ℝ) * θ^3 - (401546 : ℝ) * θ^2 - (40270 : ℝ) * θ - (1030 : ℝ)) * (1 - u + θ * u) ^ 9 + ((3849 : ℝ) * θ^10 + (90070 : ℝ) * θ^9 + (563376 : ℝ) * θ^8 + (989966 : ℝ) * θ^7 - (549585 : ℝ) * θ^6 - (2195352 : ℝ) * θ^5 - (549585 : ℝ) * θ^4 + (989966 : ℝ) * θ^3 + (563376 : ℝ) * θ^2 + (90070 : ℝ) * θ + (3849 : ℝ)) * (1 - u + θ * u) ^ 10 + ((-8464 : ℝ) * θ^9 - (128050 : ℝ) * θ^8 - (497222 : ℝ) * θ^7 - (317690 : ℝ) * θ^6 + (951426 : ℝ) * θ^5 + (951426 : ℝ) * θ^4 - (317690 : ℝ) * θ^3 - (497222 : ℝ) * θ^2 - (128050 : ℝ) * θ - (8464 : ℝ)) * (1 - u + θ * u) ^ 11 + ((11885 : ℝ) * θ^8 + (117650 : ℝ) * θ^7 + (259030 : ℝ) * θ^6 - (110594 : ℝ) * θ^5 - (555942 : ℝ) * θ^4 - (110594 : ℝ) * θ^3 + (259030 : ℝ) * θ^2 + (117650 : ℝ) * θ + (11885 : ℝ)) * (1 - u + θ * u) ^ 12 + ((-10830 : ℝ) * θ^7 - (67850 : ℝ) * θ^6 - (61422 : ℝ) * θ^5 + (140102 : ℝ) * θ^4 + (140102 : ℝ) * θ^3 - (61422 : ℝ) * θ^2 - (67850 : ℝ) * θ - (10830 : ℝ)) * (1 - u + θ * u) ^ 13 + ((6215 : ℝ) * θ^6 + (22370 : ℝ) * θ^5 - (5039 : ℝ) * θ^4 - (47092 : ℝ) * θ^3 - (5039 : ℝ) * θ^2 + (22370 : ℝ) * θ + (6215 : ℝ)) * (1 - u + θ * u) ^ 14 + ((-2044 : ℝ) * θ^5 - (3220 : ℝ) * θ^4 + (5264 : ℝ) * θ^3 + (5264 : ℝ) * θ^2 - (3220 : ℝ) * θ - (2044 : ℝ)) * (1 - u + θ * u) ^ 15 + ((294 : ℝ) * θ^4 - (588 : ℝ) * θ^2 + (294 : ℝ)) * (1 - u + θ * u) ^ 16 := by ring
  have hA0 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 / (1 - u + θ * u) ^ 8) * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 0 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA1 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 / (1 - u + θ * u) ^ 7) * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 1 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA2 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 / (1 - u + θ * u) ^ 6) * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 2 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA3 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 / (1 - u + θ * u) ^ 5) * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 3 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA4 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 / (1 - u + θ * u) ^ 4) * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 4 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA5 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 / (1 - u + θ * u) ^ 3) * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 5 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA6 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 / (1 - u + θ * u) ^ 2) * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 6 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA7 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 / (1 - u + θ * u)) * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 7 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA8 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 - u + θ * u) ^ 0 * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 8 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA9 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 - u + θ * u) ^ 1 * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 9 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA10 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 - u + θ * u) ^ 2 * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 10 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA11 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 - u + θ * u) ^ 3 * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 11 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA12 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 - u + θ * u) ^ 4 * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 12 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA13 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 - u + θ * u) ^ 5 * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 13 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA14 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 - u + θ * u) ^ 6 * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 14 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA15 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 - u + θ * u) ^ 7 * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 15 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hA16 : ∀ p : ℝ, p / (θ - 1) ^ 16 * (1 - u + θ * u) ^ 8 * (1 - u + θ * u) ^ 8 * (θ - 1) ^ 16 = p * (1 - u + θ * u) ^ 16 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  first
    | (rw [div_eq_iff (pow_ne_zero 8 hd)]; refine mul_right_cancel₀ (pow_ne_zero 16 h1) ?_; linear_combination hkey - hA0 ((500 : ℝ) * θ^12 - (1000 : ℝ) * θ^10 + (500 : ℝ) * θ^8) - hA1 ((-3500 : ℝ) * θ^12 - (4620 : ℝ) * θ^11 + (8120 : ℝ) * θ^10 + (8120 : ℝ) * θ^9 - (4620 : ℝ) * θ^8 - (3500 : ℝ) * θ^7) - hA2 ((10625 : ℝ) * θ^12 + (32090 : ℝ) * θ^11 - (9449 : ℝ) * θ^10 - (66532 : ℝ) * θ^9 - (9449 : ℝ) * θ^8 + (32090 : ℝ) * θ^7 + (10625 : ℝ) * θ^6) - hA3 ((-18250 : ℝ) * θ^12 - (96550 : ℝ) * θ^11 - (75002 : ℝ) * θ^10 + (189802 : ℝ) * θ^9 + (189802 : ℝ) * θ^8 - (75002 : ℝ) * θ^7 - (96550 : ℝ) * θ^6 - (18250 : ℝ) * θ^5) - hA4 ((19375 : ℝ) * θ^12 + (164130 : ℝ) * θ^11 + (323570 : ℝ) * θ^10 - (157074 : ℝ) * θ^9 - (700002 : ℝ) * θ^8 - (157074 : ℝ) * θ^7 + (323570 : ℝ) * θ^6 + (164130 : ℝ) * θ^5 + (19375 : ℝ) * θ^4) - hA5 ((-13000 : ℝ) * θ^12 - (172150 : ℝ) * θ^11 - (608354 : ℝ) * θ^10 - (349190 : ℝ) * θ^9 + (1142694 : ℝ) * θ^8 + (1142694 : ℝ) * θ^7 - (349190 : ℝ) * θ^6 - (608354 : ℝ) * θ^5 - (172150 : ℝ) * θ^4 - (13000 : ℝ) * θ^3) - hA6 ((5375 : ℝ) * θ^12 + (113870 : ℝ) * θ^11 + (661600 : ℝ) * θ^10 + (1101574 : ℝ) * θ^9 - (649335 : ℝ) * θ^8 - (2466168 : ℝ) * θ^7 - (649335 : ℝ) * θ^6 + (1101574 : ℝ) * θ^5 + (661600 : ℝ) * θ^4 + (113870 : ℝ) * θ^3 + (5375 : ℝ) * θ^2) - hA7 ((-1250 : ℝ) * θ^12 - (46290 : ℝ) * θ^11 - (442126 : ℝ) * θ^10 - (1380738 : ℝ) * θ^9 - (695916 : ℝ) * θ^8 + (2566320 : ℝ) * θ^7 + (2566320 : ℝ) * θ^6 - (695916 : ℝ) * θ^5 - (1380738 : ℝ) * θ^4 - (442126 : ℝ) * θ^3 - (46290 : ℝ) * θ^2 - (1250 : ℝ) * θ) - hA8 ((125 : ℝ) * θ^12 + (10550 : ℝ) * θ^11 + (179062 : ℝ) * θ^10 + (973978 : ℝ) * θ^9 + (1571793 : ℝ) * θ^8 - (961008 : ℝ) * θ^7 - (3549000 : ℝ) * θ^6 - (961008 : ℝ) * θ^5 + (1571793 : ℝ) * θ^4 + (973978 : ℝ) * θ^3 + (179062 : ℝ) * θ^2 + (10550 : ℝ) * θ + (125 : ℝ)) - hA9 ((-1030 : ℝ) * θ^11 - (40270 : ℝ) * θ^10 - (401546 : ℝ) * θ^9 - (1292678 : ℝ) * θ^8 - (677916 : ℝ) * θ^7 + (2413440 : ℝ) * θ^6 + (2413440 : ℝ) * θ^5 - (677916 : ℝ) * θ^4 - (1292678 : ℝ) * θ^3 - (401546 : ℝ) * θ^2 - (40270 : ℝ) * θ - (1030 : ℝ)) - hA10 ((3849 : ℝ) * θ^10 + (90070 : ℝ) * θ^9 + (563376 : ℝ) * θ^8 + (989966 : ℝ) * θ^7 - (549585 : ℝ) * θ^6 - (2195352 : ℝ) * θ^5 - (549585 : ℝ) * θ^4 + (989966 : ℝ) * θ^3 + (563376 : ℝ) * θ^2 + (90070 : ℝ) * θ + (3849 : ℝ)) - hA11 ((-8464 : ℝ) * θ^9 - (128050 : ℝ) * θ^8 - (497222 : ℝ) * θ^7 - (317690 : ℝ) * θ^6 + (951426 : ℝ) * θ^5 + (951426 : ℝ) * θ^4 - (317690 : ℝ) * θ^3 - (497222 : ℝ) * θ^2 - (128050 : ℝ) * θ - (8464 : ℝ)) - hA12 ((11885 : ℝ) * θ^8 + (117650 : ℝ) * θ^7 + (259030 : ℝ) * θ^6 - (110594 : ℝ) * θ^5 - (555942 : ℝ) * θ^4 - (110594 : ℝ) * θ^3 + (259030 : ℝ) * θ^2 + (117650 : ℝ) * θ + (11885 : ℝ)) - hA13 ((-10830 : ℝ) * θ^7 - (67850 : ℝ) * θ^6 - (61422 : ℝ) * θ^5 + (140102 : ℝ) * θ^4 + (140102 : ℝ) * θ^3 - (61422 : ℝ) * θ^2 - (67850 : ℝ) * θ - (10830 : ℝ)) - hA14 ((6215 : ℝ) * θ^6 + (22370 : ℝ) * θ^5 - (5039 : ℝ) * θ^4 - (47092 : ℝ) * θ^3 - (5039 : ℝ) * θ^2 + (22370 : ℝ) * θ + (6215 : ℝ)) - hA15 ((-2044 : ℝ) * θ^5 - (3220 : ℝ) * θ^4 + (5264 : ℝ) * θ^3 + (5264 : ℝ) * θ^2 - (3220 : ℝ) * θ - (2044 : ℝ)) - hA16 ((294 : ℝ) * θ^4 - (588 : ℝ) * θ^2 + (294 : ℝ)))
    | (rw [div_eq_iff₀ (pow_ne_zero 8 hd)]; refine mul_right_cancel₀ (pow_ne_zero 16 h1) ?_; linear_combination hkey - hA0 ((500 : ℝ) * θ^12 - (1000 : ℝ) * θ^10 + (500 : ℝ) * θ^8) - hA1 ((-3500 : ℝ) * θ^12 - (4620 : ℝ) * θ^11 + (8120 : ℝ) * θ^10 + (8120 : ℝ) * θ^9 - (4620 : ℝ) * θ^8 - (3500 : ℝ) * θ^7) - hA2 ((10625 : ℝ) * θ^12 + (32090 : ℝ) * θ^11 - (9449 : ℝ) * θ^10 - (66532 : ℝ) * θ^9 - (9449 : ℝ) * θ^8 + (32090 : ℝ) * θ^7 + (10625 : ℝ) * θ^6) - hA3 ((-18250 : ℝ) * θ^12 - (96550 : ℝ) * θ^11 - (75002 : ℝ) * θ^10 + (189802 : ℝ) * θ^9 + (189802 : ℝ) * θ^8 - (75002 : ℝ) * θ^7 - (96550 : ℝ) * θ^6 - (18250 : ℝ) * θ^5) - hA4 ((19375 : ℝ) * θ^12 + (164130 : ℝ) * θ^11 + (323570 : ℝ) * θ^10 - (157074 : ℝ) * θ^9 - (700002 : ℝ) * θ^8 - (157074 : ℝ) * θ^7 + (323570 : ℝ) * θ^6 + (164130 : ℝ) * θ^5 + (19375 : ℝ) * θ^4) - hA5 ((-13000 : ℝ) * θ^12 - (172150 : ℝ) * θ^11 - (608354 : ℝ) * θ^10 - (349190 : ℝ) * θ^9 + (1142694 : ℝ) * θ^8 + (1142694 : ℝ) * θ^7 - (349190 : ℝ) * θ^6 - (608354 : ℝ) * θ^5 - (172150 : ℝ) * θ^4 - (13000 : ℝ) * θ^3) - hA6 ((5375 : ℝ) * θ^12 + (113870 : ℝ) * θ^11 + (661600 : ℝ) * θ^10 + (1101574 : ℝ) * θ^9 - (649335 : ℝ) * θ^8 - (2466168 : ℝ) * θ^7 - (649335 : ℝ) * θ^6 + (1101574 : ℝ) * θ^5 + (661600 : ℝ) * θ^4 + (113870 : ℝ) * θ^3 + (5375 : ℝ) * θ^2) - hA7 ((-1250 : ℝ) * θ^12 - (46290 : ℝ) * θ^11 - (442126 : ℝ) * θ^10 - (1380738 : ℝ) * θ^9 - (695916 : ℝ) * θ^8 + (2566320 : ℝ) * θ^7 + (2566320 : ℝ) * θ^6 - (695916 : ℝ) * θ^5 - (1380738 : ℝ) * θ^4 - (442126 : ℝ) * θ^3 - (46290 : ℝ) * θ^2 - (1250 : ℝ) * θ) - hA8 ((125 : ℝ) * θ^12 + (10550 : ℝ) * θ^11 + (179062 : ℝ) * θ^10 + (973978 : ℝ) * θ^9 + (1571793 : ℝ) * θ^8 - (961008 : ℝ) * θ^7 - (3549000 : ℝ) * θ^6 - (961008 : ℝ) * θ^5 + (1571793 : ℝ) * θ^4 + (973978 : ℝ) * θ^3 + (179062 : ℝ) * θ^2 + (10550 : ℝ) * θ + (125 : ℝ)) - hA9 ((-1030 : ℝ) * θ^11 - (40270 : ℝ) * θ^10 - (401546 : ℝ) * θ^9 - (1292678 : ℝ) * θ^8 - (677916 : ℝ) * θ^7 + (2413440 : ℝ) * θ^6 + (2413440 : ℝ) * θ^5 - (677916 : ℝ) * θ^4 - (1292678 : ℝ) * θ^3 - (401546 : ℝ) * θ^2 - (40270 : ℝ) * θ - (1030 : ℝ)) - hA10 ((3849 : ℝ) * θ^10 + (90070 : ℝ) * θ^9 + (563376 : ℝ) * θ^8 + (989966 : ℝ) * θ^7 - (549585 : ℝ) * θ^6 - (2195352 : ℝ) * θ^5 - (549585 : ℝ) * θ^4 + (989966 : ℝ) * θ^3 + (563376 : ℝ) * θ^2 + (90070 : ℝ) * θ + (3849 : ℝ)) - hA11 ((-8464 : ℝ) * θ^9 - (128050 : ℝ) * θ^8 - (497222 : ℝ) * θ^7 - (317690 : ℝ) * θ^6 + (951426 : ℝ) * θ^5 + (951426 : ℝ) * θ^4 - (317690 : ℝ) * θ^3 - (497222 : ℝ) * θ^2 - (128050 : ℝ) * θ - (8464 : ℝ)) - hA12 ((11885 : ℝ) * θ^8 + (117650 : ℝ) * θ^7 + (259030 : ℝ) * θ^6 - (110594 : ℝ) * θ^5 - (555942 : ℝ) * θ^4 - (110594 : ℝ) * θ^3 + (259030 : ℝ) * θ^2 + (117650 : ℝ) * θ + (11885 : ℝ)) - hA13 ((-10830 : ℝ) * θ^7 - (67850 : ℝ) * θ^6 - (61422 : ℝ) * θ^5 + (140102 : ℝ) * θ^4 + (140102 : ℝ) * θ^3 - (61422 : ℝ) * θ^2 - (67850 : ℝ) * θ - (10830 : ℝ)) - hA14 ((6215 : ℝ) * θ^6 + (22370 : ℝ) * θ^5 - (5039 : ℝ) * θ^4 - (47092 : ℝ) * θ^3 - (5039 : ℝ) * θ^2 + (22370 : ℝ) * θ + (6215 : ℝ)) - hA15 ((-2044 : ℝ) * θ^5 - (3220 : ℝ) * θ^4 + (5264 : ℝ) * θ^3 + (5264 : ℝ) * θ^2 - (3220 : ℝ) * θ - (2044 : ℝ)) - hA16 ((294 : ℝ) * θ^4 - (588 : ℝ) * θ^2 + (294 : ℝ)))
    | (first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf)

theorem d006258 {θ : ℝ} (ht1 : θ ≠ 1) {u : ℝ} (hd : _root_.GD.N0155.d006241 θ u ≠ 0) :
    _root_.GD.N0155.d006254 θ u =
      ((((-10 : ℝ)/3) * θ^9 + ((-10 : ℝ)/3) * θ^8 + ((10 : ℝ)/3) * θ^7 + ((10 : ℝ)/3) * θ^6) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u ^ 5) + ((((55 : ℝ)/3) * θ^9 + ((151 : ℝ)/3) * θ^8 + ((-151 : ℝ)/3) * θ^6 + ((-55 : ℝ)/3) * θ^5) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u ^ 4) + ((((-125 : ℝ)/3) * θ^9 + ((-1301 : ℝ)/6) * θ^8 + ((-1135 : ℝ)/6) * θ^7 + ((1135 : ℝ)/6) * θ^6 + ((1301 : ℝ)/6) * θ^5 + ((125 : ℝ)/3) * θ^4) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u ^ 3) + (((50 : ℝ) * θ^9 + ((2675 : ℝ)/6) * θ^8 + (887 : ℝ) * θ^7 - (887 : ℝ) * θ^5 + ((-2675 : ℝ)/6) * θ^4 - (50 : ℝ) * θ^3) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u ^ 2) + ((((-100 : ℝ)/3) * θ^9 - (505 : ℝ) * θ^8 + ((-10985 : ℝ)/6) * θ^7 + ((-8575 : ℝ)/6) * θ^6 + ((8575 : ℝ)/6) * θ^5 + ((10985 : ℝ)/6) * θ^4 + (505 : ℝ) * θ^3 + ((100 : ℝ)/3) * θ^2) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u) + ((((35 : ℝ)/3) * θ^9 + ((970 : ℝ)/3) * θ^8 + (2050 : ℝ) * θ^7 + ((10885 : ℝ)/3) * θ^6 + ((-10885 : ℝ)/3) * θ^4 - (2050 : ℝ) * θ^3 + ((-970 : ℝ)/3) * θ^2 + ((-35 : ℝ)/3) * θ) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 0 + ((((-5 : ℝ)/3) * θ^9 + ((-219 : ℝ)/2) * θ^8 + ((-7745 : ℝ)/6) * θ^7 + ((-25823 : ℝ)/6) * θ^6 + ((-19565 : ℝ)/6) * θ^5 + ((19565 : ℝ)/6) * θ^4 + ((25823 : ℝ)/6) * θ^3 + ((7745 : ℝ)/6) * θ^2 + ((219 : ℝ)/2) * θ + ((5 : ℝ)/3)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 1 + ((((91 : ℝ)/6) * θ^8 + ((1285 : ℝ)/3) * θ^7 + (2750 : ℝ) * θ^6 + ((14707 : ℝ)/3) * θ^5 + ((-14707 : ℝ)/3) * θ^3 - (2750 : ℝ) * θ^2 + ((-1285 : ℝ)/3) * θ + ((-91 : ℝ)/6)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 2 + ((((-347 : ℝ)/6) * θ^7 + ((-1815 : ℝ)/2) * θ^6 + ((-20183 : ℝ)/6) * θ^5 + ((-15925 : ℝ)/6) * θ^4 + ((15925 : ℝ)/6) * θ^3 + ((20183 : ℝ)/6) * θ^2 + ((1815 : ℝ)/2) * θ + ((347 : ℝ)/6)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 3 + (((120 : ℝ) * θ^6 + ((3385 : ℝ)/3) * θ^5 + (2315 : ℝ) * θ^4 - (2315 : ℝ) * θ^2 + ((-3385 : ℝ)/3) * θ - (120 : ℝ)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 4 + ((((-440 : ℝ)/3) * θ^5 + ((-4955 : ℝ)/6) * θ^4 + ((-4495 : ℝ)/6) * θ^3 + ((4495 : ℝ)/6) * θ^2 + ((4955 : ℝ)/6) * θ + ((440 : ℝ)/3)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 5 + ((((635 : ℝ)/6) * θ^4 + ((991 : ℝ)/3) * θ^3 + ((-991 : ℝ)/3) * θ + ((-635 : ℝ)/6)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 6 + ((((-251 : ℝ)/6) * θ^3 + ((-335 : ℝ)/6) * θ^2 + ((335 : ℝ)/6) * θ + ((251 : ℝ)/6)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 7 + (((7 : ℝ) * θ^2 - (7 : ℝ)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 8 := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr ht1
  unfold _root_.GD.N0155.d006241 at hd
  unfold _root_.GD.N0155.d006254 _root_.GD.N0155.d006241
  have hkey : (u^5 * (1-u)^5 * (2*u - 1) * ((1+θ)*u - 1) * (5/3*(1+θ) - 7/2*(1 - u + θ * u))) * (θ - 1) ^ 13 =
      (((-10 : ℝ)/3) * θ^9 + ((-10 : ℝ)/3) * θ^8 + ((10 : ℝ)/3) * θ^7 + ((10 : ℝ)/3) * θ^6) * (1 - u + θ * u) ^ 0 + (((55 : ℝ)/3) * θ^9 + ((151 : ℝ)/3) * θ^8 + ((-151 : ℝ)/3) * θ^6 + ((-55 : ℝ)/3) * θ^5) * (1 - u + θ * u) ^ 1 + (((-125 : ℝ)/3) * θ^9 + ((-1301 : ℝ)/6) * θ^8 + ((-1135 : ℝ)/6) * θ^7 + ((1135 : ℝ)/6) * θ^6 + ((1301 : ℝ)/6) * θ^5 + ((125 : ℝ)/3) * θ^4) * (1 - u + θ * u) ^ 2 + ((50 : ℝ) * θ^9 + ((2675 : ℝ)/6) * θ^8 + (887 : ℝ) * θ^7 - (887 : ℝ) * θ^5 + ((-2675 : ℝ)/6) * θ^4 - (50 : ℝ) * θ^3) * (1 - u + θ * u) ^ 3 + (((-100 : ℝ)/3) * θ^9 - (505 : ℝ) * θ^8 + ((-10985 : ℝ)/6) * θ^7 + ((-8575 : ℝ)/6) * θ^6 + ((8575 : ℝ)/6) * θ^5 + ((10985 : ℝ)/6) * θ^4 + (505 : ℝ) * θ^3 + ((100 : ℝ)/3) * θ^2) * (1 - u + θ * u) ^ 4 + (((35 : ℝ)/3) * θ^9 + ((970 : ℝ)/3) * θ^8 + (2050 : ℝ) * θ^7 + ((10885 : ℝ)/3) * θ^6 + ((-10885 : ℝ)/3) * θ^4 - (2050 : ℝ) * θ^3 + ((-970 : ℝ)/3) * θ^2 + ((-35 : ℝ)/3) * θ) * (1 - u + θ * u) ^ 5 + (((-5 : ℝ)/3) * θ^9 + ((-219 : ℝ)/2) * θ^8 + ((-7745 : ℝ)/6) * θ^7 + ((-25823 : ℝ)/6) * θ^6 + ((-19565 : ℝ)/6) * θ^5 + ((19565 : ℝ)/6) * θ^4 + ((25823 : ℝ)/6) * θ^3 + ((7745 : ℝ)/6) * θ^2 + ((219 : ℝ)/2) * θ + ((5 : ℝ)/3)) * (1 - u + θ * u) ^ 6 + (((91 : ℝ)/6) * θ^8 + ((1285 : ℝ)/3) * θ^7 + (2750 : ℝ) * θ^6 + ((14707 : ℝ)/3) * θ^5 + ((-14707 : ℝ)/3) * θ^3 - (2750 : ℝ) * θ^2 + ((-1285 : ℝ)/3) * θ + ((-91 : ℝ)/6)) * (1 - u + θ * u) ^ 7 + (((-347 : ℝ)/6) * θ^7 + ((-1815 : ℝ)/2) * θ^6 + ((-20183 : ℝ)/6) * θ^5 + ((-15925 : ℝ)/6) * θ^4 + ((15925 : ℝ)/6) * θ^3 + ((20183 : ℝ)/6) * θ^2 + ((1815 : ℝ)/2) * θ + ((347 : ℝ)/6)) * (1 - u + θ * u) ^ 8 + ((120 : ℝ) * θ^6 + ((3385 : ℝ)/3) * θ^5 + (2315 : ℝ) * θ^4 - (2315 : ℝ) * θ^2 + ((-3385 : ℝ)/3) * θ - (120 : ℝ)) * (1 - u + θ * u) ^ 9 + (((-440 : ℝ)/3) * θ^5 + ((-4955 : ℝ)/6) * θ^4 + ((-4495 : ℝ)/6) * θ^3 + ((4495 : ℝ)/6) * θ^2 + ((4955 : ℝ)/6) * θ + ((440 : ℝ)/3)) * (1 - u + θ * u) ^ 10 + (((635 : ℝ)/6) * θ^4 + ((991 : ℝ)/3) * θ^3 + ((-991 : ℝ)/3) * θ + ((-635 : ℝ)/6)) * (1 - u + θ * u) ^ 11 + (((-251 : ℝ)/6) * θ^3 + ((-335 : ℝ)/6) * θ^2 + ((335 : ℝ)/6) * θ + ((251 : ℝ)/6)) * (1 - u + θ * u) ^ 12 + ((7 : ℝ) * θ^2 - (7 : ℝ)) * (1 - u + θ * u) ^ 13 := by ring
  have hC0 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 / (1 - u + θ * u) ^ 5) * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 0 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hC1 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 / (1 - u + θ * u) ^ 4) * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 1 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hC2 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 / (1 - u + θ * u) ^ 3) * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 2 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hC3 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 / (1 - u + θ * u) ^ 2) * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 3 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hC4 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 / (1 - u + θ * u)) * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 4 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hC5 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 - u + θ * u) ^ 0 * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 5 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hC6 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 - u + θ * u) ^ 1 * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 6 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hC7 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 - u + θ * u) ^ 2 * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 7 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hC8 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 - u + θ * u) ^ 3 * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 8 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hC9 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 - u + θ * u) ^ 4 * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 9 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hC10 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 - u + θ * u) ^ 5 * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 10 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hC11 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 - u + θ * u) ^ 6 * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 11 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hC12 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 - u + θ * u) ^ 7 * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 12 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  have hC13 : ∀ p : ℝ, p / (θ - 1) ^ 13 * (1 - u + θ * u) ^ 8 * (1 - u + θ * u) ^ 5 * (θ - 1) ^ 13 = p * (1 - u + θ * u) ^ 13 := fun p => by
    first | (field_simp; done) | (field_simp; ring)
  first
    | (rw [div_eq_iff (pow_ne_zero 5 hd)]; refine mul_right_cancel₀ (pow_ne_zero 13 h1) ?_; linear_combination hkey - hC0 (((-10 : ℝ)/3) * θ^9 + ((-10 : ℝ)/3) * θ^8 + ((10 : ℝ)/3) * θ^7 + ((10 : ℝ)/3) * θ^6) - hC1 (((55 : ℝ)/3) * θ^9 + ((151 : ℝ)/3) * θ^8 + ((-151 : ℝ)/3) * θ^6 + ((-55 : ℝ)/3) * θ^5) - hC2 (((-125 : ℝ)/3) * θ^9 + ((-1301 : ℝ)/6) * θ^8 + ((-1135 : ℝ)/6) * θ^7 + ((1135 : ℝ)/6) * θ^6 + ((1301 : ℝ)/6) * θ^5 + ((125 : ℝ)/3) * θ^4) - hC3 ((50 : ℝ) * θ^9 + ((2675 : ℝ)/6) * θ^8 + (887 : ℝ) * θ^7 - (887 : ℝ) * θ^5 + ((-2675 : ℝ)/6) * θ^4 - (50 : ℝ) * θ^3) - hC4 (((-100 : ℝ)/3) * θ^9 - (505 : ℝ) * θ^8 + ((-10985 : ℝ)/6) * θ^7 + ((-8575 : ℝ)/6) * θ^6 + ((8575 : ℝ)/6) * θ^5 + ((10985 : ℝ)/6) * θ^4 + (505 : ℝ) * θ^3 + ((100 : ℝ)/3) * θ^2) - hC5 (((35 : ℝ)/3) * θ^9 + ((970 : ℝ)/3) * θ^8 + (2050 : ℝ) * θ^7 + ((10885 : ℝ)/3) * θ^6 + ((-10885 : ℝ)/3) * θ^4 - (2050 : ℝ) * θ^3 + ((-970 : ℝ)/3) * θ^2 + ((-35 : ℝ)/3) * θ) - hC6 (((-5 : ℝ)/3) * θ^9 + ((-219 : ℝ)/2) * θ^8 + ((-7745 : ℝ)/6) * θ^7 + ((-25823 : ℝ)/6) * θ^6 + ((-19565 : ℝ)/6) * θ^5 + ((19565 : ℝ)/6) * θ^4 + ((25823 : ℝ)/6) * θ^3 + ((7745 : ℝ)/6) * θ^2 + ((219 : ℝ)/2) * θ + ((5 : ℝ)/3)) - hC7 (((91 : ℝ)/6) * θ^8 + ((1285 : ℝ)/3) * θ^7 + (2750 : ℝ) * θ^6 + ((14707 : ℝ)/3) * θ^5 + ((-14707 : ℝ)/3) * θ^3 - (2750 : ℝ) * θ^2 + ((-1285 : ℝ)/3) * θ + ((-91 : ℝ)/6)) - hC8 (((-347 : ℝ)/6) * θ^7 + ((-1815 : ℝ)/2) * θ^6 + ((-20183 : ℝ)/6) * θ^5 + ((-15925 : ℝ)/6) * θ^4 + ((15925 : ℝ)/6) * θ^3 + ((20183 : ℝ)/6) * θ^2 + ((1815 : ℝ)/2) * θ + ((347 : ℝ)/6)) - hC9 ((120 : ℝ) * θ^6 + ((3385 : ℝ)/3) * θ^5 + (2315 : ℝ) * θ^4 - (2315 : ℝ) * θ^2 + ((-3385 : ℝ)/3) * θ - (120 : ℝ)) - hC10 (((-440 : ℝ)/3) * θ^5 + ((-4955 : ℝ)/6) * θ^4 + ((-4495 : ℝ)/6) * θ^3 + ((4495 : ℝ)/6) * θ^2 + ((4955 : ℝ)/6) * θ + ((440 : ℝ)/3)) - hC11 (((635 : ℝ)/6) * θ^4 + ((991 : ℝ)/3) * θ^3 + ((-991 : ℝ)/3) * θ + ((-635 : ℝ)/6)) - hC12 (((-251 : ℝ)/6) * θ^3 + ((-335 : ℝ)/6) * θ^2 + ((335 : ℝ)/6) * θ + ((251 : ℝ)/6)) - hC13 ((7 : ℝ) * θ^2 - (7 : ℝ)))
    | (rw [div_eq_iff₀ (pow_ne_zero 5 hd)]; refine mul_right_cancel₀ (pow_ne_zero 13 h1) ?_; linear_combination hkey - hC0 (((-10 : ℝ)/3) * θ^9 + ((-10 : ℝ)/3) * θ^8 + ((10 : ℝ)/3) * θ^7 + ((10 : ℝ)/3) * θ^6) - hC1 (((55 : ℝ)/3) * θ^9 + ((151 : ℝ)/3) * θ^8 + ((-151 : ℝ)/3) * θ^6 + ((-55 : ℝ)/3) * θ^5) - hC2 (((-125 : ℝ)/3) * θ^9 + ((-1301 : ℝ)/6) * θ^8 + ((-1135 : ℝ)/6) * θ^7 + ((1135 : ℝ)/6) * θ^6 + ((1301 : ℝ)/6) * θ^5 + ((125 : ℝ)/3) * θ^4) - hC3 ((50 : ℝ) * θ^9 + ((2675 : ℝ)/6) * θ^8 + (887 : ℝ) * θ^7 - (887 : ℝ) * θ^5 + ((-2675 : ℝ)/6) * θ^4 - (50 : ℝ) * θ^3) - hC4 (((-100 : ℝ)/3) * θ^9 - (505 : ℝ) * θ^8 + ((-10985 : ℝ)/6) * θ^7 + ((-8575 : ℝ)/6) * θ^6 + ((8575 : ℝ)/6) * θ^5 + ((10985 : ℝ)/6) * θ^4 + (505 : ℝ) * θ^3 + ((100 : ℝ)/3) * θ^2) - hC5 (((35 : ℝ)/3) * θ^9 + ((970 : ℝ)/3) * θ^8 + (2050 : ℝ) * θ^7 + ((10885 : ℝ)/3) * θ^6 + ((-10885 : ℝ)/3) * θ^4 - (2050 : ℝ) * θ^3 + ((-970 : ℝ)/3) * θ^2 + ((-35 : ℝ)/3) * θ) - hC6 (((-5 : ℝ)/3) * θ^9 + ((-219 : ℝ)/2) * θ^8 + ((-7745 : ℝ)/6) * θ^7 + ((-25823 : ℝ)/6) * θ^6 + ((-19565 : ℝ)/6) * θ^5 + ((19565 : ℝ)/6) * θ^4 + ((25823 : ℝ)/6) * θ^3 + ((7745 : ℝ)/6) * θ^2 + ((219 : ℝ)/2) * θ + ((5 : ℝ)/3)) - hC7 (((91 : ℝ)/6) * θ^8 + ((1285 : ℝ)/3) * θ^7 + (2750 : ℝ) * θ^6 + ((14707 : ℝ)/3) * θ^5 + ((-14707 : ℝ)/3) * θ^3 - (2750 : ℝ) * θ^2 + ((-1285 : ℝ)/3) * θ + ((-91 : ℝ)/6)) - hC8 (((-347 : ℝ)/6) * θ^7 + ((-1815 : ℝ)/2) * θ^6 + ((-20183 : ℝ)/6) * θ^5 + ((-15925 : ℝ)/6) * θ^4 + ((15925 : ℝ)/6) * θ^3 + ((20183 : ℝ)/6) * θ^2 + ((1815 : ℝ)/2) * θ + ((347 : ℝ)/6)) - hC9 ((120 : ℝ) * θ^6 + ((3385 : ℝ)/3) * θ^5 + (2315 : ℝ) * θ^4 - (2315 : ℝ) * θ^2 + ((-3385 : ℝ)/3) * θ - (120 : ℝ)) - hC10 (((-440 : ℝ)/3) * θ^5 + ((-4955 : ℝ)/6) * θ^4 + ((-4495 : ℝ)/6) * θ^3 + ((4495 : ℝ)/6) * θ^2 + ((4955 : ℝ)/6) * θ + ((440 : ℝ)/3)) - hC11 (((635 : ℝ)/6) * θ^4 + ((991 : ℝ)/3) * θ^3 + ((-991 : ℝ)/3) * θ + ((-635 : ℝ)/6)) - hC12 (((-251 : ℝ)/6) * θ^3 + ((-335 : ℝ)/6) * θ^2 + ((335 : ℝ)/6) * θ + ((251 : ℝ)/6)) - hC13 ((7 : ℝ) * θ^2 - (7 : ℝ)))
    | (first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf)

theorem d006259 {θ : ℝ} (hθ : 0 < θ) (ht1 : θ ≠ 1) : _root_.GD.N0155.d006255 θ = _root_.GD.N0155.d006222 θ := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hθ0 : θ ≠ 0 := ne_of_gt hθ
  have hθ1 : θ + 1 ≠ 0 := by positivity
  have hI : (∫ u in (0:ℝ)..1, _root_.GD.N0155.d006253 θ u)
      = ∫ u in (0:ℝ)..1, ((((500 : ℝ) * θ^12 - (1000 : ℝ) * θ^10 + (500 : ℝ) * θ^8) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 8) + (((-3500 : ℝ) * θ^12 - (4620 : ℝ) * θ^11 + (8120 : ℝ) * θ^10 + (8120 : ℝ) * θ^9 - (4620 : ℝ) * θ^8 - (3500 : ℝ) * θ^7) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 7) + (((10625 : ℝ) * θ^12 + (32090 : ℝ) * θ^11 - (9449 : ℝ) * θ^10 - (66532 : ℝ) * θ^9 - (9449 : ℝ) * θ^8 + (32090 : ℝ) * θ^7 + (10625 : ℝ) * θ^6) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 6) + (((-18250 : ℝ) * θ^12 - (96550 : ℝ) * θ^11 - (75002 : ℝ) * θ^10 + (189802 : ℝ) * θ^9 + (189802 : ℝ) * θ^8 - (75002 : ℝ) * θ^7 - (96550 : ℝ) * θ^6 - (18250 : ℝ) * θ^5) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 5) + (((19375 : ℝ) * θ^12 + (164130 : ℝ) * θ^11 + (323570 : ℝ) * θ^10 - (157074 : ℝ) * θ^9 - (700002 : ℝ) * θ^8 - (157074 : ℝ) * θ^7 + (323570 : ℝ) * θ^6 + (164130 : ℝ) * θ^5 + (19375 : ℝ) * θ^4) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 4) + (((-13000 : ℝ) * θ^12 - (172150 : ℝ) * θ^11 - (608354 : ℝ) * θ^10 - (349190 : ℝ) * θ^9 + (1142694 : ℝ) * θ^8 + (1142694 : ℝ) * θ^7 - (349190 : ℝ) * θ^6 - (608354 : ℝ) * θ^5 - (172150 : ℝ) * θ^4 - (13000 : ℝ) * θ^3) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 3) + (((5375 : ℝ) * θ^12 + (113870 : ℝ) * θ^11 + (661600 : ℝ) * θ^10 + (1101574 : ℝ) * θ^9 - (649335 : ℝ) * θ^8 - (2466168 : ℝ) * θ^7 - (649335 : ℝ) * θ^6 + (1101574 : ℝ) * θ^5 + (661600 : ℝ) * θ^4 + (113870 : ℝ) * θ^3 + (5375 : ℝ) * θ^2) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 2) + (((-1250 : ℝ) * θ^12 - (46290 : ℝ) * θ^11 - (442126 : ℝ) * θ^10 - (1380738 : ℝ) * θ^9 - (695916 : ℝ) * θ^8 + (2566320 : ℝ) * θ^7 + (2566320 : ℝ) * θ^6 - (695916 : ℝ) * θ^5 - (1380738 : ℝ) * θ^4 - (442126 : ℝ) * θ^3 - (46290 : ℝ) * θ^2 - (1250 : ℝ) * θ) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u) + (((125 : ℝ) * θ^12 + (10550 : ℝ) * θ^11 + (179062 : ℝ) * θ^10 + (973978 : ℝ) * θ^9 + (1571793 : ℝ) * θ^8 - (961008 : ℝ) * θ^7 - (3549000 : ℝ) * θ^6 - (961008 : ℝ) * θ^5 + (1571793 : ℝ) * θ^4 + (973978 : ℝ) * θ^3 + (179062 : ℝ) * θ^2 + (10550 : ℝ) * θ + (125 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 0 + (((-1030 : ℝ) * θ^11 - (40270 : ℝ) * θ^10 - (401546 : ℝ) * θ^9 - (1292678 : ℝ) * θ^8 - (677916 : ℝ) * θ^7 + (2413440 : ℝ) * θ^6 + (2413440 : ℝ) * θ^5 - (677916 : ℝ) * θ^4 - (1292678 : ℝ) * θ^3 - (401546 : ℝ) * θ^2 - (40270 : ℝ) * θ - (1030 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 1 + (((3849 : ℝ) * θ^10 + (90070 : ℝ) * θ^9 + (563376 : ℝ) * θ^8 + (989966 : ℝ) * θ^7 - (549585 : ℝ) * θ^6 - (2195352 : ℝ) * θ^5 - (549585 : ℝ) * θ^4 + (989966 : ℝ) * θ^3 + (563376 : ℝ) * θ^2 + (90070 : ℝ) * θ + (3849 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 2 + (((-8464 : ℝ) * θ^9 - (128050 : ℝ) * θ^8 - (497222 : ℝ) * θ^7 - (317690 : ℝ) * θ^6 + (951426 : ℝ) * θ^5 + (951426 : ℝ) * θ^4 - (317690 : ℝ) * θ^3 - (497222 : ℝ) * θ^2 - (128050 : ℝ) * θ - (8464 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 3 + (((11885 : ℝ) * θ^8 + (117650 : ℝ) * θ^7 + (259030 : ℝ) * θ^6 - (110594 : ℝ) * θ^5 - (555942 : ℝ) * θ^4 - (110594 : ℝ) * θ^3 + (259030 : ℝ) * θ^2 + (117650 : ℝ) * θ + (11885 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 4 + (((-10830 : ℝ) * θ^7 - (67850 : ℝ) * θ^6 - (61422 : ℝ) * θ^5 + (140102 : ℝ) * θ^4 + (140102 : ℝ) * θ^3 - (61422 : ℝ) * θ^2 - (67850 : ℝ) * θ - (10830 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 5 + (((6215 : ℝ) * θ^6 + (22370 : ℝ) * θ^5 - (5039 : ℝ) * θ^4 - (47092 : ℝ) * θ^3 - (5039 : ℝ) * θ^2 + (22370 : ℝ) * θ + (6215 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 6 + (((-2044 : ℝ) * θ^5 - (3220 : ℝ) * θ^4 + (5264 : ℝ) * θ^3 + (5264 : ℝ) * θ^2 - (3220 : ℝ) * θ - (2044 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 7 + (((294 : ℝ) * θ^4 - (588 : ℝ) * θ^2 + (294 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 8) :=
    intervalIntegral.integral_congr fun u hu => by
      obtain ⟨hu0, hu1⟩ := _root_.GD.N0155.d006245 hu
      exact _root_.GD.N0155.d006257 ht1 (ne_of_gt (_root_.GD.N0155.d006243 hθ hu0 hu1))
  unfold _root_.GD.N0155.d006255
  rw [hI]
  have ii0 : IntervalIntegrable (fun u => (((500 : ℝ) * θ^12 - (1000 : ℝ) * θ^10 + (500 : ℝ) * θ^8) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 8)) volume 0 1 := _root_.GD.N0155.d006249 hθ _ 8
  have ii1 : IntervalIntegrable (fun u => (((-3500 : ℝ) * θ^12 - (4620 : ℝ) * θ^11 + (8120 : ℝ) * θ^10 + (8120 : ℝ) * θ^9 - (4620 : ℝ) * θ^8 - (3500 : ℝ) * θ^7) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 7)) volume 0 1 := _root_.GD.N0155.d006249 hθ _ 7
  have ii2 : IntervalIntegrable (fun u => (((10625 : ℝ) * θ^12 + (32090 : ℝ) * θ^11 - (9449 : ℝ) * θ^10 - (66532 : ℝ) * θ^9 - (9449 : ℝ) * θ^8 + (32090 : ℝ) * θ^7 + (10625 : ℝ) * θ^6) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 6)) volume 0 1 := _root_.GD.N0155.d006249 hθ _ 6
  have ii3 : IntervalIntegrable (fun u => (((-18250 : ℝ) * θ^12 - (96550 : ℝ) * θ^11 - (75002 : ℝ) * θ^10 + (189802 : ℝ) * θ^9 + (189802 : ℝ) * θ^8 - (75002 : ℝ) * θ^7 - (96550 : ℝ) * θ^6 - (18250 : ℝ) * θ^5) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 5)) volume 0 1 := _root_.GD.N0155.d006249 hθ _ 5
  have ii4 : IntervalIntegrable (fun u => (((19375 : ℝ) * θ^12 + (164130 : ℝ) * θ^11 + (323570 : ℝ) * θ^10 - (157074 : ℝ) * θ^9 - (700002 : ℝ) * θ^8 - (157074 : ℝ) * θ^7 + (323570 : ℝ) * θ^6 + (164130 : ℝ) * θ^5 + (19375 : ℝ) * θ^4) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 4)) volume 0 1 := _root_.GD.N0155.d006249 hθ _ 4
  have ii5 : IntervalIntegrable (fun u => (((-13000 : ℝ) * θ^12 - (172150 : ℝ) * θ^11 - (608354 : ℝ) * θ^10 - (349190 : ℝ) * θ^9 + (1142694 : ℝ) * θ^8 + (1142694 : ℝ) * θ^7 - (349190 : ℝ) * θ^6 - (608354 : ℝ) * θ^5 - (172150 : ℝ) * θ^4 - (13000 : ℝ) * θ^3) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 3)) volume 0 1 := _root_.GD.N0155.d006249 hθ _ 3
  have ii6 : IntervalIntegrable (fun u => (((5375 : ℝ) * θ^12 + (113870 : ℝ) * θ^11 + (661600 : ℝ) * θ^10 + (1101574 : ℝ) * θ^9 - (649335 : ℝ) * θ^8 - (2466168 : ℝ) * θ^7 - (649335 : ℝ) * θ^6 + (1101574 : ℝ) * θ^5 + (661600 : ℝ) * θ^4 + (113870 : ℝ) * θ^3 + (5375 : ℝ) * θ^2) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u ^ 2)) volume 0 1 := _root_.GD.N0155.d006249 hθ _ 2
  have ii7 : IntervalIntegrable (fun u => (((-1250 : ℝ) * θ^12 - (46290 : ℝ) * θ^11 - (442126 : ℝ) * θ^10 - (1380738 : ℝ) * θ^9 - (695916 : ℝ) * θ^8 + (2566320 : ℝ) * θ^7 + (2566320 : ℝ) * θ^6 - (695916 : ℝ) * θ^5 - (1380738 : ℝ) * θ^4 - (442126 : ℝ) * θ^3 - (46290 : ℝ) * θ^2 - (1250 : ℝ) * θ) / (θ - 1) ^ 16) * (1 / _root_.GD.N0155.d006241 θ u)) volume 0 1 := _root_.GD.N0155.d006250 hθ _
  have ii8 : IntervalIntegrable (fun u => (((125 : ℝ) * θ^12 + (10550 : ℝ) * θ^11 + (179062 : ℝ) * θ^10 + (973978 : ℝ) * θ^9 + (1571793 : ℝ) * θ^8 - (961008 : ℝ) * θ^7 - (3549000 : ℝ) * θ^6 - (961008 : ℝ) * θ^5 + (1571793 : ℝ) * θ^4 + (973978 : ℝ) * θ^3 + (179062 : ℝ) * θ^2 + (10550 : ℝ) * θ + (125 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 0) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 0
  have ii9 : IntervalIntegrable (fun u => (((-1030 : ℝ) * θ^11 - (40270 : ℝ) * θ^10 - (401546 : ℝ) * θ^9 - (1292678 : ℝ) * θ^8 - (677916 : ℝ) * θ^7 + (2413440 : ℝ) * θ^6 + (2413440 : ℝ) * θ^5 - (677916 : ℝ) * θ^4 - (1292678 : ℝ) * θ^3 - (401546 : ℝ) * θ^2 - (40270 : ℝ) * θ - (1030 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 1) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 1
  have ii10 : IntervalIntegrable (fun u => (((3849 : ℝ) * θ^10 + (90070 : ℝ) * θ^9 + (563376 : ℝ) * θ^8 + (989966 : ℝ) * θ^7 - (549585 : ℝ) * θ^6 - (2195352 : ℝ) * θ^5 - (549585 : ℝ) * θ^4 + (989966 : ℝ) * θ^3 + (563376 : ℝ) * θ^2 + (90070 : ℝ) * θ + (3849 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 2) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 2
  have ii11 : IntervalIntegrable (fun u => (((-8464 : ℝ) * θ^9 - (128050 : ℝ) * θ^8 - (497222 : ℝ) * θ^7 - (317690 : ℝ) * θ^6 + (951426 : ℝ) * θ^5 + (951426 : ℝ) * θ^4 - (317690 : ℝ) * θ^3 - (497222 : ℝ) * θ^2 - (128050 : ℝ) * θ - (8464 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 3) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 3
  have ii12 : IntervalIntegrable (fun u => (((11885 : ℝ) * θ^8 + (117650 : ℝ) * θ^7 + (259030 : ℝ) * θ^6 - (110594 : ℝ) * θ^5 - (555942 : ℝ) * θ^4 - (110594 : ℝ) * θ^3 + (259030 : ℝ) * θ^2 + (117650 : ℝ) * θ + (11885 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 4) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 4
  have ii13 : IntervalIntegrable (fun u => (((-10830 : ℝ) * θ^7 - (67850 : ℝ) * θ^6 - (61422 : ℝ) * θ^5 + (140102 : ℝ) * θ^4 + (140102 : ℝ) * θ^3 - (61422 : ℝ) * θ^2 - (67850 : ℝ) * θ - (10830 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 5) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 5
  have ii14 : IntervalIntegrable (fun u => (((6215 : ℝ) * θ^6 + (22370 : ℝ) * θ^5 - (5039 : ℝ) * θ^4 - (47092 : ℝ) * θ^3 - (5039 : ℝ) * θ^2 + (22370 : ℝ) * θ + (6215 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 6) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 6
  have ii15 : IntervalIntegrable (fun u => (((-2044 : ℝ) * θ^5 - (3220 : ℝ) * θ^4 + (5264 : ℝ) * θ^3 + (5264 : ℝ) * θ^2 - (3220 : ℝ) * θ - (2044 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 7) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 7
  have ii16 : IntervalIntegrable (fun u => (((294 : ℝ) * θ^4 - (588 : ℝ) * θ^2 + (294 : ℝ)) / (θ - 1) ^ 16) * _root_.GD.N0155.d006241 θ u ^ 8) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 8
  have iF0 := ii0
  have iF1 := iF0.add ii1
  have iF2 := iF1.add ii2
  have iF3 := iF2.add ii3
  have iF4 := iF3.add ii4
  have iF5 := iF4.add ii5
  have iF6 := iF5.add ii6
  have iF7 := iF6.add ii7
  have iF8 := iF7.add ii8
  have iF9 := iF8.add ii9
  have iF10 := iF9.add ii10
  have iF11 := iF10.add ii11
  have iF12 := iF11.add ii12
  have iF13 := iF12.add ii13
  have iF14 := iF13.add ii14
  have iF15 := iF14.add ii15
  have iF16 := iF15.add ii16
  rw [intervalIntegral.integral_add iF15 ii16, intervalIntegral.integral_add iF14 ii15, intervalIntegral.integral_add iF13 ii14, intervalIntegral.integral_add iF12 ii13, intervalIntegral.integral_add iF11 ii12, intervalIntegral.integral_add iF10 ii11, intervalIntegral.integral_add iF9 ii10, intervalIntegral.integral_add iF8 ii9, intervalIntegral.integral_add iF7 ii8, intervalIntegral.integral_add iF6 ii7, intervalIntegral.integral_add iF5 ii6, intervalIntegral.integral_add iF4 ii5, intervalIntegral.integral_add iF3 ii4, intervalIntegral.integral_add iF2 ii3, intervalIntegral.integral_add iF1 ii2, intervalIntegral.integral_add iF0 ii1]
  simp only [intervalIntegral.integral_const_mul]
  rw [_root_.GD.N0155.d006247 hθ ht1 8 (by norm_num), _root_.GD.N0155.d006247 hθ ht1 7 (by norm_num), _root_.GD.N0155.d006247 hθ ht1 6 (by norm_num), _root_.GD.N0155.d006247 hθ ht1 5 (by norm_num), _root_.GD.N0155.d006247 hθ ht1 4 (by norm_num), _root_.GD.N0155.d006247 hθ ht1 3 (by norm_num), _root_.GD.N0155.d006247 hθ ht1 2 (by norm_num), _root_.GD.N0155.d006248 hθ ht1, _root_.GD.N0155.d006246 hθ ht1 0, _root_.GD.N0155.d006246 hθ ht1 1, _root_.GD.N0155.d006246 hθ ht1 2, _root_.GD.N0155.d006246 hθ ht1 3, _root_.GD.N0155.d006246 hθ ht1 4, _root_.GD.N0155.d006246 hθ ht1 5, _root_.GD.N0155.d006246 hθ ht1 6, _root_.GD.N0155.d006246 hθ ht1 7, _root_.GD.N0155.d006246 hθ ht1 8]
  simp only [_root_.GD.N0155.d006222, _root_.GD.N0155.d006219, _root_.GD.N0155.d006220]
  norm_num
  first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf

theorem d006260 {θ : ℝ} (hθ : 0 < θ) (ht1 : θ ≠ 1) : _root_.GD.N0155.d006256 θ = _root_.GD.N0155.d006221 θ := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hθ0 : θ ≠ 0 := ne_of_gt hθ
  have hθ1 : θ + 1 ≠ 0 := by positivity
  have hI : (∫ u in (0:ℝ)..1, _root_.GD.N0155.d006254 θ u)
      = ∫ u in (0:ℝ)..1, (((((-10 : ℝ)/3) * θ^9 + ((-10 : ℝ)/3) * θ^8 + ((10 : ℝ)/3) * θ^7 + ((10 : ℝ)/3) * θ^6) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u ^ 5) + ((((55 : ℝ)/3) * θ^9 + ((151 : ℝ)/3) * θ^8 + ((-151 : ℝ)/3) * θ^6 + ((-55 : ℝ)/3) * θ^5) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u ^ 4) + ((((-125 : ℝ)/3) * θ^9 + ((-1301 : ℝ)/6) * θ^8 + ((-1135 : ℝ)/6) * θ^7 + ((1135 : ℝ)/6) * θ^6 + ((1301 : ℝ)/6) * θ^5 + ((125 : ℝ)/3) * θ^4) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u ^ 3) + (((50 : ℝ) * θ^9 + ((2675 : ℝ)/6) * θ^8 + (887 : ℝ) * θ^7 - (887 : ℝ) * θ^5 + ((-2675 : ℝ)/6) * θ^4 - (50 : ℝ) * θ^3) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u ^ 2) + ((((-100 : ℝ)/3) * θ^9 - (505 : ℝ) * θ^8 + ((-10985 : ℝ)/6) * θ^7 + ((-8575 : ℝ)/6) * θ^6 + ((8575 : ℝ)/6) * θ^5 + ((10985 : ℝ)/6) * θ^4 + (505 : ℝ) * θ^3 + ((100 : ℝ)/3) * θ^2) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u) + ((((35 : ℝ)/3) * θ^9 + ((970 : ℝ)/3) * θ^8 + (2050 : ℝ) * θ^7 + ((10885 : ℝ)/3) * θ^6 + ((-10885 : ℝ)/3) * θ^4 - (2050 : ℝ) * θ^3 + ((-970 : ℝ)/3) * θ^2 + ((-35 : ℝ)/3) * θ) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 0 + ((((-5 : ℝ)/3) * θ^9 + ((-219 : ℝ)/2) * θ^8 + ((-7745 : ℝ)/6) * θ^7 + ((-25823 : ℝ)/6) * θ^6 + ((-19565 : ℝ)/6) * θ^5 + ((19565 : ℝ)/6) * θ^4 + ((25823 : ℝ)/6) * θ^3 + ((7745 : ℝ)/6) * θ^2 + ((219 : ℝ)/2) * θ + ((5 : ℝ)/3)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 1 + ((((91 : ℝ)/6) * θ^8 + ((1285 : ℝ)/3) * θ^7 + (2750 : ℝ) * θ^6 + ((14707 : ℝ)/3) * θ^5 + ((-14707 : ℝ)/3) * θ^3 - (2750 : ℝ) * θ^2 + ((-1285 : ℝ)/3) * θ + ((-91 : ℝ)/6)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 2 + ((((-347 : ℝ)/6) * θ^7 + ((-1815 : ℝ)/2) * θ^6 + ((-20183 : ℝ)/6) * θ^5 + ((-15925 : ℝ)/6) * θ^4 + ((15925 : ℝ)/6) * θ^3 + ((20183 : ℝ)/6) * θ^2 + ((1815 : ℝ)/2) * θ + ((347 : ℝ)/6)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 3 + (((120 : ℝ) * θ^6 + ((3385 : ℝ)/3) * θ^5 + (2315 : ℝ) * θ^4 - (2315 : ℝ) * θ^2 + ((-3385 : ℝ)/3) * θ - (120 : ℝ)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 4 + ((((-440 : ℝ)/3) * θ^5 + ((-4955 : ℝ)/6) * θ^4 + ((-4495 : ℝ)/6) * θ^3 + ((4495 : ℝ)/6) * θ^2 + ((4955 : ℝ)/6) * θ + ((440 : ℝ)/3)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 5 + ((((635 : ℝ)/6) * θ^4 + ((991 : ℝ)/3) * θ^3 + ((-991 : ℝ)/3) * θ + ((-635 : ℝ)/6)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 6 + ((((-251 : ℝ)/6) * θ^3 + ((-335 : ℝ)/6) * θ^2 + ((335 : ℝ)/6) * θ + ((251 : ℝ)/6)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 7 + (((7 : ℝ) * θ^2 - (7 : ℝ)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 8) :=
    intervalIntegral.integral_congr fun u hu => by
      obtain ⟨hu0, hu1⟩ := _root_.GD.N0155.d006245 hu
      exact _root_.GD.N0155.d006258 ht1 (ne_of_gt (_root_.GD.N0155.d006243 hθ hu0 hu1))
  unfold _root_.GD.N0155.d006256
  rw [hI]
  have ii0 : IntervalIntegrable (fun u => ((((-10 : ℝ)/3) * θ^9 + ((-10 : ℝ)/3) * θ^8 + ((10 : ℝ)/3) * θ^7 + ((10 : ℝ)/3) * θ^6) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u ^ 5)) volume 0 1 := _root_.GD.N0155.d006249 hθ _ 5
  have ii1 : IntervalIntegrable (fun u => ((((55 : ℝ)/3) * θ^9 + ((151 : ℝ)/3) * θ^8 + ((-151 : ℝ)/3) * θ^6 + ((-55 : ℝ)/3) * θ^5) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u ^ 4)) volume 0 1 := _root_.GD.N0155.d006249 hθ _ 4
  have ii2 : IntervalIntegrable (fun u => ((((-125 : ℝ)/3) * θ^9 + ((-1301 : ℝ)/6) * θ^8 + ((-1135 : ℝ)/6) * θ^7 + ((1135 : ℝ)/6) * θ^6 + ((1301 : ℝ)/6) * θ^5 + ((125 : ℝ)/3) * θ^4) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u ^ 3)) volume 0 1 := _root_.GD.N0155.d006249 hθ _ 3
  have ii3 : IntervalIntegrable (fun u => (((50 : ℝ) * θ^9 + ((2675 : ℝ)/6) * θ^8 + (887 : ℝ) * θ^7 - (887 : ℝ) * θ^5 + ((-2675 : ℝ)/6) * θ^4 - (50 : ℝ) * θ^3) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u ^ 2)) volume 0 1 := _root_.GD.N0155.d006249 hθ _ 2
  have ii4 : IntervalIntegrable (fun u => ((((-100 : ℝ)/3) * θ^9 - (505 : ℝ) * θ^8 + ((-10985 : ℝ)/6) * θ^7 + ((-8575 : ℝ)/6) * θ^6 + ((8575 : ℝ)/6) * θ^5 + ((10985 : ℝ)/6) * θ^4 + (505 : ℝ) * θ^3 + ((100 : ℝ)/3) * θ^2) / (θ - 1) ^ 13) * (1 / _root_.GD.N0155.d006241 θ u)) volume 0 1 := _root_.GD.N0155.d006250 hθ _
  have ii5 : IntervalIntegrable (fun u => ((((35 : ℝ)/3) * θ^9 + ((970 : ℝ)/3) * θ^8 + (2050 : ℝ) * θ^7 + ((10885 : ℝ)/3) * θ^6 + ((-10885 : ℝ)/3) * θ^4 - (2050 : ℝ) * θ^3 + ((-970 : ℝ)/3) * θ^2 + ((-35 : ℝ)/3) * θ) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 0) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 0
  have ii6 : IntervalIntegrable (fun u => ((((-5 : ℝ)/3) * θ^9 + ((-219 : ℝ)/2) * θ^8 + ((-7745 : ℝ)/6) * θ^7 + ((-25823 : ℝ)/6) * θ^6 + ((-19565 : ℝ)/6) * θ^5 + ((19565 : ℝ)/6) * θ^4 + ((25823 : ℝ)/6) * θ^3 + ((7745 : ℝ)/6) * θ^2 + ((219 : ℝ)/2) * θ + ((5 : ℝ)/3)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 1) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 1
  have ii7 : IntervalIntegrable (fun u => ((((91 : ℝ)/6) * θ^8 + ((1285 : ℝ)/3) * θ^7 + (2750 : ℝ) * θ^6 + ((14707 : ℝ)/3) * θ^5 + ((-14707 : ℝ)/3) * θ^3 - (2750 : ℝ) * θ^2 + ((-1285 : ℝ)/3) * θ + ((-91 : ℝ)/6)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 2) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 2
  have ii8 : IntervalIntegrable (fun u => ((((-347 : ℝ)/6) * θ^7 + ((-1815 : ℝ)/2) * θ^6 + ((-20183 : ℝ)/6) * θ^5 + ((-15925 : ℝ)/6) * θ^4 + ((15925 : ℝ)/6) * θ^3 + ((20183 : ℝ)/6) * θ^2 + ((1815 : ℝ)/2) * θ + ((347 : ℝ)/6)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 3) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 3
  have ii9 : IntervalIntegrable (fun u => (((120 : ℝ) * θ^6 + ((3385 : ℝ)/3) * θ^5 + (2315 : ℝ) * θ^4 - (2315 : ℝ) * θ^2 + ((-3385 : ℝ)/3) * θ - (120 : ℝ)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 4) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 4
  have ii10 : IntervalIntegrable (fun u => ((((-440 : ℝ)/3) * θ^5 + ((-4955 : ℝ)/6) * θ^4 + ((-4495 : ℝ)/6) * θ^3 + ((4495 : ℝ)/6) * θ^2 + ((4955 : ℝ)/6) * θ + ((440 : ℝ)/3)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 5) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 5
  have ii11 : IntervalIntegrable (fun u => ((((635 : ℝ)/6) * θ^4 + ((991 : ℝ)/3) * θ^3 + ((-991 : ℝ)/3) * θ + ((-635 : ℝ)/6)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 6) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 6
  have ii12 : IntervalIntegrable (fun u => ((((-251 : ℝ)/6) * θ^3 + ((-335 : ℝ)/6) * θ^2 + ((335 : ℝ)/6) * θ + ((251 : ℝ)/6)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 7) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 7
  have ii13 : IntervalIntegrable (fun u => (((7 : ℝ) * θ^2 - (7 : ℝ)) / (θ - 1) ^ 13) * _root_.GD.N0155.d006241 θ u ^ 8) volume 0 1 := _root_.GD.N0155.d006251 (θ := θ) _ 8
  have iF0 := ii0
  have iF1 := iF0.add ii1
  have iF2 := iF1.add ii2
  have iF3 := iF2.add ii3
  have iF4 := iF3.add ii4
  have iF5 := iF4.add ii5
  have iF6 := iF5.add ii6
  have iF7 := iF6.add ii7
  have iF8 := iF7.add ii8
  have iF9 := iF8.add ii9
  have iF10 := iF9.add ii10
  have iF11 := iF10.add ii11
  have iF12 := iF11.add ii12
  have iF13 := iF12.add ii13
  rw [intervalIntegral.integral_add iF12 ii13, intervalIntegral.integral_add iF11 ii12, intervalIntegral.integral_add iF10 ii11, intervalIntegral.integral_add iF9 ii10, intervalIntegral.integral_add iF8 ii9, intervalIntegral.integral_add iF7 ii8, intervalIntegral.integral_add iF6 ii7, intervalIntegral.integral_add iF5 ii6, intervalIntegral.integral_add iF4 ii5, intervalIntegral.integral_add iF3 ii4, intervalIntegral.integral_add iF2 ii3, intervalIntegral.integral_add iF1 ii2, intervalIntegral.integral_add iF0 ii1]
  simp only [intervalIntegral.integral_const_mul]
  rw [_root_.GD.N0155.d006247 hθ ht1 5 (by norm_num), _root_.GD.N0155.d006247 hθ ht1 4 (by norm_num), _root_.GD.N0155.d006247 hθ ht1 3 (by norm_num), _root_.GD.N0155.d006247 hθ ht1 2 (by norm_num), _root_.GD.N0155.d006248 hθ ht1, _root_.GD.N0155.d006246 hθ ht1 0, _root_.GD.N0155.d006246 hθ ht1 1, _root_.GD.N0155.d006246 hθ ht1 2, _root_.GD.N0155.d006246 hθ ht1 3, _root_.GD.N0155.d006246 hθ ht1 4, _root_.GD.N0155.d006246 hθ ht1 5, _root_.GD.N0155.d006246 hθ ht1 6, _root_.GD.N0155.d006246 hθ ht1 7, _root_.GD.N0155.d006246 hθ ht1 8]
  simp only [_root_.GD.N0155.d006221, _root_.GD.N0155.d006217, _root_.GD.N0155.d006218]
  norm_num
  first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf

theorem d006261 : _root_.GD.N0155.d006255 1 = 39 / 4576 := by
  unfold _root_.GD.N0155.d006255
  have hI : (∫ u in (0:ℝ)..1, _root_.GD.N0155.d006253 1 u)
      = ∫ u in (0:ℝ)..1, ((936 : ℝ) * u^14 + (-6552 : ℝ) * u^13 + (19890 : ℝ) * u^12 + (-34164 : ℝ) * u^11 + (36270 : ℝ) * u^10 + (-24336 : ℝ) * u^9 + (10062 : ℝ) * u^8 + (-2340 : ℝ) * u^7 + (234 : ℝ) * u^6) :=
    intervalIntegral.integral_congr fun u _ => by
      unfold _root_.GD.N0155.d006253 _root_.GD.N0155.d006241
      rw [show (1:ℝ) - u + 1 * u = 1 by ring]
      norm_num
      first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf
  rw [hI]
  have jj0 : IntervalIntegrable (fun u : ℝ => (936 : ℝ) * u^14) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj1 : IntervalIntegrable (fun u : ℝ => (-6552 : ℝ) * u^13) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj2 : IntervalIntegrable (fun u : ℝ => (19890 : ℝ) * u^12) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj3 : IntervalIntegrable (fun u : ℝ => (-34164 : ℝ) * u^11) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj4 : IntervalIntegrable (fun u : ℝ => (36270 : ℝ) * u^10) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj5 : IntervalIntegrable (fun u : ℝ => (-24336 : ℝ) * u^9) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj6 : IntervalIntegrable (fun u : ℝ => (10062 : ℝ) * u^8) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj7 : IntervalIntegrable (fun u : ℝ => (-2340 : ℝ) * u^7) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj8 : IntervalIntegrable (fun u : ℝ => (234 : ℝ) * u^6) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jF0 := jj0
  have jF1 := jF0.add jj1
  have jF2 := jF1.add jj2
  have jF3 := jF2.add jj3
  have jF4 := jF3.add jj4
  have jF5 := jF4.add jj5
  have jF6 := jF5.add jj6
  have jF7 := jF6.add jj7
  have jF8 := jF7.add jj8
  rw [intervalIntegral.integral_add jF7 jj8, intervalIntegral.integral_add jF6 jj7, intervalIntegral.integral_add jF5 jj6, intervalIntegral.integral_add jF4 jj5, intervalIntegral.integral_add jF3 jj4, intervalIntegral.integral_add jF2 jj3, intervalIntegral.integral_add jF1 jj2, intervalIntegral.integral_add jF0 jj1]
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  norm_num

theorem d006262 : _root_.GD.N0155.d006256 1 = -5 / 6864 := by
  unfold _root_.GD.N0155.d006256
  have hI : (∫ u in (0:ℝ)..1, _root_.GD.N0155.d006254 1 u)
      = ∫ u in (0:ℝ)..1, (((2 : ℝ)/3) * u^12 + (-4 : ℝ) * u^11 + ((61 : ℝ)/6) * u^10 + ((-85 : ℝ)/6) * u^9 + ((35 : ℝ)/3) * u^8 + ((-17 : ℝ)/3) * u^7 + ((3 : ℝ)/2) * u^6 + ((-1 : ℝ)/6) * u^5) :=
    intervalIntegral.integral_congr fun u _ => by
      unfold _root_.GD.N0155.d006254 _root_.GD.N0155.d006241
      rw [show (1:ℝ) - u + 1 * u = 1 by ring]
      norm_num
      first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf
  rw [hI]
  have jj0 : IntervalIntegrable (fun u : ℝ => ((2 : ℝ)/3) * u^12) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj1 : IntervalIntegrable (fun u : ℝ => (-4 : ℝ) * u^11) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj2 : IntervalIntegrable (fun u : ℝ => ((61 : ℝ)/6) * u^10) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj3 : IntervalIntegrable (fun u : ℝ => ((-85 : ℝ)/6) * u^9) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj4 : IntervalIntegrable (fun u : ℝ => ((35 : ℝ)/3) * u^8) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj5 : IntervalIntegrable (fun u : ℝ => ((-17 : ℝ)/3) * u^7) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj6 : IntervalIntegrable (fun u : ℝ => ((3 : ℝ)/2) * u^6) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jj7 : IntervalIntegrable (fun u : ℝ => ((-1 : ℝ)/6) * u^5) volume 0 1 := _root_.GD.N0155.d006252 _ _
  have jF0 := jj0
  have jF1 := jF0.add jj1
  have jF2 := jF1.add jj2
  have jF3 := jF2.add jj3
  have jF4 := jF3.add jj4
  have jF5 := jF4.add jj5
  have jF6 := jF5.add jj6
  have jF7 := jF6.add jj7
  rw [intervalIntegral.integral_add jF6 jj7, intervalIntegral.integral_add jF5 jj6, intervalIntegral.integral_add jF4 jj5, intervalIntegral.integral_add jF3 jj4, intervalIntegral.integral_add jF2 jj3, intervalIntegral.integral_add jF1 jj2, intervalIntegral.integral_add jF0 jj1]
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  norm_num



theorem d006263 {θ : ℝ} (hθ : 0 < θ) (ht1 : θ ≠ 1) : 0 < _root_.GD.N0155.d006255 θ := by
  have h1 : θ - 1 ≠ 0 := sub_ne_zero.mpr ht1
  unfold _root_.GD.N0155.d006255
  have hpre : (0:ℝ) < 630 * θ^2 / 96 := by positivity
  refine mul_pos hpre ?_
  apply intervalIntegral.integral_pos (by norm_num : (0:ℝ) < 1)
  ·
    apply ContinuousOn.div
    · first
        | fun_prop
        | exact ((((continuous_pow 6).mul
            ((continuous_const.sub continuous_id).pow 6)).mul
            (((continuous_const.mul continuous_id).sub continuous_const).pow 2)).mul
            ((continuous_const.sub
              (continuous_const.mul (_root_.GD.N0155.d006242 θ))).add
              (continuous_const.mul ((_root_.GD.N0155.d006242 θ).pow 2)))).continuousOn
        | (apply Continuous.continuousOn; continuity)
    · exact ((_root_.GD.N0155.d006242 θ).pow 8).continuousOn
    · intro x hx
      exact pow_ne_zero _ (ne_of_gt (_root_.GD.N0155.d006243 hθ hx.1 hx.2))
  ·
    intro x hx
    unfold _root_.GD.N0155.d006253
    have hd : 0 < _root_.GD.N0155.d006241 θ x := _root_.GD.N0155.d006243 hθ (le_of_lt hx.1) hx.2
    have hq := _root_.GD.N0155.d006181 (_root_.GD.N0155.d006241 θ x) (1+θ) (by positivity)
    have hq2 : (0:ℝ) < 125*(1+θ)^2 - 280*(1+θ)*_root_.GD.N0155.d006241 θ x + 294*_root_.GD.N0155.d006241 θ x ^ 2 := by
      linarith
    have hfac : (0:ℝ) ≤ x^6 * (1-x)^6 * ((1+θ)*x - 1)^2 := by positivity
    exact div_nonneg (mul_nonneg hfac (le_of_lt hq2)) (le_of_lt (pow_pos hd 8))
  ·
    refine ⟨1/2, ⟨by norm_num, by norm_num⟩, ?_⟩
    unfold _root_.GD.N0155.d006253
    have hd : (0:ℝ) < _root_.GD.N0155.d006241 θ (1/2) := _root_.GD.N0155.d006243 hθ (by norm_num) (by norm_num)
    have hq := _root_.GD.N0155.d006181 (_root_.GD.N0155.d006241 θ (1/2)) (1+θ) (by positivity)
    have hq2 : (0:ℝ) < 125*(1+θ)^2 - 280*(1+θ)*_root_.GD.N0155.d006241 θ (1/2) + 294*_root_.GD.N0155.d006241 θ (1/2) ^ 2 := by
      linarith
    have hsq : (0:ℝ) < ((1+θ)*(1/2 : ℝ) - 1)^2 := by
      have he : (1+θ)*(1/2 : ℝ) - 1 = (θ - 1)/2 := by ring
      rw [he]
      positivity
    apply div_pos
    · have hp1 : (0:ℝ) < (1/2 : ℝ)^6 * (1 - 1/2)^6 := by norm_num
      exact mul_pos (mul_pos hp1 hsq) hq2
    · exact pow_pos hd 8


theorem d006264 : ∀ t : ℝ, 0 < t → 0 < _root_.GD.N0155.d006224 t := by
  intro t ht
  by_cases h1 : t = 1
  · subst h1; rw [_root_.GD.N0155.d006226]; norm_num
  · rw [_root_.GD.N0155.d006228 h1, ← _root_.GD.N0155.d006259 ht h1]
    exact _root_.GD.N0155.d006263 ht h1


theorem d006265 : ∀ t : ℝ, 0 < t → _root_.GD.N0155.d006224 t = _root_.GD.N0155.d006255 t := by
  intro t ht
  by_cases h1 : t = 1
  · subst h1; rw [_root_.GD.N0155.d006226, _root_.GD.N0155.d006261]
  · rw [_root_.GD.N0155.d006228 h1, ← _root_.GD.N0155.d006259 ht h1]


theorem d006266 : ∀ t : ℝ, 0 < t → _root_.GD.N0155.d006223 t = _root_.GD.N0155.d006256 t := by
  intro t ht
  by_cases h1 : t = 1
  · subst h1; rw [_root_.GD.N0155.d006225, _root_.GD.N0155.d006262]
  · rw [_root_.GD.N0155.d006227 h1, ← _root_.GD.N0155.d006260 ht h1]

end GD.N0155
