import GD.Module1391
import GD.Module1380
import GD.Module0476
import GD.Module0474















set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators Interval

namespace GD.N0177
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0178 _root_.GD.N0180 _root_.GD.N0163
open _root_.GD.N0181 _root_.GD.N0167 _root_.GD.N0171
open _root_.GD.N0193 _root_.GD.N0166 _root_.GD.N0182
open _root_.GD.N0174


def d022413 {N : ℕ} (hN : 2 ≤ N) (i : Fin (_root_.GD.N0193.d007343 N)) : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨_root_.GD.N0193.d007346 N i, _root_.GD.N0193.d007358 hN i, _root_.GD.N0193.d007359 hN i⟩


def d022414 {N : ℕ} (hN : 2 ≤ N) (i : _root_.GD.N0193.d007344 N) : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨_root_.GD.N0193.d007347 N i, _root_.GD.N0193.d007363 hN i⟩

theorem d022415 {N : ℕ} (hN : 2 ≤ N) (i : Fin (_root_.GD.N0193.d007343 N)) :
    _root_.GD.N0177.d022414 hN (i, 0) = _root_.GD.N0177.d022413 hN i := by
  apply Subtype.ext
  rfl

theorem d022416 {N : ℕ} (hN : 2 ≤ N) (i : Fin (_root_.GD.N0193.d007343 N)) :
    _root_.GD.N0177.d022414 hN (i, 1) = _root_.GD.N0182.d022216 (_root_.GD.N0177.d022413 hN i) := by
  apply Subtype.ext
  simp only [_root_.GD.N0177.d022414, _root_.GD.N0193.d007347, _root_.GD.N0177.d022413, _root_.GD.N0182.d022216]
  norm_num


theorem d022417 {N : ℕ} (hN : 2 ≤ N)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    _root_.GD.N0163.d022185 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN) g =
      _root_.GD.N0193.d007348 N * ∑ i : Fin (_root_.GD.N0193.d007343 N), _root_.GD.N0182.d022221 (_root_.GD.N0177.d022413 hN i) g := by
  classical
  rw [_root_.GD.N0163.d022185, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two, _root_.GD.N0177.d022415, _root_.GD.N0177.d022416, _root_.GD.N0182.d022221]
  ring


theorem d022418 {N : ℕ} (hN : 2 ≤ N) :
    _root_.GD.N0178.d007132 (_root_.GD.N0181.d007268 N) (_root_.GD.N0181.d007269 N) = _root_.GD.N0171.d007331 N := by
  unfold _root_.GD.N0178.d007132 _root_.GD.N0171.d007331
  rw [_root_.GD.N0178.d007137 (_root_.GD.N0171.d007334 hN)]

theorem d022419 {N : ℕ} (hN : 2 ≤ N) :
    2 * _root_.GD.N0178.d007132 (_root_.GD.N0181.d007268 N) (_root_.GD.N0181.d007269 N) * ((_root_.GD.N0181.d007268 N)⁻¹ - 1) / (1 - _root_.GD.N0181.d007269 N) = _root_.GD.N0171.d007332 N := by
  rw [_root_.GD.N0177.d022418 hN]
  simp only [_root_.GD.N0171.d007332, one_div]


theorem d022420 {r : ℝ} (hr : 0 < r)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    (∫ p, _root_.GD.N0174.d022396 g r p ∂_root_.GD.N0232.N0720.N1436.d013288) =
      _root_.GD.N0182.d022221 (_root_.GD.N0174.d022394 r hr) (_root_.GD.N0163.d022211 g) := by
  rw [_root_.GD.N0174.d022401 hr g hg h01]
  rfl

private theorem d022421 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0167.d007305 N :=
  (show (0 : ℝ) < (N : ℝ) by exact_mod_cast (show 0 < N by omega)).trans_le
    (_root_.GD.N0167.d007314 hN)


theorem d022422 {N : ℕ} (hN : 2 ≤ N) (i : Fin (_root_.GD.N0193.d007343 N))
    {r : ℝ}
    (hr : r ∈ Icc ((_root_.GD.N0193.d007345 N i : ℝ) * _root_.GD.N0167.d007304 N)
      (((_root_.GD.N0193.d007345 N i + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N))
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0171.d007331 N * (∫ p, _root_.GD.N0174.d022396 g r p ∂_root_.GD.N0232.N0720.N1436.d013288) - 2 * _root_.GD.N0171.d007332 N ≤
      _root_.GD.N0182.d022221 (_root_.GD.N0177.d022413 hN i) (_root_.GD.N0163.d022211 g) := by
  have hi := _root_.GD.N0193.d007355 hN i
  have hr0 : 0 < r := (_root_.GD.N0177.d022421 hN).trans_le
    (_root_.GD.N0166.d007384 hN hi hr).1
  have hb := _root_.GD.N0166.d007382 hN hi.1 hr
  have hd : _root_.GD.N0181.d007269 N < 1 := (_root_.GD.N0181.d007282 hN).trans (by norm_num)
  have hp := _root_.GD.N0182.d022223 (_root_.GD.N0174.d022394 r hr0)
    (_root_.GD.N0177.d022413 hN i) (_root_.GD.N0181.d007276 hN) hb.1 hb.2.1 hb.2.2 hd g hg h01
  rw [_root_.GD.N0177.d022419 hN, _root_.GD.N0177.d022418 hN,
    ← _root_.GD.N0177.d022420 hr0 g hg h01] at hp
  exact hp


theorem d022423 {N : ℕ} (hN : 2 ≤ N)
    (i : Fin (_root_.GD.N0193.d007343 N)) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0171.d007331 N * (∫ r in ((_root_.GD.N0193.d007345 N i : ℝ) * _root_.GD.N0167.d007304 N)..
      (((_root_.GD.N0193.d007345 N i + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N),
        ∫ p, _root_.GD.N0174.d022396 g r p ∂_root_.GD.N0232.N0720.N1436.d013288) ≤
      _root_.GD.N0167.d007304 N * (_root_.GD.N0182.d022221 (_root_.GD.N0177.d022413 hN i) (_root_.GD.N0163.d022211 g) + 2 * _root_.GD.N0171.d007332 N) := by
  have hf := _root_.GD.N0174.d022409 (_root_.GD.N0177.d022421 hN)
    (show _root_.GD.N0167.d007305 N ≤ _root_.GD.N0167.d007305 N + _root_.GD.N0167.d007306 N by linarith [_root_.GD.N0167.d007318 hN]) g hg h01
  have hfi := _root_.GD.N0166.d007385 hN (_root_.GD.N0193.d007355 hN i) _ hf
  have hm := intervalIntegral.integral_mono_on (_root_.GD.N0166.d007383 hN (_root_.GD.N0193.d007345 N i))
    (hfi.const_mul (_root_.GD.N0171.d007331 N))
    (intervalIntegrable_const (c :=
      _root_.GD.N0182.d022221 (_root_.GD.N0177.d022413 hN i) (_root_.GD.N0163.d022211 g) + 2 * _root_.GD.N0171.d007332 N))
    (fun r hr => by linarith [_root_.GD.N0177.d022422 hN i hr g hg h01])
  simpa only [intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    smul_eq_mul, _root_.GD.N0166.d007389] using hm


theorem d022424 {N : ℕ} (hN : 2 ≤ N)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0171.d007331 N * _root_.GD.N0174.d022397 (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007306 N) g - _root_.GD.N0171.d007332 N ≤
      _root_.GD.N0193.d007348 N * ∑ i : Fin (_root_.GD.N0193.d007343 N),
        _root_.GD.N0182.d022221 (_root_.GD.N0177.d022413 hN i) (_root_.GD.N0163.d022211 g) := by
  classical
  let F : ℝ → ℝ := fun r => ∫ p, _root_.GD.N0174.d022396 g r p ∂_root_.GD.N0232.N0720.N1436.d013288
  have hf : IntervalIntegrable F volume (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007305 N + _root_.GD.N0167.d007306 N) :=
    _root_.GD.N0174.d022409 (_root_.GD.N0177.d022421 hN)
      (by linarith [_root_.GD.N0167.d007318 hN]) g hg h01
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (_root_.GD.N0193.d007343 N))))
    (fun i _ => _root_.GD.N0177.d022423 hN i g hg h01)
  change (∑ i : Fin (_root_.GD.N0193.d007343 N), _root_.GD.N0171.d007331 N *
      (∫ r in ((_root_.GD.N0193.d007345 N i : ℝ) * _root_.GD.N0167.d007304 N)..
        (((_root_.GD.N0193.d007345 N i + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N), F r)) ≤
    ∑ i : Fin (_root_.GD.N0193.d007343 N), _root_.GD.N0167.d007304 N *
      (_root_.GD.N0182.d022221 (_root_.GD.N0177.d022413 hN i) (_root_.GD.N0163.d022211 g) + 2 * _root_.GD.N0171.d007332 N) at hs
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [_root_.GD.N0166.d007388 hN F hf] at hs
  have hscaled := mul_le_mul_of_nonneg_left hs
    (one_div_nonneg.mpr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (_root_.GD.N0167.d007318 hN).le))
  have hh : _root_.GD.N0167.d007304 N ≠ 0 := (_root_.GD.N0167.d007313 hN).ne'
  have hk : (_root_.GD.N0193.d007343 N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (_root_.GD.N0193.d007353 hN).ne'
  have hright : 1 / (2 * _root_.GD.N0167.d007306 N) *
      (_root_.GD.N0167.d007304 N * ((∑ i : Fin (_root_.GD.N0193.d007343 N), _root_.GD.N0182.d022221 (_root_.GD.N0177.d022413 hN i) (_root_.GD.N0163.d022211 g)) +
        (_root_.GD.N0193.d007343 N : ℝ) * (2 * _root_.GD.N0171.d007332 N))) =
      _root_.GD.N0193.d007348 N * (∑ i : Fin (_root_.GD.N0193.d007343 N), _root_.GD.N0182.d022221 (_root_.GD.N0177.d022413 hN i) (_root_.GD.N0163.d022211 g)) +
        _root_.GD.N0171.d007332 N := by
    rw [_root_.GD.N0166.d007390, _root_.GD.N0193.d007348]
    field_simp [hk, hh] <;> ring
  rw [hright] at hscaled
  have hleft : 1 / (2 * _root_.GD.N0167.d007306 N) * (_root_.GD.N0171.d007331 N * ∫ r in (_root_.GD.N0167.d007305 N)..(_root_.GD.N0167.d007305 N + _root_.GD.N0167.d007306 N), F r) =
      _root_.GD.N0171.d007331 N * _root_.GD.N0174.d022397 (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007306 N) g := by
    unfold _root_.GD.N0174.d022397 F
    ring
  rw [hleft] at hscaled
  linarith


theorem d022425 {N : ℕ} (hN : 2 ≤ N)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0171.d007331 N * _root_.GD.N0174.d022397 (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007306 N) g - _root_.GD.N0171.d007332 N ≤
      _root_.GD.N0163.d022185 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN)
        (_root_.GD.N0163.d022211 g) := by
  rw [_root_.GD.N0177.d022417]
  exact _root_.GD.N0177.d022424 hN g hg h01

end
end GD.N0177

#print axioms _root_.GD.N0177.d022415
#print axioms _root_.GD.N0177.d022416
#print axioms _root_.GD.N0177.d022417
#print axioms _root_.GD.N0177.d022418
#print axioms _root_.GD.N0177.d022419
#print axioms _root_.GD.N0177.d022420
#print axioms _root_.GD.N0177.d022422
#print axioms _root_.GD.N0177.d022423
#print axioms _root_.GD.N0177.d022424
#print axioms _root_.GD.N0177.d022425
