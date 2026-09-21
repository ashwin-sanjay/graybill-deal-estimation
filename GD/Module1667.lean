import GD.Module1666

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0102.N0422
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0910 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0072 _root_.GD.N0021 _root_.GD.N0033
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0102.N0420 _root_.GD.N0102.N0423

variable {k : ℕ}


def d028281 (v : Fin k → ℝ) : ℝ := ∑ i, (v i)⁻¹


def d028282 (v : Fin k → ℝ) (i : Fin k) : ℝ := (v i)⁻¹ / _root_.GD.N0102.N0422.d028281 v

theorem d028283 (hk : 0 < k) (v : Fin k → ℝ) (hv : ∀ i, 0 < v i) :
    0 < _root_.GD.N0102.N0422.d028281 v :=
  Finset.sum_pos (fun i _ => inv_pos.mpr (hv i))
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hk))

theorem d028284 (hk : 0 < k) (v : Fin k → ℝ) (hv : ∀ i, 0 < v i)
    (i : Fin k) : 0 < _root_.GD.N0102.N0422.d028282 v i :=
  div_pos (inv_pos.mpr (hv i)) (_root_.GD.N0102.N0422.d028283 hk v hv)

theorem d028285 (hk : 0 < k) (v : Fin k → ℝ) (hv : ∀ i, 0 < v i) :
    ∑ i, _root_.GD.N0102.N0422.d028282 v i = 1 := by
  unfold _root_.GD.N0102.N0422.d028282
  rw [← Finset.sum_div]
  exact div_self (_root_.GD.N0102.N0422.d028283 hk v hv).ne'

theorem d028286 (hk : 0 < k) (v : Fin k → ℝ)
    (hv : ∀ i, 0 < v i) (i : Fin k) :
    _root_.GD.N0102.N0422.d028281 v * v i * _root_.GD.N0102.N0422.d028282 v i = 1 := by
  unfold _root_.GD.N0102.N0422.d028282
  field_simp [(_root_.GD.N0102.N0422.d028283 hk v hv).ne', (hv i).ne']

theorem d028287 (v q : Fin k → ℝ) (i : Fin k) :
    _root_.GD.N0102.N0422.d028282 v i / q i = (v i * q i)⁻¹ / _root_.GD.N0102.N0422.d028281 v := by
  simp only [_root_.GD.N0102.N0422.d028282, div_eq_mul_inv, mul_inv_rev]
  ring

theorem d028288 (v q : Fin k → ℝ) :
    _root_.GD.N0102.N0420.d028253 (_root_.GD.N0102.N0422.d028282 v) q =
      _root_.GD.N0102.N0422.d028281 (fun i => v i * q i) / _root_.GD.N0102.N0422.d028281 v := by
  unfold _root_.GD.N0102.N0420.d028253
  simp_rw [_root_.GD.N0102.N0422.d028287]
  rw [← Finset.sum_div]
  rfl

theorem d028289 (hk : 0 < k) (t : Fin k → ℝ)
    (ht : ∀ i, 0 < t i) (i : Fin k) :
    _root_.GD.N0021.d023313 t i = (t i)⁻¹ / _root_.GD.N0102.N0422.d028281 t := by
  have htotal : _root_.GD.N0232.N0719.N0900.d009107 (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)) =
      _root_.GD.N0102.N0422.d028281 t := by
    unfold _root_.GD.N0232.N0719.N0900.d009107 _root_.GD.N0232.N0719.N0900.d009106 _root_.GD.N0102.N0422.d028281
    apply Finset.sum_congr rfl
    intro j _
    exact _root_.GD.N0232.N0719.N0900.d009127 (ht j)
  unfold _root_.GD.N0021.d023313 _root_.GD.N0232.N0719.N0900.d009108
  rw [htotal, if_neg (_root_.GD.N0102.N0422.d028283 hk t ht).ne']
  congr 1
  exact _root_.GD.N0232.N0719.N0900.d009127 (ht i)



theorem d028290 (hk : 0 < k) (v q : Fin k → ℝ)
    (hv : ∀ i, 0 < v i) (hq : ∀ i, 0 < q i) (i : Fin k) :
    _root_.GD.N0021.d023313 (fun j => v j * q j) i =
      (_root_.GD.N0102.N0422.d028282 v i / q i) / _root_.GD.N0102.N0420.d028253 (_root_.GD.N0102.N0422.d028282 v) q := by
  rw [_root_.GD.N0102.N0422.d028289 hk _ (fun j => mul_pos (hv j) (hq j)),
    _root_.GD.N0102.N0422.d028287, _root_.GD.N0102.N0422.d028288]
  exact (div_div_div_cancel_right₀ (_root_.GD.N0102.N0422.d028283 hk v hv).ne' _ _).symm



theorem d028291 (v q : Fin (k + 1) → ℝ)
    (hv : ∀ i, 0 < v i) (hq : ∀ i, 0 < q i) :
    _root_.GD.N0072.d007621 v (_root_.GD.N0021.d023313 (fun i => v i * q i)) * _root_.GD.N0102.N0422.d028281 v =
      _root_.GD.N0102.N0420.d028256 (_root_.GD.N0102.N0422.d028282 v) q := by
  simpa only [_root_.GD.N0072.d007621, mul_comm] using
    _root_.GD.N0102.N0420.d028270 (_root_.GD.N0102.N0422.d028282 v) q v
      (_root_.GD.N0021.d023313 (fun i => v i * q i)) (_root_.GD.N0102.N0422.d028281 v)
      (_root_.GD.N0102.N0422.d028286 (Nat.succ_pos _) v hv)
      (_root_.GD.N0102.N0422.d028290 (Nat.succ_pos _) v q hv hq)

def d028292 (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (i : Fin k) : ℝ := θ.scale i ^ 2 / (sizes i : ℝ)

theorem d028293 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    0 < _root_.GD.N0102.N0422.d028292 sizes θ i :=
  div_pos (sq_pos_of_pos (θ.scale_pos i)) (Nat.cast_pos.mpr (hn i))

theorem d028294 (sizes : Fin k → ℕ)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0963.d012141 k sizes θ = (_root_.GD.N0102.N0422.d028281 (_root_.GD.N0102.N0422.d028292 sizes θ))⁻¹ := by
  simp only [_root_.GD.N0232.N0719.N0963.d012141, _root_.GD.N0232.N0719.N0838.d012097,
    _root_.GD.N0232.N0719.N0838.d012096, _root_.GD.N0102.N0422.d028281,
    _root_.GD.N0102.N0422.d028292, inv_div]

theorem d028295 (sizes : Fin (k + 1) → ℕ)
    (hn : ∀ i, 0 < sizes i) (θ : _root_.GD.N0232.N0719.N0859.d010809 (k + 1))
    (q : Fin (k + 1) → ℝ) (hq : ∀ i, 0 < q i) :
    _root_.GD.N0072.d007621 (_root_.GD.N0102.N0422.d028292 sizes θ)
        (_root_.GD.N0021.d023313 (fun i => _root_.GD.N0102.N0422.d028292 sizes θ i * q i)) /
        _root_.GD.N0232.N0719.N0963.d012141 (k + 1) sizes θ =
      _root_.GD.N0102.N0420.d028256 (_root_.GD.N0102.N0422.d028282 (_root_.GD.N0102.N0422.d028292 sizes θ)) q := by
  rw [_root_.GD.N0102.N0422.d028294, div_eq_mul_inv, inv_inv]
  exact _root_.GD.N0102.N0422.d028291 _ q (_root_.GD.N0102.N0422.d028293 sizes hn θ) hq




theorem d028296
    (sizes : Fin (k + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hscalar : ∀ i, _root_.GD.N0102.N0420.d028262 (_root_.GD.N0102.N0423.d028273 sizes i)) :
    _root_.GD.N0232.N0719.N0962.d012187 (k + 1) sizes (_root_.GD.N0232.N0719.N0900.d009111 (k + 1) sizes) ≤
      ENNReal.ofReal (∑ i, _root_.GD.N0102.N0423.d028273 sizes i) := by
  apply _root_.GD.N0102.N0423.d028280
    sizes (Nat.succ_pos _) hn (∑ i, _root_.GD.N0102.N0423.d028273 sizes i)
  intro θ
  have hn0 : ∀ i, 0 < sizes i := fun i => lt_of_lt_of_le (by decide : 0 < 2) (hn i)
  have hv := _root_.GD.N0102.N0422.d028293 sizes hn0 θ
  have hs := _root_.GD.N0102.N0423.d028275 sizes hn
  have heq : (∫⁻ q, ENNReal.ofReal (_root_.GD.N0072.d007621 (_root_.GD.N0102.N0422.d028292 sizes θ)
      (_root_.GD.N0021.d023313 (fun i => _root_.GD.N0102.N0422.d028292 sizes θ i * q i)) /
      _root_.GD.N0232.N0719.N0963.d012141 (k + 1) sizes θ) ∂_root_.GD.N0102.N0423.d028274 sizes) =
      ∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028256 (_root_.GD.N0102.N0422.d028282 (_root_.GD.N0102.N0422.d028292 sizes θ)) q)
        ∂_root_.GD.N0033.d028239 (_root_.GD.N0102.N0423.d028273 sizes) := by
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0033.d028240 (_root_.GD.N0102.N0423.d028273 sizes) hs] with q hq
    rw [_root_.GD.N0102.N0422.d028295 sizes hn0 θ q hq]
  change (∫⁻ q, ENNReal.ofReal (_root_.GD.N0072.d007621 (_root_.GD.N0102.N0422.d028292 sizes θ)
      (_root_.GD.N0021.d023313 (fun i => _root_.GD.N0102.N0422.d028292 sizes θ i * q i)) /
      _root_.GD.N0232.N0719.N0963.d012141 (k + 1) sizes θ) ∂_root_.GD.N0102.N0423.d028274 sizes) ≤ _
  rw [heq]
  exact _root_.GD.N0102.N0420.d028272 (_root_.GD.N0102.N0423.d028273 sizes)
    (_root_.GD.N0102.N0422.d028282 (_root_.GD.N0102.N0422.d028292 sizes θ)) hs
    (_root_.GD.N0102.N0422.d028284 (Nat.succ_pos _) _ hv)
    (_root_.GD.N0102.N0422.d028285 (Nat.succ_pos _) _ hv) hscalar

theorem d028297
    (hk : 0 < k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hscalar : ∀ i, _root_.GD.N0102.N0420.d028262 (_root_.GD.N0102.N0423.d028273 sizes i)) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≤
      ENNReal.ofReal (∑ i, _root_.GD.N0102.N0423.d028273 sizes i) := by
  cases k with
  | zero => omega
  | succ k => exact _root_.GD.N0102.N0422.d028296 sizes hn hscalar

end
end GD.N0102.N0422

#print axioms _root_.GD.N0102.N0422.d028285
#print axioms _root_.GD.N0102.N0422.d028290
#print axioms _root_.GD.N0102.N0422.d028295
#print axioms _root_.GD.N0102.N0422.d028297
