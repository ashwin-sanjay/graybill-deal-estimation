import GD.Module1849

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0022.N0255

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0034.N0289
open _root_.GD.N0046.N0305
open _root_.GD.N0024 _root_.GD.N0024.N0274
open _root_.GD.N0230.N0611
open _root_.GD.N0022.N0256

local instance : DecidableEq _root_.GD.N0232.N0720.N1080.d014168 := Classical.decEq _

theorem d030392 (b v e : ℝ) (he : 0 ≤ e) :
    min b (v + e) ≤ min b v + e := by
  rcases le_total b v with h | h
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right h]
    exact min_le_right _ _


def d030393 (m n : ℕ) : Set (_root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :=
  {f | Measurable f ∧ ∀ θ,
    _root_.GD.N0232.N0720.N1080.d014197 m n θ f ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)}

def d030394 (m n : ℕ) : ℝ≥0∞ :=
  _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0022.N0255.d030393 m n)



theorem d030395
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v)
    (hempty : _root_.GD.N0046.N0305.d030202 m n hm hn = ∅) :
    ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (ε : ℝ), 0 < ε ∧
      ∀ f ∈ _root_.GD.N0022.N0255.d030393 m n,
        ∃ θ ∈ insert _root_.GD.N0232.N0720.N1080.d014169 F,
          ENNReal.ofReal (v + ε) < _root_.GD.N0232.N0720.N1256.d015547 m n θ f := by
  obtain ⟨F, ε, hε, hF⟩ :=
    _root_.GD.N0022.N0256.d030390 m n hm hn hempty
  refine ⟨F, ε, hε, fun f hf => ?_⟩
  obtain ⟨θ, hθ, hbad⟩ := hF f hf.1
  refine ⟨θ, hθ, ?_⟩
  by_contra hnot
  have hncap := (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) (v + ε)
    (add_nonneg hv hε.le) θ f).mp (not_lt.mp hnot)
  have hbase : _root_.GD.N0232.N0720.N1080.d014197 m n θ f ≤ ENNReal.ofReal (_root_.GD.N0024.N0274.d030341 m n hm hn θ) := by
    rw [_root_.GD.N0024.N0274.d030342]
    simpa only [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn] using hf.2 θ
  have hmin := le_min hbase hncap
  rw [← ENNReal.ofReal_min] at hmin
  have hrelax : min (_root_.GD.N0024.N0274.d030341 m n hm hn θ) ((v + ε) * _root_.GD.N0232.N0720.N1257.d015508 m n θ) ≤
      _root_.GD.N0034.N0289.d030220 m n hm hn θ + ε * _root_.GD.N0232.N0720.N1257.d015508 m n θ := by
    rw [_root_.GD.N0024.N0274.d030343 m n hm hn v hv hvalue, add_mul]
    exact _root_.GD.N0022.N0255.d030392 _ _ _ (mul_nonneg hε.le (_root_.GD.N0232.N0720.N1257.d015509 m n θ))
  exact (not_le.mpr hbad) (hmin.trans (ENNReal.ofReal_le_ofReal hrelax))

theorem d030396
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hfinite : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤)
    (hempty : _root_.GD.N0046.N0305.d030202 m n hm hn = ∅) :
    _root_.GD.N0232.N0720.N1256.d015549 m n < _root_.GD.N0022.N0255.d030394 m n := by
  let v := (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v :=
    (ENNReal.ofReal_toReal hfinite).symm
  obtain ⟨F, ε, hε, hF⟩ :=
    _root_.GD.N0022.N0255.d030395 m n hm hn v hv hvalue hempty
  have hbound : ENNReal.ofReal (v + ε) ≤ _root_.GD.N0022.N0255.d030394 m n := by
    apply le_iInf
    intro f
    apply le_iInf
    intro hf
    obtain ⟨θ, _, hθ⟩ := hF f hf
    exact hθ.le.trans (le_iSup (fun θ => _root_.GD.N0232.N0720.N1256.d015547 m n θ f) θ)
  rw [hvalue]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < v + ε)).mpr
    (by linarith) |>.trans_le hbound

theorem d030397
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hempty : _root_.GD.N0046.N0305.d030202 m n hm hn = ∅) : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤ := by
  intro htop
  have hCE := _root_.GD.N0024.N0283.d030367 m n hm hn htop
  have hK := (_root_.GD.N0024.N0283.d030366 m n hm hn).mp hCE
  rw [hempty] at hK
  exact Set.not_nonempty_empty hK

theorem d030398
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ ↔ _root_.GD.N0232.N0720.N1256.d015549 m n < _root_.GD.N0022.N0255.d030394 m n := by
  constructor
  · intro hempty
    exact _root_.GD.N0022.N0255.d030396 m n hm hn
      (_root_.GD.N0022.N0255.d030397 m n hm hn hempty) hempty
  · intro hlt
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨p, hp⟩
    have hraw := _root_.GD.N0034.N0294.d030322 m n hm hn hp
    have hbase : _root_.GD.N0232.N0720.N1214.d014265 m n p ∈ _root_.GD.N0022.N0255.d030393 m n :=
      ⟨hraw.1, fun θ => (hraw.2 θ).2⟩
    have hbound : _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1214.d014265 m n p) ≤
        _root_.GD.N0232.N0720.N1256.d015549 m n := by
      apply iSup_le
      intro θ
      unfold _root_.GD.N0232.N0720.N1256.d015547
      apply (ENNReal.div_le_iff
        (ne_of_gt (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0720.N1257.d015510 m n (by omega) θ)))
        ENNReal.ofReal_ne_top).mpr
      exact (hraw.2 θ).1
    exact (not_le.mpr hlt)
      ((_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 m n) hbase).trans hbound)

theorem d030399 :
    _root_.GD.N0232.N0720.N1256.d015549 6 6 < _root_.GD.N0022.N0255.d030394 6 6 :=
  _root_.GD.N0022.N0255.d030396 6 6 (by norm_num) (by norm_num)
    _root_.GD.N0024.N0279.d023585 _root_.GD.N0024.N0268.d030374

theorem d030400 (m n : ℕ) :
    _root_.GD.N0232.N0720.N1080.d014175 m n ∈ _root_.GD.N0022.N0255.d030393 m n :=
  ⟨_root_.GD.N0117.d014146 m n, fun _ => le_rfl⟩

theorem d030401 :
    _root_.GD.N0022.N0255.d030394 6 6 ≤ ENNReal.ofReal (289 / 3) :=
  (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 6 6)
    (_root_.GD.N0022.N0255.d030400 6 6)).trans
      _root_.GD.N0024.N0279.d023583

theorem d030402 : _root_.GD.N0022.N0255.d030394 6 6 ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top _root_.GD.N0022.N0255.d030401

theorem d030403 :
    0 < (_root_.GD.N0022.N0255.d030394 6 6).toReal - (_root_.GD.N0232.N0720.N1256.d015549 6 6).toReal := by
  apply sub_pos.mpr
  exact (ENNReal.toReal_lt_toReal _root_.GD.N0024.N0279.d023585
    _root_.GD.N0022.N0255.d030402).mpr _root_.GD.N0022.N0255.d030399



theorem d030404 :
    ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (ε : ℝ), 0 < ε ∧
      ∀ f ∈ _root_.GD.N0022.N0255.d030393 6 6,
        ∃ θ ∈ insert _root_.GD.N0232.N0720.N1080.d014169 F,
          ENNReal.ofReal ((_root_.GD.N0232.N0720.N1256.d015549 6 6).toReal + ε) < _root_.GD.N0232.N0720.N1256.d015547 6 6 θ f :=
  _root_.GD.N0022.N0255.d030395 6 6 (by norm_num) (by norm_num)
    _ ENNReal.toReal_nonneg
    (ENNReal.ofReal_toReal _root_.GD.N0024.N0279.d023585).symm
    _root_.GD.N0024.N0268.d030374

end
end GD.N0022.N0255

#print axioms _root_.GD.N0022.N0255.d030392
#print axioms _root_.GD.N0022.N0255.d030395
#print axioms _root_.GD.N0022.N0255.d030396
#print axioms _root_.GD.N0022.N0255.d030397
#print axioms _root_.GD.N0022.N0255.d030398
#print axioms _root_.GD.N0022.N0255.d030399
#print axioms _root_.GD.N0022.N0255.d030400
#print axioms _root_.GD.N0022.N0255.d030401
#print axioms _root_.GD.N0022.N0255.d030402
#print axioms _root_.GD.N0022.N0255.d030403
#print axioms _root_.GD.N0022.N0255.d030404
