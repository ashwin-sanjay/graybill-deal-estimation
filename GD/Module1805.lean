import GD.Module1804
import GD.Module1458

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0073
noncomputable section

open _root_.GD.N0038

variable {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]



theorem d029992 (hk : 2 ≤ k) (P : Measure Ω) (μ : ℝ)
    (e : Fin k → Fin k → Ω → ℝ) (he : ∀ i j, Measurable (e i j))
    (hsym : ∀ i j z, e i j z = e j i z)
    (A : Fin k → Fin k → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hcap : ∀ i j, i ≠ j → _root_.GD.N0038.d007554 P μ (e i j) ≤ ENNReal.ofReal (A i j))
    (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    _root_.GD.N0038.d007554 P μ (_root_.GD.N0038.d007546 hk e) ≤
      ENNReal.ofReal (∑ i, w i * (∑ j ∈ Finset.univ.erase i, A i j)) := by
  let T : Fin k → ℝ := fun i => ∑ j ∈ Finset.univ.erase i, A i j
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (_root_.GD.N0038.d007536 hk) T
  have hmin (j : Fin k) : T i ≤ T j := by
    rw [← hi]
    exact Finset.inf'_le T (Finset.mem_univ j)
  have hR : _root_.GD.N0038.d007554 P μ (_root_.GD.N0038.d007546 hk e) ≤ ENNReal.ofReal (T i) := by
    apply (_root_.GD.N0038.d007555 hk P μ e he hsym i).trans
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (A i j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hcap i j (Ne.symm (Finset.mem_erase.mp hj).1)
      _ = _ := by rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hA i j)]
  apply hR.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    T i = ∑ j, w j * T i := by rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ ∑ j, w j * T j := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hmin j) (hw j)



theorem d029993 (hk : 2 ≤ k) (P : Measure Ω) (μ : ℝ)
    (e : Fin k → Fin k → Ω → ℝ) (he : ∀ i j, Measurable (e i j))
    (hsym : ∀ i j z, e i j z = e j i z)
    (q : Fin k → ℝ) (hq : ∀ i, 0 < q i) {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ i j, i ≠ j → _root_.GD.N0038.d007554 P μ (e i j) ≤
      ENNReal.ofReal (C * (q i + q j)⁻¹)) :
    _root_.GD.N0038.d007554 P μ (_root_.GD.N0038.d007546 hk e) ≤
      ENNReal.ofReal ((k.choose 2 : ℝ) * C * (∑ i, q i)⁻¹) := by
  have hQ : 0 < ∑ i, q i := Finset.sum_pos (fun i _ => hq i) (_root_.GD.N0038.d007536 hk)
  have hsum : (∑ i, q i / (∑ j, q j)) = 1 := by
    rw [← Finset.sum_div, div_self hQ.ne']
  have h := _root_.GD.N0073.d029992 hk P μ e he hsym
    (fun i j => C * (q i + q j)⁻¹)
    (fun i j => mul_nonneg hC (inv_pos.mpr (add_pos (hq i) (hq j))).le) hcap
    (fun i => q i / (∑ j, q j)) (fun i => (div_pos (hq i) hQ).le) hsum
  simpa only [_root_.GD.N0073.d029991 q hq C] using h

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0068


theorem d029994 (hk : 2 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (d : ∀ i j, _root_.GD.N0232.N0720.N1080.d014170 (sizes i) (sizes j) → ℝ)
    (hd : ∀ i j, Measurable (d i j)) (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ i j, i ≠ j → ∀ θ,
      _root_.GD.N0232.N0720.N1080.d014197 (sizes i) (sizes j) θ (d i j) ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 (sizes i) (sizes j) θ)) :
    Measurable (_root_.GD.N0068.d023034 hk sizes d) ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0068.d023034 hk sizes d) ≤
        ENNReal.ofReal ((k.choose 2 : ℝ) * C * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) := by
  have he := _root_.GD.N0068.d023032 sizes d hd
  refine ⟨_root_.GD.N0038.d007547 hk _ he, ?_⟩
  intro θ
  have hb (i j : Fin k) (hij : i ≠ j) :
      _root_.GD.N0038.d007554 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location (_root_.GD.N0068.d023031 sizes d i j) ≤
        ENNReal.ofReal (C * ((_root_.GD.N0068.d023027 sizes θ i)⁻¹ + (_root_.GD.N0068.d023027 sizes θ j)⁻¹)⁻¹) := by
    change _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0068.d023031 sizes d i j) ≤ _
    unfold _root_.GD.N0068.d023031
    split_ifs
    · rw [_root_.GD.N0068.d023026 sizes i j hij (d i j) (hd i j)]
      simpa only [_root_.GD.N0232.N0720.N1257.d015508,
        _root_.GD.N0068.d023020, _root_.GD.N0068.d023027, one_div, inv_div] using hcap i j hij (_root_.GD.N0068.d023020 θ i j)
    · rw [_root_.GD.N0068.d023026 sizes j i hij.symm (d j i) (hd j i)]
      simpa only [_root_.GD.N0232.N0720.N1257.d015508,
        _root_.GD.N0068.d023020, _root_.GD.N0068.d023027, one_div, inv_div, add_comm] using hcap j i hij.symm (_root_.GD.N0068.d023020 θ j i)
  simpa only [_root_.GD.N0068.d023034, _root_.GD.N0068.d023030, _root_.GD.N0038.d007554, _root_.GD.N0232.N0719.N0859.d010840] using
    _root_.GD.N0073.d029993 hk (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) θ.location (_root_.GD.N0068.d023031 sizes d) he
      (_root_.GD.N0068.d023033 sizes d) (fun i => (_root_.GD.N0068.d023027 sizes θ i)⁻¹)
      (fun i => inv_pos.mpr (_root_.GD.N0068.d023028 sizes hn θ i)) hC hb

theorem d029995 (hk : 2 ≤ k) (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i)
    (d : ∀ i j, _root_.GD.N0232.N0720.N1080.d014170 (sizes i) (sizes j) → ℝ)
    (hd : ∀ i j, Measurable (d i j)) (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ i j, i ≠ j → ∀ θ,
      _root_.GD.N0232.N0720.N1080.d014197 (sizes i) (sizes j) θ (d i j) ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 (sizes i) (sizes j) θ)) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≤ ENNReal.ofReal ((k.choose 2 : ℝ) * C) := by
  obtain ⟨hd', hb⟩ := _root_.GD.N0073.d029994 hk sizes hn d hd C hC hcap
  apply (_root_.GD.N0230.N0611.d003520
    (_root_.GD.N0232.N0719.N0962.d012186 k sizes) hd').trans
  apply iSup_le
  intro θ
  exact (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega) (fun i => by have := hn i; omega)
    _ (by positivity) θ _).mpr (hb θ)

theorem d029996 (hk : 2 ≤ k) (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (C : ℝ) (hC : 0 ≤ C)
    (hpair : ∀ i j, i ≠ j →
      _root_.GD.N0232.N0720.N1256.d015549 (sizes i) (sizes j) ≤ ENNReal.ofReal C) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≤ ENNReal.ofReal ((k.choose 2 : ℝ) * C) := by
  classical
  have hex := fun i j => _root_.GD.N0232.N0720.N1222.d015570
    (sizes i) (sizes j) (hn i) (hn j)
  choose d hd hv using hex
  apply _root_.GD.N0073.d029995 hk sizes hn d (fun i j => (hd i j).1.1) C hC
  intro i j hij θ
  apply (_root_.GD.N0232.N0720.N1256.d015553
    (sizes i) (sizes j) (by have := hn i; omega) C hC θ (d i j)).mp
  have hupper : _root_.GD.N0232.N0720.N1256.d015548
      (sizes i) (sizes j) (d i j) ≤ ENNReal.ofReal C :=
    (hv i j).le.trans (hpair i j hij)
  exact (le_iSup (fun θ => _root_.GD.N0232.N0720.N1256.d015547
    (sizes i) (sizes j) θ (d i j)) θ).trans hupper



theorem d029997 (hk : 2 ≤ k) (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≤ (k.choose 2 : ℝ≥0∞) * _root_.GD.N0068.d023038 sizes := by
  by_cases htop : _root_.GD.N0068.d023038 sizes = ⊤
  · rw [htop, ENNReal.mul_top (Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne')]
    exact le_top
  let C := (_root_.GD.N0068.d023038 sizes).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hval : ENNReal.ofReal C = _root_.GD.N0068.d023038 sizes := ENNReal.ofReal_toReal htop
  have hbound := _root_.GD.N0073.d029996 hk sizes hn C hC (fun i j hij => by
    rw [hval]
    exact _root_.GD.N0068.d023039 sizes i j hij)
  have heq : ENNReal.ofReal ((k.choose 2 : ℝ) * C) = (k.choose 2 : ℝ≥0∞) * _root_.GD.N0068.d023038 sizes := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, hval]
  exact heq ▸ hbound

theorem d029998 (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 2 sizes = _root_.GD.N0068.d023038 sizes := by
  apply le_antisymm
  · simpa using _root_.GD.N0073.d029997 (by decide) sizes hn
  · exact _root_.GD.N0068.d023040 sizes hn

end
end GD.N0073

#print axioms _root_.GD.N0073.d029992
#print axioms _root_.GD.N0073.d029993
#print axioms _root_.GD.N0073.d029994
#print axioms _root_.GD.N0073.d029996
#print axioms _root_.GD.N0073.d029997
#print axioms _root_.GD.N0073.d029998
