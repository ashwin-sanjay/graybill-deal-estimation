import GD.Module1186
import GD.Module0983

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal BigOperators

namespace GD.N0213.N0512

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1043
open _root_.GD.N0232.N0720.N1042
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1226
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608

def d022937 (n : ℕ) (hn : 2 ≤ n) : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n) :=
  (2 : ℝ)⁻¹ • (_root_.GD.N0232.N0720.N1080.d014181 n n hn hn + _root_.GD.N0232.N0720.N1043.d019067 n (_root_.GD.N0232.N0720.N1080.d014181 n n hn hn))

theorem d022938 (n : ℕ) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1043.d019067 n (_root_.GD.N0213.N0512.d022937 n hn) = _root_.GD.N0213.N0512.d022937 n hn := by
  simp only [_root_.GD.N0213.N0512.d022937, _root_.GD.N0232.N0720.N1043.d019070, _root_.GD.N0232.N0720.N1043.d019069,
    _root_.GD.N0232.N0720.N1043.d019068, add_comm]

theorem d022939 (n : ℕ) (hn : 2 ≤ n) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 n n) (_root_.GD.N0213.N0512.d022937 n hn)
      (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn) := by
  intro θ
  have hd := _root_.GD.N0232.N0720.N1080.d014186 n n hn hn θ
  have hs : _root_.GD.N0232.N0720.N1080.d014182 n n θ (_root_.GD.N0232.N0720.N1043.d019067 n (_root_.GD.N0232.N0720.N1080.d014181 n n hn hn)) <
      _root_.GD.N0232.N0720.N1080.d014182 n n θ (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn) := by
    rw [_root_.GD.N0232.N0720.N1043.d019072]
    exact (_root_.GD.N0232.N0720.N1080.d014186 n n hn hn (_root_.GD.N0232.N0720.N1043.d019058 θ)).trans_eq
      (_root_.GD.N0232.N0720.N1043.d019080 n hn θ)
  have havg := _root_.GD.N0232.N0720.N1506.d019013 n n
    (G := Fin 2) θ ![_root_.GD.N0232.N0720.N1080.d014181 n n hn hn, _root_.GD.N0232.N0720.N1043.d019067 n (_root_.GD.N0232.N0720.N1080.d014181 n n hn hn)]
  simp only [Fintype.card_fin, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Nat.cast_ofNat] at havg
  apply havg.trans_lt
  have hmul := ENNReal.mul_lt_mul_left
    (ENNReal.inv_ne_zero.mpr (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
    (ENNReal.inv_ne_top.mpr (by norm_num : (2 : ℝ≥0∞) ≠ 0))
    (ENNReal.add_lt_add hd hs)
  rw [mul_comm] at hmul
  convert hmul using 1
  rw [← mul_two]
  exact (ENNReal.mul_inv_cancel_right
    (a := _root_.GD.N0232.N0720.N1080.d014182 n n θ (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn)) (b := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num)).symm

def d022940 (n : ℕ) (hn : 2 ≤ n) : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n) :=
  _root_.GD.N0232.N0720.N1159.d014633 n n (_root_.GD.N0213.N0512.d022937 n hn)

theorem d022941 (n : ℕ) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1043.d019067 n (_root_.GD.N0213.N0512.d022940 n hn) = _root_.GD.N0213.N0512.d022940 n hn :=
  _root_.GD.N0232.N0720.N1042.d019085 n
    (_root_.GD.N0213.N0512.d022937 n hn) (_root_.GD.N0213.N0512.d022938 n hn)

theorem d022942 (n : ℕ) (hn : 2 ≤ n) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 n n) (_root_.GD.N0213.N0512.d022940 n hn)
      (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn) :=
  _root_.GD.N0232.N0720.N1159.d014636 n n
    (_root_.GD.N0213.N0512.d022937 n hn) (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn) (_root_.GD.N0213.N0512.d022939 n hn)

theorem d022943 (n : ℕ) (hn : 2 ≤ n) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 n n) (_root_.GD.N0213.N0512.d022940 n hn) :=
  (_root_.GD.N0232.N0720.N1159.d014634 n n (_root_.GD.N0213.N0512.d022937 n hn)).2.1

def d022944 (n : ℕ) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n))
    (ω : _root_.GD.N0232.N0720.N1080.d014170 n n) : ℝ :=
  (_root_.GD.N0232.N0720.N1214.d014265 n n p ω + _root_.GD.N0232.N0720.N1214.d014265 n n p (_root_.GD.N0232.N0720.N1043.d019054 n ω)) / 2

theorem d022945 (n : ℕ) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n)) :
    Measurable (_root_.GD.N0213.N0512.d022944 n p) :=
  ((_root_.GD.N0232.N0720.N1214.d014266 n n p).add
    ((_root_.GD.N0232.N0720.N1214.d014266 n n p).comp (_root_.GD.N0232.N0720.N1043.d019056 n))).div_const 2

theorem d022946 (n : ℕ) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n))
    (ω : _root_.GD.N0232.N0720.N1080.d014170 n n) :
    _root_.GD.N0213.N0512.d022944 n p (_root_.GD.N0232.N0720.N1043.d019054 n ω) = _root_.GD.N0213.N0512.d022944 n p ω := by
  simp only [_root_.GD.N0213.N0512.d022944, _root_.GD.N0232.N0720.N1043.d019055, add_comm]

theorem d022947 (n : ℕ) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n))
    (hp : _root_.GD.N0232.N0720.N1043.d019067 n p = p) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0213.N0512.d022944 n p =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 n n θ] _root_.GD.N0232.N0720.N1214.d014265 n n p := by
  apply (_root_.GD.N0232.N0720.N1080.d014173 n n θ).ae_le
  have hB := _root_.GD.N0232.N0720.N1214.d014267 n n p
  have hcomp := (_root_.GD.N0232.N0720.N1043.d019066 n).quasiMeasurePreserving.ae_eq_comp hB
  have hcoe := Lp.coeFn_compMeasurePreserving p (_root_.GD.N0232.N0720.N1043.d019066 n)
  change (fun ω => _root_.GD.N0232.N0720.N1043.d019067 n p ω) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 n n]
    (fun ω => p (_root_.GD.N0232.N0720.N1043.d019054 n ω)) at hcoe
  rw [hp] at hcoe
  filter_upwards [hB, hcomp, hcoe] with ω hω hsω hcω
  dsimp only [Function.comp_apply] at hsω
  simp only [_root_.GD.N0213.N0512.d022944, hsω, ← hcω, hω]
  ring

def d022948 (n : ℕ) (hn : 2 ≤ n) : _root_.GD.N0232.N0720.N1080.d014170 n n → ℝ :=
  _root_.GD.N0213.N0512.d022944 n (_root_.GD.N0213.N0512.d022940 n hn)

theorem d022949 (n : ℕ) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 n n θ (_root_.GD.N0213.N0512.d022948 n hn) =
      _root_.GD.N0232.N0720.N1080.d014182 n n θ (_root_.GD.N0213.N0512.d022940 n hn) := by
  unfold _root_.GD.N0213.N0512.d022948
  rw [_root_.GD.N0232.N0720.N1159.d014662 n n θ
    (_root_.GD.N0213.N0512.d022947 n (_root_.GD.N0213.N0512.d022940 n hn) (_root_.GD.N0213.N0512.d022941 n hn) θ)]
  exact _root_.GD.N0232.N0720.N1215.d014286 n n θ _

theorem d022950 (n : ℕ) (hn : 2 ≤ n) :
    ∃ d : _root_.GD.N0232.N0720.N1080.d014170 n n → ℝ,
      Measurable d ∧
      (∀ ω, d (_root_.GD.N0232.N0720.N1043.d019054 n ω) = d ω) ∧
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 n n θ d < _root_.GD.N0232.N0720.N1080.d014197 n n θ (_root_.GD.N0232.N0720.N1080.d014175 n n)) ∧
      (∀ e : _root_.GD.N0232.N0720.N1080.d014170 n n → ℝ, Measurable e →
        (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 n n θ e ≤ _root_.GD.N0232.N0720.N1080.d014197 n n θ d) →
        ∀ θ, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 n n θ] d) := by
  refine ⟨_root_.GD.N0213.N0512.d022948 n hn, _root_.GD.N0213.N0512.d022945 n _, _root_.GD.N0213.N0512.d022946 n _, ?_, ?_⟩
  · intro θ
    rw [_root_.GD.N0213.N0512.d022949, _root_.GD.N0232.N0720.N1080.d014199 n n hn hn θ]
    exact _root_.GD.N0213.N0512.d022942 n hn θ
  · intro e he hdom θ
    have hbelow : ∀ η,
        _root_.GD.N0232.N0720.N1080.d014197 n n η e ≤
          _root_.GD.N0232.N0720.N1080.d014197 n n η (_root_.GD.N0232.N0720.N1214.d014265 n n (_root_.GD.N0213.N0512.d022940 n hn)) := by
      intro η
      rw [_root_.GD.N0232.N0720.N1215.d014286]
      simpa only [_root_.GD.N0213.N0512.d022949] using hdom η
    exact (_root_.GD.N0232.N0720.N1226.d015581 n n
      (_root_.GD.N0213.N0512.d022940 n hn) (_root_.GD.N0213.N0512.d022943 n hn) e he hbelow θ).trans
        (_root_.GD.N0213.N0512.d022947 n _ (_root_.GD.N0213.N0512.d022941 n hn) θ).symm

def d022951 (m n : ℕ) (h : m = n) (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) : _root_.GD.N0232.N0720.N1080.d014170 m n := by
  subst n
  exact _root_.GD.N0232.N0720.N1043.d019054 m ω

theorem d022952 (m n : ℕ) (hmn : m ≠ n)
    (σ : Equiv.Perm (Fin 2)) (hσ : (![m, n] : Fin 2 → ℕ) ∘ σ = ![m, n]) :
    σ = Equiv.refl (Fin 2) := by
  have hinj : Function.Injective (![m, n] : Fin 2 → ℕ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  apply Equiv.ext
  intro i
  exact hinj (congrFun hσ i)

theorem d022953 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable d ∧
      (∀ (h : m = n) ω, d (_root_.GD.N0213.N0512.d022951 m n h ω) = d ω) ∧
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d < _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      (∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e →
        (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ d) →
        ∀ θ, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] d) := by
  by_cases h : m = n
  · subst n
    obtain ⟨d, hd, hs, hstrict, ht⟩ := _root_.GD.N0213.N0512.d022950 m hm
    exact ⟨d, hd, fun _ ω => hs ω, hstrict, ht⟩
  · exact ⟨_root_.GD.N0232.N0720.N1080.d014194 m n hm hn,
      _root_.GD.N0232.N0720.N1080.d014195 m n hm hn,
      fun h' _ => (h h').elim,
      _root_.GD.N0232.N0720.N1080.d014201 m n hm hn,
      _root_.GD.N0232.N0720.N1080.d014202 m n hm hn⟩

end
end GD.N0213.N0512

#print axioms _root_.GD.N0213.N0512.d022939
#print axioms _root_.GD.N0213.N0512.d022941
#print axioms _root_.GD.N0213.N0512.d022942
#print axioms _root_.GD.N0213.N0512.d022943
#print axioms _root_.GD.N0213.N0512.d022947
#print axioms _root_.GD.N0213.N0512.d022950
#print axioms _root_.GD.N0213.N0512.d022952
#print axioms _root_.GD.N0213.N0512.d022953
