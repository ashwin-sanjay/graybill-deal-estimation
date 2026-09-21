import GD.Module0695
import GD.Module0229
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Fintype.CardEmbedding























open scoped BigOperators RealInnerProductSpace

namespace GD.N0232.N0719.N0863

noncomputable section

open _root_.GD.N0234.N0736
open _root_.GD.N0232.N0719.N1002

variable {ι E : Type*}
  [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]


def d010234 (x : ι → E) (i j l : ι) : ℝ :=
  ‖x i - x j‖ ^ 2 + ‖x i - x l‖ ^ 2 + ‖x j - x l‖ ^ 2


def d010235 (x : ι → E) : ℝ :=
  ∑ i, ∑ j, ∑ l, _root_.GD.N0232.N0719.N0863.d010234 x i j l


theorem d010236 (x : ι → E) :
    (∑ i : ι, ∑ j : ι, ∑ _l : ι, ‖x i - x j‖ ^ 2) =
      (Fintype.card ι : ℝ) * _root_.GD.N0234.N0736.d003269 x := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    _root_.GD.N0234.N0736.d003269]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]


theorem d010237 (x : ι → E) :
    (∑ i : ι, ∑ _j : ι, ∑ l : ι, ‖x i - x l‖ ^ 2) =
      (Fintype.card ι : ℝ) * _root_.GD.N0234.N0736.d003269 x := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    _root_.GD.N0234.N0736.d003269]
  rw [← Finset.mul_sum]


theorem d010238 (x : ι → E) :
    (∑ _i : ι, ∑ j : ι, ∑ l : ι, ‖x j - x l‖ ^ 2) =
      (Fintype.card ι : ℝ) * _root_.GD.N0234.N0736.d003269 x := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    _root_.GD.N0234.N0736.d003269]



theorem d010239 (x : ι → E) :
    _root_.GD.N0232.N0719.N0863.d010235 x =
      3 * (Fintype.card ι : ℝ) * _root_.GD.N0234.N0736.d003269 x := by
  rw [_root_.GD.N0232.N0719.N0863.d010235]
  simp only [_root_.GD.N0232.N0719.N0863.d010234, Finset.sum_add_distrib]
  rw [_root_.GD.N0232.N0719.N0863.d010236, _root_.GD.N0232.N0719.N0863.d010237,
    _root_.GD.N0232.N0719.N0863.d010238]
  ring



theorem d010240 (x : ι → E) :
    _root_.GD.N0232.N0719.N0863.d010235 x =
      6 * (Fintype.card ι : ℝ) ^ 2 * _root_.GD.N0234.N0736.d003268 x := by
  rw [_root_.GD.N0232.N0719.N0863.d010239,
    ← _root_.GD.N0234.N0736.d003281]
  ring



theorem d010241
    (x : ι → E) :
    ((Fintype.card ι : ℝ) ^ 3)⁻¹ * _root_.GD.N0232.N0719.N0863.d010235 x =
      (6 / (Fintype.card ι : ℝ)) * _root_.GD.N0234.N0736.d003268 x := by
  rw [_root_.GD.N0232.N0719.N0863.d010240]
  have hn : (Fintype.card ι : ℝ) ≠ 0 :=
    ne_of_gt (_root_.GD.N0234.N0736.d003271 (ι := ι))
  field_simp



theorem d010242
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (e : κ ≃ ι) (x : ι → E) :
    _root_.GD.N0232.N0719.N0863.d010235 (x ∘ e) = _root_.GD.N0232.N0719.N0863.d010235 x := by
  unfold _root_.GD.N0232.N0719.N0863.d010235
  calc
    (∑ i : κ, ∑ j : κ, ∑ l : κ, _root_.GD.N0232.N0719.N0863.d010234 (x ∘ e) i j l) =
        ∑ i : κ, ∑ j : κ, ∑ l : κ,
          _root_.GD.N0232.N0719.N0863.d010234 x (e i) (e j) (e l) := by rfl
    _ = ∑ i : κ, ∑ j : κ, ∑ l : ι,
          _root_.GD.N0232.N0719.N0863.d010234 x (e i) (e j) l := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact Equiv.sum_comp e (fun l : ι ↦ _root_.GD.N0232.N0719.N0863.d010234 x (e i) (e j) l)
    _ = ∑ i : κ, ∑ j : ι, ∑ l : ι,
          _root_.GD.N0232.N0719.N0863.d010234 x (e i) j l := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Equiv.sum_comp e
        (fun j : ι ↦ ∑ l : ι, _root_.GD.N0232.N0719.N0863.d010234 x (e i) j l)
    _ = ∑ i : ι, ∑ j : ι, ∑ l : ι,
          _root_.GD.N0232.N0719.N0863.d010234 x i j l := by
      exact Equiv.sum_comp e
        (fun i : ι ↦ ∑ j : ι, ∑ l : ι, _root_.GD.N0232.N0719.N0863.d010234 x i j l)




def d010243 (x : ι → E) (t : Fin 3 ↪ ι) : ℝ :=
  _root_.GD.N0232.N0719.N0863.d010234 x (t 0) (t 1) (t 2)



def d010244 (x : ι → E) : ℝ :=
  ∑ t : Fin 3 ↪ ι, _root_.GD.N0232.N0719.N0863.d010243 x t



def d010245 (σ : Equiv.Perm (Fin 3)) :
    (Fin 3 ↪ ι) ≃ (Fin 3 ↪ ι) where
  toFun t := σ.toEmbedding.trans t
  invFun t := σ.symm.toEmbedding.trans t
  left_inv t := by
    ext i
    simp
  right_inv t := by
    ext i
    simp

@[simp]
theorem d010246
    (σ : Equiv.Perm (Fin 3)) (t : Fin 3 ↪ ι) (i : Fin 3) :
    _root_.GD.N0232.N0719.N0863.d010245 σ t i = t (σ i) :=
  rfl



theorem d010247 (x : ι → E) :
    (∑ t : Fin 3 ↪ ι, ‖x (t 0) - x (t 1)‖ ^ 2) =
      ∑ t : Fin 3 ↪ ι, ‖x (t 1) - x (t 2)‖ ^ 2 := by
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  calc
    (∑ t : Fin 3 ↪ ι, ‖x (t 0) - x (t 1)‖ ^ 2) =
        ∑ t : Fin 3 ↪ ι,
          ‖x ((_root_.GD.N0232.N0719.N0863.d010245 σ t) 0) -
            x ((_root_.GD.N0232.N0719.N0863.d010245 σ t) 1)‖ ^ 2 := by
      symm
      exact Equiv.sum_comp (_root_.GD.N0232.N0719.N0863.d010245 σ)
        (fun t : Fin 3 ↪ ι ↦ ‖x (t 0) - x (t 1)‖ ^ 2)
    _ = ∑ t : Fin 3 ↪ ι, ‖x (t 2) - x (t 1)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [_root_.GD.N0232.N0719.N0863.d010246]
      dsimp [σ]
      rw [Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    _ = ∑ t : Fin 3 ↪ ι, ‖x (t 1) - x (t 2)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [norm_sub_rev]


theorem d010248 (x : ι → E) :
    (∑ t : Fin 3 ↪ ι, ‖x (t 0) - x (t 2)‖ ^ 2) =
      ∑ t : Fin 3 ↪ ι, ‖x (t 1) - x (t 2)‖ ^ 2 := by
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  calc
    (∑ t : Fin 3 ↪ ι, ‖x (t 0) - x (t 2)‖ ^ 2) =
        ∑ t : Fin 3 ↪ ι,
          ‖x ((_root_.GD.N0232.N0719.N0863.d010245 σ t) 0) -
            x ((_root_.GD.N0232.N0719.N0863.d010245 σ t) 2)‖ ^ 2 := by
      symm
      exact Equiv.sum_comp (_root_.GD.N0232.N0719.N0863.d010245 σ)
        (fun t : Fin 3 ↪ ι ↦ ‖x (t 0) - x (t 2)‖ ^ 2)
    _ = ∑ t : Fin 3 ↪ ι, ‖x (t 1) - x (t 2)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [_root_.GD.N0232.N0719.N0863.d010246]
      dsimp [σ]
      rw [Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]



theorem d010249 (x : ι → E) :
    (∑ e : Fin 2 ↪ ι, ‖x (e 0) - x (e 1)‖ ^ 2) =
      _root_.GD.N0234.N0736.d003269 x := by
  classical
  let f : ι × ι → ℝ := fun p ↦ ‖x p.1 - x p.2‖ ^ 2
  have hcompl :
      (∑ p : {p : ι × ι // ¬p.1 ≠ p.2}, f p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have heq : p.1.1 = p.1.2 := not_ne_iff.mp p.2
    simp [f, heq]
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (p := fun p : ι × ι ↦ p.1 ≠ p.2) f
  calc
    (∑ e : Fin 2 ↪ ι, ‖x (e 0) - x (e 1)‖ ^ 2) =
        ∑ p : {p : ι × ι // p.1 ≠ p.2}, f p := by
      exact Equiv.sum_comp Function.Embedding.twoEmbeddingEquiv
        (fun p : {p : ι × ι // p.1 ≠ p.2} ↦ f p)
    _ = _root_.GD.N0234.N0736.d003269 x := by
      rw [hcompl, add_zero] at hsplit
      rw [hsplit]
      unfold _root_.GD.N0234.N0736.d003269
      change (Finset.univ : Finset (ι × ι)).sum f =
        ∑ i : ι, ∑ j : ι, ‖x i - x j‖ ^ 2
      rw [show (Finset.univ : Finset (ι × ι)) =
          Finset.univ ×ˢ Finset.univ by ext p; simp]
      rw [Finset.sum_product]



theorem d010250
    (x : ι → E) :
    (∑ t : Fin 3 ↪ ι, ‖x (t 1) - x (t 2)‖ ^ 2) =
      ((Fintype.card ι - 2 : ℕ) : ℝ) * _root_.GD.N0234.N0736.d003269 x := by
  classical
  calc
    (∑ t : Fin 3 ↪ ι, ‖x (t 1) - x (t 2)‖ ^ 2) =
        ∑ f : Σ e : Fin 2 ↪ ι, {a // a ∉ Set.range e},
          ‖x (f.1 0) - x (f.1 1)‖ ^ 2 := by
      simpa only [Equiv.embeddingFinSucc_fst, Function.comp_apply,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using
        (Equiv.sum_comp (Equiv.embeddingFinSucc 2 ι)
          (fun f : Σ e : Fin 2 ↪ ι, {a // a ∉ Set.range e} ↦
            ‖x (f.1 0) - x (f.1 1)‖ ^ 2))
    _ = (∑ e : Fin 2 ↪ ι,
        ∑ _a : {a // a ∉ Set.range e}, ‖x (e 0) - x (e 1)‖ ^ 2) := by
      rw [Fintype.sum_sigma]
    _ = ∑ e : Fin 2 ↪ ι,
          ((Fintype.card ι - 2 : ℕ) : ℝ) *
            ‖x (e 0) - x (e 1)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.card_univ, Fintype.card_subtype_compl, Fintype.card_range]
      norm_num
    _ = ((Fintype.card ι - 2 : ℕ) : ℝ) *
          ∑ e : Fin 2 ↪ ι, ‖x (e 0) - x (e 1)‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = ((Fintype.card ι - 2 : ℕ) : ℝ) * _root_.GD.N0234.N0736.d003269 x := by
      rw [_root_.GD.N0232.N0719.N0863.d010249]



theorem d010251
    (x : ι → E) :
    _root_.GD.N0232.N0719.N0863.d010244 x =
      3 * ((Fintype.card ι - 2 : ℕ) : ℝ) * _root_.GD.N0234.N0736.d003269 x := by
  unfold _root_.GD.N0232.N0719.N0863.d010244 _root_.GD.N0232.N0719.N0863.d010243 _root_.GD.N0232.N0719.N0863.d010234
  simp only [Finset.sum_add_distrib]
  rw [_root_.GD.N0232.N0719.N0863.d010247, _root_.GD.N0232.N0719.N0863.d010248,
    _root_.GD.N0232.N0719.N0863.d010250]
  ring



theorem d010252
    (hcard : 2 ≤ Fintype.card ι) (x : ι → E) :
    _root_.GD.N0232.N0719.N0863.d010244 x =
      6 * (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 2) *
        _root_.GD.N0234.N0736.d003268 x := by
  rw [_root_.GD.N0232.N0719.N0863.d010251,
    ← _root_.GD.N0234.N0736.d003281]
  rw [Nat.cast_sub hcard]
  norm_num
  ring



theorem d010253
    (hcard : 3 ≤ Fintype.card ι) (x : ι → E) :
    ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) *
        ((Fintype.card ι : ℝ) - 2))⁻¹ * _root_.GD.N0232.N0719.N0863.d010244 x =
      (6 / ((Fintype.card ι : ℝ) - 1)) * _root_.GD.N0234.N0736.d003268 x := by
  rw [_root_.GD.N0232.N0719.N0863.d010252
    (Nat.le_trans (by norm_num) hcard) x]
  have hk : (Fintype.card ι : ℝ) ≠ 0 := by
    positivity
  have hcardR : (3 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hcard
  have hk1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    exact ne_of_gt (by linarith)
  have hk2 : (Fintype.card ι : ℝ) - 2 ≠ 0 := by
    exact ne_of_gt (by linarith)
  field_simp




def d010254 (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ l, _root_.GD.N0232.N0719.N1002.d010215 (x i) (x j) (x l)


def d010255 (x : ι → ℝ) : ℝ := ∑ i, x i


def d010256 (x : ι → ℝ) : ℝ := ∑ i, (x i) ^ 2


def d010257 (x : ι → ℝ) : ℝ := ∑ i, (x i) ^ 3


def d010258 (x : ι → ℝ) : ℝ :=
  ∑ i, (x i - _root_.GD.N0232.N0719.N0863.d010255 x / (Fintype.card ι : ℝ)) ^ 3


theorem d010259 (a b c : ℝ) :
    _root_.GD.N0232.N0719.N1002.d010215 a b c =
      (2 / 9 : ℝ) * (a ^ 3 + b ^ 3 + c ^ 3) -
      (1 / 3 : ℝ) *
        (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c +
          c ^ 2 * a + c ^ 2 * b) +
      (4 / 3 : ℝ) * a * b * c := by
  simp only [_root_.GD.N0232.N0719.N1002.d010215, _root_.GD.N0232.N0719.N1002.d010214]
  ring


end

end GD.N0232.N0719.N0863
