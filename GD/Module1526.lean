import GD.Module0514
import GD.Module1522
import GD.Module1411








set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace GD.N0106.N0428.N0765.N1581
open _root_.GD.N0106.N0428.N0765.N1579 _root_.GD.N0106.N0428.N0765.N1548 _root_.GD.N0106.N0428.N0765.N1634

def d023709 (a : Array _root_.GD.N0106.N0428.N0765.N1579.d007457) (k : ℕ) : _root_.GD.N0106.N0428.N0765.N1579.d007457 := (a[k]?).getD _root_.GD.N0106.N0428.N0765.N1579.d007436.d007438
def d023710 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) (k : ℕ) : _root_.GD.N0106.N0428.N0765.N1579.d007461 :=
  (cache.innerRows[k]?).getD _root_.GD.N0106.N0428.N0765.N1579.d007462

def d023711 (a : Array _root_.GD.N0106.N0428.N0765.N1579.d007457) : Prop :=
  a.size = 1691 ∧ _root_.GD.N0106.N0428.N0765.N1581.d023709 a 0 = _root_.GD.N0106.N0428.N0765.N1579.d007459 ∧
  (∀ k : Fin 1690, _root_.GD.N0106.N0428.N0765.N1581.d023709 a (k.val + 1) =
    _root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1581.d023709 a k.val) (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 _root_.GD.N0106.N0428.N0765.N1582.d007421)) ∧
  (∀ k : Fin 1691, (_root_.GD.N0106.N0428.N0765.N1581.d023709 a k.val).valid = true)

instance (a : Array _root_.GD.N0106.N0428.N0765.N1579.d007457) : Decidable (_root_.GD.N0106.N0428.N0765.N1581.d023711 a) := by
  unfold _root_.GD.N0106.N0428.N0765.N1581.d023711
  infer_instance

def d023712 (positive negative : Array _root_.GD.N0106.N0428.N0765.N1579.d007457) : Prop :=
  negative.size = 1691 ∧ _root_.GD.N0106.N0428.N0765.N1581.d023709 negative 0 = _root_.GD.N0106.N0428.N0765.N1579.d007459 ∧
  (∀ k : Fin 1690, _root_.GD.N0106.N0428.N0765.N1581.d023709 negative (k.val + 1) =
    _root_.GD.N0106.N0428.N0765.N1579.d007436.d007448 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1581.d023709 positive (k.val + 1))) ∧
  (∀ k : Fin 1691, (_root_.GD.N0106.N0428.N0765.N1581.d023709 negative k.val).valid = true)

instance (positive negative : Array _root_.GD.N0106.N0428.N0765.N1579.d007457) : Decidable (_root_.GD.N0106.N0428.N0765.N1581.d023712 positive negative) := by
  unfold _root_.GD.N0106.N0428.N0765.N1581.d023712
  infer_instance

def d023713 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : Prop :=
  cache.innerRows.size = 129 ∧ ∀ k : Fin 129,
    _root_.GD.N0106.N0428.N0765.N1581.d023710 cache k.val = _root_.GD.N0106.N0428.N0765.N1579.d007466 cache.positive cache.negative k.val ∧
    (_root_.GD.N0106.N0428.N0765.N1581.d023710 cache k.val).lam.valid = true ∧
    (_root_.GD.N0106.N0428.N0765.N1581.d023710 cache k.val).complement.valid = true ∧
    (_root_.GD.N0106.N0428.N0765.N1581.d023710 cache k.val).common.valid = true ∧
    (_root_.GD.N0106.N0428.N0765.N1581.d023710 cache k.val).baseC.valid = true

instance (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : Decidable (_root_.GD.N0106.N0428.N0765.N1581.d023713 cache) := by
  unfold _root_.GD.N0106.N0428.N0765.N1581.d023713
  infer_instance



def d023714 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : Prop :=
  _root_.GD.N0106.N0428.N0765.N1581.d023711 cache.positive ∧ _root_.GD.N0106.N0428.N0765.N1581.d023712 cache.positive cache.negative ∧
  _root_.GD.N0106.N0428.N0765.N1581.d023713 cache ∧ cache.epsilon = _root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 _root_.GD.N0106.N0428.N0765.N1582.d007422

instance (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : Decidable (_root_.GD.N0106.N0428.N0765.N1581.d023714 cache) := by
  unfold _root_.GD.N0106.N0428.N0765.N1581.d023714
  infer_instance

def d023715 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : Bool := decide (_root_.GD.N0106.N0428.N0765.N1581.d023714 cache)

theorem d023716 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true ↔ _root_.GD.N0106.N0428.N0765.N1581.d023714 cache := by
  simp only [_root_.GD.N0106.N0428.N0765.N1581.d023715, decide_eq_true_eq]

theorem d023717 : _root_.GD.N0106.N0428.N0765.N1579.d007459.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (1 : ℝ) :=
  _root_.GD.N0106.N0428.N0765.N1548.d006926.d006949 _root_.GD.N0106.N0428.N0765.N1573.d022632

theorem d023718 : (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 _root_.GD.N0106.N0428.N0765.N1582.d007421).d007727
    _root_.GD.N0106.N0428.N0765.N1579.d007456 (Real.exp (1 / 16)) := _root_.GD.N0106.N0428.N0765.N1573.d022633

theorem d023719 {a : Array _root_.GD.N0106.N0428.N0765.N1579.d007457} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023711 a) {k : ℕ} (hk : k < 1691) :
    (_root_.GD.N0106.N0428.N0765.N1581.d023709 a k).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (Real.exp ((k : ℝ) / 16)) := by
  obtain ⟨_, hz, hstep, hv⟩ := hc
  induction k with
  | zero =>
    rw [hz]
    simpa only [Nat.cast_zero, zero_div, Real.exp_zero] using _root_.GD.N0106.N0428.N0765.N1581.d023717
  | succ k ih =>
    have hki : k < 1690 := by omega
    have heq := hstep ⟨k, hki⟩
    have hout := hv ⟨k + 1, hk⟩
    rw [heq] at hout ⊢
    have h := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hout (ih (by omega)) _root_.GD.N0106.N0428.N0765.N1581.d023718
    have he : Real.exp (((k + 1 : ℕ) : ℝ) / 16) =
        Real.exp ((k : ℝ) / 16) * Real.exp (1 / 16) := by
      rw [show (((k + 1 : ℕ) : ℝ) / 16) = (k : ℝ) / 16 + 1 / 16 by push_cast; ring,
        Real.exp_add]
    exact he.symm ▸ h

theorem d023720 {positive negative : Array _root_.GD.N0106.N0428.N0765.N1579.d007457}
    (hp : _root_.GD.N0106.N0428.N0765.N1581.d023711 positive) (hn : _root_.GD.N0106.N0428.N0765.N1581.d023712 positive negative)
    {k : ℕ} (hk : k < 1691) :
    (_root_.GD.N0106.N0428.N0765.N1581.d023709 negative k).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (Real.exp (-((k : ℝ) / 16))) := by
  obtain ⟨_, hz, hstep, hv⟩ := hn
  cases k with
  | zero =>
    rw [hz]
    simpa only [Nat.cast_zero, zero_div, neg_zero, Real.exp_zero] using _root_.GD.N0106.N0428.N0765.N1581.d023717
  | succ k =>
    have heq := hstep ⟨k, by omega⟩
    have hout := hv ⟨k + 1, hk⟩
    rw [heq] at hout ⊢
    have h := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007739 hout (_root_.GD.N0106.N0428.N0765.N1581.d023719 hp hk)
    simpa only [Real.exp_neg, one_div] using h

theorem d023721 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023714 cache) {k : ℤ}
    (hk : -1690 ≤ k ∧ k ≤ 1690) :
    (cache.d007468 k).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (Real.exp ((k : ℝ) / 16)) := by
  rcases hc with ⟨hp, hn, _, _⟩
  by_cases hk0 : 0 ≤ k
  · simp only [_root_.GD.N0106.N0428.N0765.N1579.d007463.d007468, _root_.GD.N0106.N0428.N0765.N1579.d007464, if_pos hk0]
    have h := _root_.GD.N0106.N0428.N0765.N1581.d023719 hp (k := k.toNat) (by omega)
    have he : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hk0
    simpa only [_root_.GD.N0106.N0428.N0765.N1581.d023709, he] using h
  · simp only [_root_.GD.N0106.N0428.N0765.N1579.d007463.d007468, _root_.GD.N0106.N0428.N0765.N1579.d007464, if_neg hk0]
    have h := _root_.GD.N0106.N0428.N0765.N1581.d023720 hp hn (k := (-k).toNat) (by omega)
    have he : (((-k).toNat : ℕ) : ℝ) = -(k : ℝ) := by
      have hi := Int.toNat_of_nonneg (show (0 : ℤ) ≤ -k by omega)
      exact_mod_cast hi
    simpa only [_root_.GD.N0106.N0428.N0765.N1581.d023709, he, neg_div, neg_neg] using h

noncomputable def d023722 (i : ℕ) : ℝ := ((i : ℝ) - 64) / 4

def d023723 (r : _root_.GD.N0106.N0428.N0765.N1579.d007461) (c : ℝ) : Prop :=
  r.lam.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1634.d023649 c) ∧
  r.complement.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1634.d023648 c) ∧
  r.common.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1634.d023650 c) ∧
  r.baseC.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1634.d023650 c ^ 5 * Real.sqrt (_root_.GD.N0106.N0428.N0765.N1634.d023650 c))

theorem d023724 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023714 cache)
    {i : ℕ} (hi : i < 129) : _root_.GD.N0106.N0428.N0765.N1581.d023723 (_root_.GD.N0106.N0428.N0765.N1581.d023710 cache i) (_root_.GD.N0106.N0428.N0765.N1581.d023722 i) := by
  obtain ⟨heq, hvL, hvM, hvC, hvB⟩ := hc.2.2.1.2 ⟨i, hi⟩
  rw [heq] at hvL hvM hvC hvB ⊢
  have hgrid := _root_.GD.N0106.N0428.N0765.N1581.d023721 hc
    (k := 4 * ((i : ℤ) - 64)) (by constructor <;> omega)
  have he : ((4 * ((i : ℤ) - 64) : ℤ) : ℝ) / 16 = _root_.GD.N0106.N0428.N0765.N1581.d023722 i := by
    unfold _root_.GD.N0106.N0428.N0765.N1581.d023722
    push_cast
    ring
  rw [he] at hgrid
  have hm := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007739 hvM (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 _root_.GD.N0106.N0428.N0765.N1581.d023717 hgrid)
  have hl := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hvL hgrid hm
  have hr := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hvC hl hm
  have hbvalid := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hvB
  have hpow := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007741 5 hbvalid.1 hr
  have hsqrt := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007742 hbvalid.2 hr
  have hb := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hvB hpow hsqrt
  exact ⟨hl, hm, hr, hb⟩



def d023725 (cache : _root_.GD.N0106.N0428.N0765.N1579.d007463) : Prop :=
  (∀ k : ℤ, -1690 ≤ k ∧ k ≤ 1690 →
    (cache.d007468 k).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (Real.exp ((k : ℝ) / 16))) ∧
  cache.innerRows.size = 129 ∧
  (∀ i : Fin 129, _root_.GD.N0106.N0428.N0765.N1581.d023723 (_root_.GD.N0106.N0428.N0765.N1581.d023710 cache i.val) (_root_.GD.N0106.N0428.N0765.N1581.d023722 i.val)) ∧
  cache.epsilon.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1562.d021061 (11 / 10) (1 / 4))

theorem d023726 {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463} (hc : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true) : _root_.GD.N0106.N0428.N0765.N1581.d023725 cache := by
  have hp := (_root_.GD.N0106.N0428.N0765.N1581.d023716 cache).mp hc
  refine ⟨fun _ hk => _root_.GD.N0106.N0428.N0765.N1581.d023721 hp hk, hp.2.2.1.1,
    fun i => _root_.GD.N0106.N0428.N0765.N1581.d023724 hp i.isLt, ?_⟩
  rw [hp.2.2.2]
  exact _root_.GD.N0106.N0428.N0765.N1573.d022642

end GD.N0106.N0428.N0765.N1581

#print axioms _root_.GD.N0106.N0428.N0765.N1581.d023726
