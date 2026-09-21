import GD.Module0445








set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open _root_.GD.N0232.N0720.N1164

namespace GD.N0106.N0428.N0765.N1548

structure d006926 where
  lo : ℤ
  hi : ℤ
deriving DecidableEq, Repr

def d006927 (a b : ℤ) : ℤ := -((-a) / b)

namespace d006926

def d006928 (s : ℤ) (I : _root_.GD.N0106.N0428.N0765.N1548.d006926) (x : ℝ) : Prop :=
  (I.lo : ℝ) / (s : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ) / (s : ℝ)

def d006929 (s : ℤ) (I : _root_.GD.N0106.N0428.N0765.N1548.d006926) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ⟨(I.lo : ℚ) / (s : ℚ), (I.hi : ℚ) / (s : ℚ)⟩

def d006930 (s : ℤ) (J : _root_.GD.N0106.N0428.N0765.N1548.d006926) (I : _root_.GD.N0232.N0720.N1164.d006809) : Prop :=
  (J.lo : ℚ) ≤ I.lo * (s : ℚ) ∧ I.hi * (s : ℚ) ≤ (J.hi : ℚ)

instance (s : ℤ) (J : _root_.GD.N0106.N0428.N0765.N1548.d006926) (I : _root_.GD.N0232.N0720.N1164.d006809) : Decidable (_root_.GD.N0106.N0428.N0765.N1548.d006926.d006930 s J I) := by
  unfold _root_.GD.N0106.N0428.N0765.N1548.d006926.d006930
  infer_instance

theorem d006931 (s : ℤ) (I : _root_.GD.N0106.N0428.N0765.N1548.d006926) (x : ℝ) :
    I.d006928 s x ↔ (I.d006929 s).d006810 x := by
  simp [_root_.GD.N0106.N0428.N0765.N1548.d006926.d006928, _root_.GD.N0106.N0428.N0765.N1548.d006926.d006929, _root_.GD.N0232.N0720.N1164.d006809.d006810]

theorem d006932 {s : ℤ} {I : _root_.GD.N0232.N0720.N1164.d006809} {J : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x : ℝ}
    (hs : 0 < s) (hI : I.d006810 x) (hJ : J.d006930 s I) : J.d006928 s x := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hlo : (J.lo : ℝ) ≤ (I.lo : ℝ) * (s : ℝ) := by exact_mod_cast hJ.1
  have hhi : (I.hi : ℝ) * (s : ℝ) ≤ (J.hi : ℝ) := by exact_mod_cast hJ.2
  exact ⟨((div_le_iff₀ hsR).mpr hlo).trans hI.1,
    hI.2.trans ((le_div_iff₀ hsR).mpr hhi)⟩

theorem d006933 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x : ℝ}
    (hs : 0 < s) (hx : I.d006928 s x) (hlo : J.lo ≤ I.lo) (hhi : I.hi ≤ J.hi) :
    J.d006928 s x := by
  have hsR : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  have hloR : (J.lo : ℝ) ≤ I.lo := by exact_mod_cast hlo
  have hhiR : (I.hi : ℝ) ≤ J.hi := by exact_mod_cast hhi
  exact ⟨(div_le_div_of_nonneg_right hloR hsR).trans hx.1,
    hx.2.trans (div_le_div_of_nonneg_right hhiR hsR)⟩

def d006934 : _root_.GD.N0106.N0428.N0765.N1548.d006926 := ⟨0, 0⟩
def d006935 (s : ℤ) : _root_.GD.N0106.N0428.N0765.N1548.d006926 := ⟨s, s⟩
def d006936 (I J : _root_.GD.N0106.N0428.N0765.N1548.d006926) : _root_.GD.N0106.N0428.N0765.N1548.d006926 := ⟨I.lo + J.lo, I.hi + J.hi⟩
def d006937 (I : _root_.GD.N0106.N0428.N0765.N1548.d006926) : _root_.GD.N0106.N0428.N0765.N1548.d006926 := ⟨-I.hi, -I.lo⟩
def d006938 (I J : _root_.GD.N0106.N0428.N0765.N1548.d006926) : _root_.GD.N0106.N0428.N0765.N1548.d006926 := ⟨I.lo - J.hi, I.hi - J.lo⟩

def d006939 (s n d : ℤ) : _root_.GD.N0106.N0428.N0765.N1548.d006926 := ⟨n * s / d, _root_.GD.N0106.N0428.N0765.N1548.d006927 (n * s) d⟩

def d006940 (s : ℤ) (I J : _root_.GD.N0106.N0428.N0765.N1548.d006926) : _root_.GD.N0106.N0428.N0765.N1548.d006926 :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)) / s,
   _root_.GD.N0106.N0428.N0765.N1548.d006927 (max (max (I.lo * J.lo) (I.lo * J.hi))
     (max (I.hi * J.lo) (I.hi * J.hi))) s⟩

def d006941 (s : ℤ) (I : _root_.GD.N0106.N0428.N0765.N1548.d006926) : _root_.GD.N0106.N0428.N0765.N1548.d006926 :=
  if I.lo ≤ 0 ∧ 0 ≤ I.hi then
    ⟨0, _root_.GD.N0106.N0428.N0765.N1548.d006927 (max (I.lo ^ 2) (I.hi ^ 2)) s⟩
  else
    ⟨min (I.lo ^ 2) (I.hi ^ 2) / s, _root_.GD.N0106.N0428.N0765.N1548.d006927 (max (I.lo ^ 2) (I.hi ^ 2)) s⟩

def d006942 (s : ℤ) (I : _root_.GD.N0106.N0428.N0765.N1548.d006926) : _root_.GD.N0106.N0428.N0765.N1548.d006926 := ⟨max 0 I.lo, min s I.hi⟩

def d006943 (f : ℕ → _root_.GD.N0106.N0428.N0765.N1548.d006926) : ℕ → _root_.GD.N0106.N0428.N0765.N1548.d006926
  | 0 => _root_.GD.N0106.N0428.N0765.N1548.d006926.d006934
  | n + 1 => (d006943 f n).d006936 (f n)

def d006944 (s : ℤ) (I J : _root_.GD.N0106.N0428.N0765.N1548.d006926) : _root_.GD.N0106.N0428.N0765.N1548.d006926 :=
  ⟨I.lo * J.lo / s, _root_.GD.N0106.N0428.N0765.N1548.d006927 (I.hi * J.hi) s⟩

def d006945 (s : ℤ) (I : _root_.GD.N0106.N0428.N0765.N1548.d006926) : _root_.GD.N0106.N0428.N0765.N1548.d006926 :=
  ⟨s * s / I.hi, _root_.GD.N0106.N0428.N0765.N1548.d006927 (s * s) I.lo⟩


def d006946 (s : ℤ) (I : _root_.GD.N0106.N0428.N0765.N1548.d006926) : ℕ → _root_.GD.N0106.N0428.N0765.N1548.d006926
  | 0 => _root_.GD.N0106.N0428.N0765.N1548.d006926.d006935 s
  | n + 1 => ⟨I.lo ^ (n + 1) / s ^ n, _root_.GD.N0106.N0428.N0765.N1548.d006927 (I.hi ^ (n + 1)) (s ^ n)⟩



def d006947 (s : ℤ) (I J : _root_.GD.N0106.N0428.N0765.N1548.d006926) : Prop :=
  0 ≤ I.lo ∧ 0 ≤ J.lo ∧ 0 ≤ J.hi ∧ J.lo ^ 2 ≤ I.lo * s ∧ I.hi * s ≤ J.hi ^ 2

instance (s : ℤ) (I J : _root_.GD.N0106.N0428.N0765.N1548.d006926) : Decidable (_root_.GD.N0106.N0428.N0765.N1548.d006926.d006947 s I J) := by
  unfold _root_.GD.N0106.N0428.N0765.N1548.d006926.d006947
  infer_instance

theorem d006948 (s : ℤ) : _root_.GD.N0106.N0428.N0765.N1548.d006926.d006934.d006928 s 0 := by simp [_root_.GD.N0106.N0428.N0765.N1548.d006926.d006928, _root_.GD.N0106.N0428.N0765.N1548.d006926.d006934]

theorem d006949 {s : ℤ} (hs : 0 < s) : (_root_.GD.N0106.N0428.N0765.N1548.d006926.d006935 s).d006928 s 1 := by
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  simp [_root_.GD.N0106.N0428.N0765.N1548.d006926.d006928, _root_.GD.N0106.N0428.N0765.N1548.d006926.d006935, hsR]

theorem d006950 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x : ℝ}
    (hs : 0 < s) (hx : I.d006928 s x) : I.lo ≤ I.hi := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have h := (div_le_div_iff_of_pos_right hsR).mp (hx.1.trans hx.2)
  exact_mod_cast h

theorem d006951 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x y : ℝ}
    (hx : I.d006928 s x) (hy : J.d006928 s y) : (I.d006936 J).d006928 s (x + y) := by
  unfold _root_.GD.N0106.N0428.N0765.N1548.d006926.d006928 _root_.GD.N0106.N0428.N0765.N1548.d006926.d006936 at *
  push_cast
  simp only [add_div]
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem d006952 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x : ℝ}
    (hx : I.d006928 s x) : I.d006937.d006928 s (-x) := by
  unfold _root_.GD.N0106.N0428.N0765.N1548.d006926.d006928 _root_.GD.N0106.N0428.N0765.N1548.d006926.d006937 at *
  push_cast
  simp only [neg_div]
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

theorem d006953 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x y : ℝ}
    (hx : I.d006928 s x) (hy : J.d006928 s y) : (I.d006938 J).d006928 s (x - y) := by
  unfold _root_.GD.N0106.N0428.N0765.N1548.d006926.d006928 _root_.GD.N0106.N0428.N0765.N1548.d006926.d006938 at *
  push_cast
  simp only [sub_div]
  exact ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

theorem d006954 {s : ℤ} (f : ℕ → _root_.GD.N0106.N0428.N0765.N1548.d006926) (g : ℕ → ℝ) (n : ℕ)
    (hfg : ∀ i, i < n → (f i).d006928 s (g i)) :
    (_root_.GD.N0106.N0428.N0765.N1548.d006926.d006943 f n).d006928 s (∑ i ∈ Finset.range n, g i) := by
  induction n with
  | zero => simpa [_root_.GD.N0106.N0428.N0765.N1548.d006926.d006943] using _root_.GD.N0106.N0428.N0765.N1548.d006926.d006948 s
  | succ n ih =>
    rw [Finset.sum_range_succ, _root_.GD.N0106.N0428.N0765.N1548.d006926.d006943]
    exact _root_.GD.N0106.N0428.N0765.N1548.d006926.d006951 (ih (fun i hi => hfg i (Nat.lt_succ_of_lt hi)))
      (hfg n (Nat.lt_succ_self n))

theorem d006955 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x : ℝ}
    (hs : 0 < s) (hx : I.d006928 s x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (I.d006942 s).d006928 s x := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  unfold _root_.GD.N0106.N0428.N0765.N1548.d006926.d006928 _root_.GD.N0106.N0428.N0765.N1548.d006926.d006942
  push_cast
  constructor
  · apply (div_le_iff₀ hsR).mpr
    exact max_le (mul_nonneg hx0 hsR.le) ((div_le_iff₀ hsR).mp hx.1)
  · apply (le_div_iff₀ hsR).mpr
    exact le_min (by nlinarith) ((le_div_iff₀ hsR).mp hx.2)

theorem d006956 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x : ℝ}
    (hs : 0 < s) (hI : 0 ≤ I.lo) (hx : I.d006928 s x) : 0 ≤ x := by
  have hsR : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  have hIR : (0 : ℝ) ≤ I.lo := by exact_mod_cast hI
  exact (div_nonneg hIR hsR).trans hx.1

end d006926

theorem d006957 (a : ℤ) {b : ℤ} (hb : 0 < b) :
    ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  apply (le_div_iff₀ hbR).mpr
  exact_mod_cast Int.ediv_mul_le a hb.ne'

theorem d006958 (a : ℤ) {b : ℤ} (hb : 0 < b) : a ≤ _root_.GD.N0106.N0428.N0765.N1548.d006927 a b * b := by
  have h := Int.ediv_mul_le (-a) hb.ne'
  unfold _root_.GD.N0106.N0428.N0765.N1548.d006927
  nlinarith

theorem d006959 (a : ℤ) {b : ℤ} (hb : 0 < b) :
    (a : ℝ) / (b : ℝ) ≤ (_root_.GD.N0106.N0428.N0765.N1548.d006927 a b : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  apply (div_le_iff₀ hbR).mpr
  exact_mod_cast _root_.GD.N0106.N0428.N0765.N1548.d006958 a hb

theorem d006960 (a : ℤ) {b s : ℤ} (hb : 0 < b) (hs : 0 < s) :
    ((a / b : ℤ) : ℝ) / (s : ℝ) ≤ (a : ℝ) / (b : ℝ) / (s : ℝ) := by
  have hsR : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  exact div_le_div_of_nonneg_right (_root_.GD.N0106.N0428.N0765.N1548.d006957 a hb) hsR

theorem d006961 (a : ℤ) {b s : ℤ} (hb : 0 < b) (hs : 0 < s) :
    (a : ℝ) / (b : ℝ) / (s : ℝ) ≤ (_root_.GD.N0106.N0428.N0765.N1548.d006927 a b : ℝ) / (s : ℝ) := by
  have hsR : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  exact div_le_div_of_nonneg_right (_root_.GD.N0106.N0428.N0765.N1548.d006959 a hb) hsR

theorem d006962 (a b : ℤ) {s : ℤ} (hs : 0 < s) :
    ((a * b / s : ℤ) : ℝ) / (s : ℝ) ≤ (a : ℝ) / (s : ℝ) * ((b : ℝ) / (s : ℝ)) := by
  refine (_root_.GD.N0106.N0428.N0765.N1548.d006960 (a * b) hs hs).trans_eq ?_
  push_cast
  ring

theorem d006963 (a b : ℤ) {s : ℤ} (hs : 0 < s) :
    (a : ℝ) / (s : ℝ) * ((b : ℝ) / (s : ℝ)) ≤
      (_root_.GD.N0106.N0428.N0765.N1548.d006927 (a * b) s : ℝ) / (s : ℝ) := by
  convert _root_.GD.N0106.N0428.N0765.N1548.d006961 (a * b) hs hs using 1 <;> push_cast <;> ring

namespace d006926

theorem d006964 {s d : ℤ} (hs : 0 < s) (hd : 0 < d) (n : ℤ) :
    (_root_.GD.N0106.N0428.N0765.N1548.d006926.d006939 s n d).d006928 s ((n : ℝ) / (d : ℝ)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heq : ((n * s : ℤ) : ℝ) / (d : ℝ) / (s : ℝ) =
      (n : ℝ) / (d : ℝ) := by
    push_cast
    field_simp [hsR.ne', hdR.ne']
  have hlo := _root_.GD.N0106.N0428.N0765.N1548.d006960 (n * s) hd hs
  have hhi := _root_.GD.N0106.N0428.N0765.N1548.d006961 (n * s) hd hs
  rw [heq] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem d006965 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x y : ℝ}
    (hs : 0 < s) (hI : 0 ≤ I.lo) (hJ : 0 ≤ J.lo)
    (hx : I.d006928 s x) (hy : J.d006928 s y) :
    (I.d006944 s J).d006928 s (x * y) := by
  have hsR : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  have hJ0 : (0 : ℝ) ≤ (J.lo : ℝ) / (s : ℝ) :=
    div_nonneg (by exact_mod_cast hJ) hsR
  have hx0 := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006956 hs hI hx
  have hy0 := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006956 hs hJ hy
  constructor
  · exact (_root_.GD.N0106.N0428.N0765.N1548.d006962 I.lo J.lo hs).trans (mul_le_mul hx.1 hy.1 hJ0 hx0)
  · exact (mul_le_mul hx.2 hy.2 hy0 (hx0.trans hx.2)).trans (_root_.GD.N0106.N0428.N0765.N1548.d006963 I.hi J.hi hs)

theorem d006966 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x : ℝ}
    (hs : 0 < s) (hI : 0 < I.lo) (hx : I.d006928 s x) :
    (I.d006945 s).d006928 s (1 / x) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hloR : (0 : ℝ) < I.lo := by exact_mod_cast hI
  have hhi : 0 < I.hi := hI.trans_le (_root_.GD.N0106.N0428.N0765.N1548.d006926.d006950 hs hx)
  have hhiR : (0 : ℝ) < I.hi := by exact_mod_cast hhi
  have hx0 : 0 < x := (div_pos hloR hsR).trans_le hx.1
  have hlo := _root_.GD.N0106.N0428.N0765.N1548.d006960 (s * s) hhi hs
  have hhi' := _root_.GD.N0106.N0428.N0765.N1548.d006961 (s * s) hI hs
  have eqhi : ((s * s : ℤ) : ℝ) / (I.hi : ℝ) / (s : ℝ) =
      1 / ((I.hi : ℝ) / (s : ℝ)) := by
    push_cast
    field_simp [hsR.ne', hhiR.ne']
  have eqlo : ((s * s : ℤ) : ℝ) / (I.lo : ℝ) / (s : ℝ) =
      1 / ((I.lo : ℝ) / (s : ℝ)) := by
    push_cast
    field_simp [hsR.ne', hloR.ne']
  rw [eqhi] at hlo
  rw [eqlo] at hhi'
  exact ⟨hlo.trans (one_div_le_one_div_of_le hx0 hx.2),
    (one_div_le_one_div_of_le (div_pos hloR hsR) hx.1).trans hhi'⟩

theorem d006967 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x : ℝ}
    (hs : 0 < s) (hI : 0 ≤ I.lo) (hx : I.d006928 s x) (n : ℕ) :
    (I.d006946 s n).d006928 s (x ^ n) := by
  cases n with
  | zero => simpa only [_root_.GD.N0106.N0428.N0765.N1548.d006926.d006946, pow_zero] using _root_.GD.N0106.N0428.N0765.N1548.d006926.d006949 hs
  | succ n =>
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    have hsN : 0 < s ^ n := pow_pos hs _
    have hlo := _root_.GD.N0106.N0428.N0765.N1548.d006960 (I.lo ^ (n + 1)) hsN hs
    have hhi := _root_.GD.N0106.N0428.N0765.N1548.d006961 (I.hi ^ (n + 1)) hsN hs
    have eqlo : ((I.lo ^ (n + 1) : ℤ) : ℝ) / ((s ^ n : ℤ) : ℝ) / (s : ℝ) =
        ((I.lo : ℝ) / (s : ℝ)) ^ (n + 1) := by
      push_cast
      rw [div_div, ← pow_succ, div_pow]
    have eqhi : ((I.hi ^ (n + 1) : ℤ) : ℝ) / ((s ^ n : ℤ) : ℝ) / (s : ℝ) =
        ((I.hi : ℝ) / (s : ℝ)) ^ (n + 1) := by
      push_cast
      rw [div_div, ← pow_succ, div_pow]
    rw [eqlo] at hlo
    rw [eqhi] at hhi
    have hI0 : (0 : ℝ) ≤ (I.lo : ℝ) / (s : ℝ) :=
      div_nonneg (by exact_mod_cast hI) hsR.le
    have hx0 := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006956 hs hI hx
    exact ⟨hlo.trans (pow_le_pow_left₀ hI0 hx.1 _),
      (pow_le_pow_left₀ hx0 hx.2 _).trans hhi⟩



theorem d006968 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x : ℝ}
    (hs : 0 < s) (hx : I.d006928 s x) (hc : _root_.GD.N0106.N0428.N0765.N1548.d006926.d006947 s I J) :
    J.d006928 s (Real.sqrt x) := by
  obtain ⟨hI0, hJlo, hJhi, hlow, hhigh⟩ := hc
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hx0 := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006956 hs hI0 hx
  have hJloR : (0 : ℝ) ≤ (J.lo : ℝ) / (s : ℝ) :=
    div_nonneg (by exact_mod_cast hJlo) hsR.le
  have hJhiR : (0 : ℝ) ≤ (J.hi : ℝ) / (s : ℝ) :=
    div_nonneg (by exact_mod_cast hJhi) hsR.le
  have hlR : (J.lo : ℝ) ^ 2 ≤ (I.lo : ℝ) * (s : ℝ) := by exact_mod_cast hlow
  have hhR : (I.hi : ℝ) * (s : ℝ) ≤ (J.hi : ℝ) ^ 2 := by exact_mod_cast hhigh
  have hlo : ((J.lo : ℝ) / (s : ℝ)) ^ 2 ≤ (I.lo : ℝ) / (s : ℝ) := by
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hsR) hsR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlR hsR.le]
  have hhi : (I.hi : ℝ) / (s : ℝ) ≤ ((J.hi : ℝ) / (s : ℝ)) ^ 2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ hsR (sq_pos_of_pos hsR)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hhR hsR.le]
  have hsqrt := Real.sq_sqrt hx0
  have hsqrt0 := Real.sqrt_nonneg x
  constructor <;> nlinarith [hx.1, hx.2]

end d006926
end GD.N0106.N0428.N0765.N1548
