import GD.Module1742
import GD.Module1784
import GD.Module0554











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Finset

namespace GD.N0106.N0428.N0765.N1678
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1539 _root_.GD.N0106.N0428.N0765.N1521 _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1676
open _root_.GD.N0106.N0428.N0765.N1687 _root_.GD.N0106.N0428.N0765.N1629

def d029922 (e α β hA hB a₀ b₀ : ℝ) (p : ℤ × ℤ) : ℂ :=
  ((hA * hB : ℝ) : ℂ) *
    _root_.GD.N0106.N0428.N0765.N1676.d028931 e α β (a₀ + (p.1 : ℝ) * hA, b₀ + (p.2 : ℝ) * hB)

def d029923 (E α β : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1676.d028930 α β * ((1 + E) / 11)

def d029924 (E α β : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1678.d029923 E α β * (1 + _root_.GD.N0106.N0428.N0765.N1676.d028912 α β ^ 2)

def d029925 (E α β : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1678.d029923 E α β * (2 * (1 + _root_.GD.N0106.N0428.N0765.N1676.d028912 α β))

def d029926 (h a₀ : ℝ) : ℤ → ℝ := _root_.GD.N0106.N0428.N0765.N1687.d029646 (3 / 2) 10 0 h a₀
def d029927 (j h b₀ : ℝ) : ℤ → ℝ := _root_.GD.N0106.N0428.N0765.N1687.d029646 5 5 j h b₀

def d029928 (h a₀ : ℝ) (k : ℤ) : ℝ := _root_.GD.N0106.N0428.N0765.N1687.d029651 (3 / 2) 10 0 h (a₀ + (k : ℝ) * h)
def d029929 (j h b₀ : ℝ) (k : ℤ) : ℝ := _root_.GD.N0106.N0428.N0765.N1687.d029651 5 5 j h (b₀ + (k : ℝ) * h)
def d029930 (h a₀ : ℝ) (N : ℕ) : ℝ := _root_.GD.N0106.N0428.N0765.N1687.d029652 (3 / 2) 10 0 h a₀ N
def d029931 (j h b₀ : ℝ) (N : ℕ) : ℝ := _root_.GD.N0106.N0428.N0765.N1687.d029652 5 5 j h b₀ N


def d029932 (E α β hA hB a₀ b₀ : ℝ) (NA NB : ℕ) (kA kB : ℤ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1678.d029924 E α β *
    (_root_.GD.N0106.N0428.N0765.N1678.d029930 hA a₀ NA * _root_.GD.N0106.N0428.N0765.N1678.d029929 2 hB b₀ kB + _root_.GD.N0106.N0428.N0765.N1678.d029928 hA a₀ kA * _root_.GD.N0106.N0428.N0765.N1678.d029931 2 hB b₀ NB) +
  _root_.GD.N0106.N0428.N0765.N1678.d029925 E α β *
    (_root_.GD.N0106.N0428.N0765.N1678.d029930 hA a₀ NA * _root_.GD.N0106.N0428.N0765.N1678.d029929 1 hB b₀ kB + _root_.GD.N0106.N0428.N0765.N1678.d029928 hA a₀ kA * _root_.GD.N0106.N0428.N0765.N1678.d029931 1 hB b₀ NB)

theorem d029933 {E α β : ℝ} (hE : 0 ≤ E)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1678.d029923 E α β :=
  mul_nonneg (_root_.GD.N0106.N0428.N0765.N1537.d021537 hw).le (by positivity)

theorem d029934 {E α β : ℝ} (hE : 0 ≤ E)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1678.d029924 E α β :=
  mul_nonneg (_root_.GD.N0106.N0428.N0765.N1678.d029933 hE hw) (by positivity)

theorem d029935 {E α β : ℝ} (hE : 0 ≤ E)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1678.d029925 E α β := by
  have hc := _root_.GD.N0106.N0428.N0765.N1675.d021512 hw
  exact mul_nonneg (_root_.GD.N0106.N0428.N0765.N1678.d029933 hE hw) (by positivity)

theorem d029936 {h : ℝ} (hh : 0 ≤ h) (a₀ : ℝ) (k : ℤ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1678.d029926 h a₀ k :=
  _root_.GD.N0106.N0428.N0765.N1687.d029654 (by norm_num) (by norm_num) hh 0 a₀ k

theorem d029937 {h : ℝ} (hh : 0 ≤ h) (j b₀ : ℝ) (k : ℤ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1678.d029927 j h b₀ k :=
  _root_.GD.N0106.N0428.N0765.N1687.d029654 (by norm_num) (by norm_num) hh j b₀ k

theorem d029938 {h : ℝ} (hh : 0 < h) (a₀ : ℝ) : Summable (_root_.GD.N0106.N0428.N0765.N1678.d029926 h a₀) :=
  _root_.GD.N0106.N0428.N0765.N1687.d029661 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hh a₀

theorem d029939 {j h : ℝ} (hjL : 0 < 5 + j) (hjR : 0 < 5 - j)
    (hh : 0 < h) (b₀ : ℝ) : Summable (_root_.GD.N0106.N0428.N0765.N1678.d029927 j h b₀) :=
  _root_.GD.N0106.N0428.N0765.N1687.d029661 (by norm_num) (by norm_num) hjL hjR hh b₀


theorem d029940 {e E α β hA hB : ℝ} (he : 0 ≤ e) (heE : e ≤ E)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (a₀ b₀ : ℝ) (p : ℤ × ℤ) :
    ‖_root_.GD.N0106.N0428.N0765.N1678.d029922 e α β hA hB a₀ b₀ p‖ ≤
      _root_.GD.N0106.N0428.N0765.N1678.d029924 E α β * _root_.GD.N0106.N0428.N0765.N1678.d029926 hA a₀ p.1 * _root_.GD.N0106.N0428.N0765.N1678.d029927 2 hB b₀ p.2 +
      _root_.GD.N0106.N0428.N0765.N1678.d029925 E α β * _root_.GD.N0106.N0428.N0765.N1678.d029926 hA a₀ p.1 * _root_.GD.N0106.N0428.N0765.N1678.d029927 1 hB b₀ p.2 := by
  rw [_root_.GD.N0106.N0428.N0765.N1678.d029922, norm_mul, Complex.norm_of_nonneg (mul_nonneg hhA.le hhB.le)]
  have hp := mul_le_mul_of_nonneg_left
    (_root_.GD.N0106.N0428.N0765.N1676.d028933 he heE α β hw (a₀ + (p.1 : ℝ) * hA, b₀ + (p.2 : ℝ) * hB))
    (mul_nonneg hhA.le hhB.le)
  apply hp.trans_eq
  unfold _root_.GD.N0106.N0428.N0765.N1678.d029924 _root_.GD.N0106.N0428.N0765.N1678.d029925 _root_.GD.N0106.N0428.N0765.N1678.d029923 _root_.GD.N0106.N0428.N0765.N1676.d028914 _root_.GD.N0106.N0428.N0765.N1676.d028913
    _root_.GD.N0106.N0428.N0765.N1521.d020868 _root_.GD.N0106.N0428.N0765.N1678.d029926 _root_.GD.N0106.N0428.N0765.N1678.d029927 _root_.GD.N0106.N0428.N0765.N1687.d029646 _root_.GD.N0106.N0428.N0765.N1687.d029645
  simp only [Prod.fst, Prod.snd, zero_mul, Real.exp_zero, one_mul]
  rw [show Real.exp (2 * (b₀ + (p.2 : ℝ) * hB)) =
      Real.exp (b₀ + (p.2 : ℝ) * hB) ^ 2 by rw [two_mul, Real.exp_add, pow_two]]
  ring


theorem d029941 {e α β hA hB : ℝ} (he : 0 ≤ e)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (a₀ b₀ : ℝ) :
    Summable (_root_.GD.N0106.N0428.N0765.N1678.d029922 e α β hA hB a₀ b₀) := by
  exact _root_.GD.N0106.N0428.N0765.N1629.d008250
    (_root_.GD.N0106.N0428.N0765.N1678.d029936 hhA.le a₀) (_root_.GD.N0106.N0428.N0765.N1678.d029937 hhB.le 2 b₀) (_root_.GD.N0106.N0428.N0765.N1678.d029937 hhB.le 1 b₀)
    (_root_.GD.N0106.N0428.N0765.N1678.d029938 hhA a₀)
    (_root_.GD.N0106.N0428.N0765.N1678.d029939 (by norm_num) (by norm_num) hhB b₀)
    (_root_.GD.N0106.N0428.N0765.N1678.d029939 (by norm_num) (by norm_num) hhB b₀)
    (_root_.GD.N0106.N0428.N0765.N1678.d029934 he hw) (_root_.GD.N0106.N0428.N0765.N1678.d029935 he hw)
    (_root_.GD.N0106.N0428.N0765.N1678.d029940 he le_rfl hhA hhB hw a₀ b₀)


theorem d029942 {e α β hA hB : ℝ} (he : 0 ≤ e)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (a₀ b₀ : ℝ) :
    Summable (fun p => ‖_root_.GD.N0106.N0428.N0765.N1678.d029922 e α β hA hB a₀ b₀ p‖) := by
  apply _root_.GD.N0106.N0428.N0765.N1629.d008250
    (_root_.GD.N0106.N0428.N0765.N1678.d029936 hhA.le a₀) (_root_.GD.N0106.N0428.N0765.N1678.d029937 hhB.le 2 b₀) (_root_.GD.N0106.N0428.N0765.N1678.d029937 hhB.le 1 b₀)
    (_root_.GD.N0106.N0428.N0765.N1678.d029938 hhA a₀)
    (_root_.GD.N0106.N0428.N0765.N1678.d029939 (by norm_num) (by norm_num) hhB b₀)
    (_root_.GD.N0106.N0428.N0765.N1678.d029939 (by norm_num) (by norm_num) hhB b₀)
    (_root_.GD.N0106.N0428.N0765.N1678.d029934 he hw) (_root_.GD.N0106.N0428.N0765.N1678.d029935 he hw)
  intro p
  simpa only [norm_norm] using _root_.GD.N0106.N0428.N0765.N1678.d029940 he le_rfl hhA hhB hw a₀ b₀ p

theorem d029943 {h : ℝ} (hh : 0 < h) (a₀ : ℝ) (k : ℤ) :
    (∑' i, _root_.GD.N0106.N0428.N0765.N1678.d029926 h a₀ i) ≤ _root_.GD.N0106.N0428.N0765.N1678.d029928 h a₀ k :=
  _root_.GD.N0106.N0428.N0765.N1687.d029666 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hh a₀ k

theorem d029944 {j h : ℝ} (hjL : 0 < 5 + j) (hjR : 0 < 5 - j)
    (hh : 0 < h) (b₀ : ℝ) (k : ℤ) :
    (∑' i, _root_.GD.N0106.N0428.N0765.N1678.d029927 j h b₀ i) ≤ _root_.GD.N0106.N0428.N0765.N1678.d029929 j h b₀ k :=
  _root_.GD.N0106.N0428.N0765.N1687.d029666 (by norm_num) (by norm_num) hjL hjR hh b₀ k

theorem d029945 {h : ℝ} (hh : 0 < h) (a₀ : ℝ) (N : ℕ) :
    (∑' i, _root_.GD.N0106.N0428.N0765.N1678.d029926 h a₀ i) - (∑ i ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 N, _root_.GD.N0106.N0428.N0765.N1678.d029926 h a₀ i) ≤ _root_.GD.N0106.N0428.N0765.N1678.d029930 h a₀ N :=
  _root_.GD.N0106.N0428.N0765.N1687.d029663 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hh a₀ N

theorem d029946 {j h : ℝ} (hjL : 0 < 5 + j) (hjR : 0 < 5 - j)
    (hh : 0 < h) (b₀ : ℝ) (N : ℕ) :
    (∑' i, _root_.GD.N0106.N0428.N0765.N1678.d029927 j h b₀ i) - (∑ i ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 N, _root_.GD.N0106.N0428.N0765.N1678.d029927 j h b₀ i) ≤
      _root_.GD.N0106.N0428.N0765.N1678.d029931 j h b₀ N :=
  _root_.GD.N0106.N0428.N0765.N1687.d029663 (by norm_num) (by norm_num) hjL hjR hh b₀ N




theorem d029947 {e E α β hA hB : ℝ} (he : 0 ≤ e) (heE : e ≤ E)
    (hhA : 0 < hA) (hhB : 0 < hB)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (a₀ b₀ : ℝ)
    (NA NB : ℕ) (kA kB : ℤ) :
    ‖(∑' p, _root_.GD.N0106.N0428.N0765.N1678.d029922 e α β hA hB a₀ b₀ p) -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB, _root_.GD.N0106.N0428.N0765.N1678.d029922 e α β hA hB a₀ b₀ p‖ ≤
        _root_.GD.N0106.N0428.N0765.N1678.d029932 E α β hA hB a₀ b₀ NA NB kA kB := by
  exact _root_.GD.N0106.N0428.N0765.N1629.d008251 (_root_.GD.N0106.N0428.N0765.N1687.d029647 NA) (_root_.GD.N0106.N0428.N0765.N1687.d029647 NB)
    (_root_.GD.N0106.N0428.N0765.N1678.d029936 hhA.le a₀) (_root_.GD.N0106.N0428.N0765.N1678.d029937 hhB.le 2 b₀) (_root_.GD.N0106.N0428.N0765.N1678.d029937 hhB.le 1 b₀)
    (_root_.GD.N0106.N0428.N0765.N1678.d029938 hhA a₀)
    (_root_.GD.N0106.N0428.N0765.N1678.d029939 (by norm_num) (by norm_num) hhB b₀)
    (_root_.GD.N0106.N0428.N0765.N1678.d029939 (by norm_num) (by norm_num) hhB b₀)
    (_root_.GD.N0106.N0428.N0765.N1678.d029934 (he.trans heE) hw)
    (_root_.GD.N0106.N0428.N0765.N1678.d029935 (he.trans heE) hw)
    (_root_.GD.N0106.N0428.N0765.N1678.d029940 he heE hhA hhB hw a₀ b₀)
    (_root_.GD.N0106.N0428.N0765.N1678.d029943 hhA a₀ kA)
    (_root_.GD.N0106.N0428.N0765.N1678.d029944 (by norm_num) (by norm_num) hhB b₀ kB)
    (_root_.GD.N0106.N0428.N0765.N1678.d029944 (by norm_num) (by norm_num) hhB b₀ kB)
    (_root_.GD.N0106.N0428.N0765.N1678.d029945 hhA a₀ NA)
    (_root_.GD.N0106.N0428.N0765.N1678.d029946 (by norm_num) (by norm_num) hhB b₀ NB)
    (_root_.GD.N0106.N0428.N0765.N1678.d029946 (by norm_num) (by norm_num) hhB b₀ NB)

theorem d029948 (α β : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1678.d029923 (1 / 50) α β = (51 / 550) * _root_.GD.N0106.N0428.N0765.N1676.d028930 α β := by
  unfold _root_.GD.N0106.N0428.N0765.N1678.d029923
  ring


theorem d029949 {e α β hA hB : ℝ}
    (he : e ∈ Set.Icc (0 : ℝ) (1 / 50)) (hhA : 0 < hA) (hhB : 0 < hB)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (a₀ b₀ : ℝ)
    (NA NB : ℕ) (kA kB : ℤ) :
    ‖(∑' p, _root_.GD.N0106.N0428.N0765.N1678.d029922 e α β hA hB a₀ b₀ p) -
      ∑ p ∈ _root_.GD.N0106.N0428.N0765.N1687.d029647 NA ×ˢ _root_.GD.N0106.N0428.N0765.N1687.d029647 NB, _root_.GD.N0106.N0428.N0765.N1678.d029922 e α β hA hB a₀ b₀ p‖ ≤
        _root_.GD.N0106.N0428.N0765.N1678.d029932 (1 / 50) α β hA hB a₀ b₀ NA NB kA kB :=
  _root_.GD.N0106.N0428.N0765.N1678.d029947 he.1 he.2 hhA hhB hw a₀ b₀ NA NB kA kB


theorem d029950 (E hA hB a₀ b₀ : ℝ) (NA NB : ℕ) (kA kB : ℤ) :
    _root_.GD.N0106.N0428.N0765.N1678.d029932 E 0 0 hA hB a₀ b₀ NA NB kA kB = ((1 + E) / 11) *
      ((13 / 4) * (_root_.GD.N0106.N0428.N0765.N1678.d029930 hA a₀ NA * _root_.GD.N0106.N0428.N0765.N1678.d029929 2 hB b₀ kB +
        _root_.GD.N0106.N0428.N0765.N1678.d029928 hA a₀ kA * _root_.GD.N0106.N0428.N0765.N1678.d029931 2 hB b₀ NB) +
      5 * (_root_.GD.N0106.N0428.N0765.N1678.d029930 hA a₀ NA * _root_.GD.N0106.N0428.N0765.N1678.d029929 1 hB b₀ kB +
        _root_.GD.N0106.N0428.N0765.N1678.d029928 hA a₀ kA * _root_.GD.N0106.N0428.N0765.N1678.d029931 1 hB b₀ NB)) := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1678.d029932, _root_.GD.N0106.N0428.N0765.N1678.d029924, _root_.GD.N0106.N0428.N0765.N1678.d029925, _root_.GD.N0106.N0428.N0765.N1678.d029923, _root_.GD.N0106.N0428.N0765.N1676.d028930,
    _root_.GD.N0106.N0428.N0765.N1537.d021528, _root_.GD.N0106.N0428.N0765.N1676.d028912, _root_.GD.N0106.N0428.N0765.N1675.d021511,
    _root_.GD.N0106.N0428.N0765.N1538.d021192, _root_.GD.N0106.N0428.N0765.N1538.d021231]
  ring

end
end GD.N0106.N0428.N0765.N1678

#print axioms _root_.GD.N0106.N0428.N0765.N1678.d029940
#print axioms _root_.GD.N0106.N0428.N0765.N1678.d029941
#print axioms _root_.GD.N0106.N0428.N0765.N1678.d029942
#print axioms _root_.GD.N0106.N0428.N0765.N1678.d029947
#print axioms _root_.GD.N0106.N0428.N0765.N1678.d029949
#print axioms _root_.GD.N0106.N0428.N0765.N1678.d029950
