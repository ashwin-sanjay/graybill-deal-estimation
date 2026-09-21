import GD.Module1217

set_option autoImplicit false
set_option warningAsError true

















open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0232.N0719.N0988

open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1314
  (d019699 d019698 d019708 d019709
   d019701 d019710 d019720
   d019721 d019722 d019727 d019728
   d019729 d019730)
open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0622

noncomputable section

abbrev d019777 (k : ℕ) := ℝ × (Fin k → Ioo (0 : ℝ) 1)

def d019778 (k : ℕ) : _root_.GD.N0232.N0719.N0988.d019777 k :=
  (0, fun _ => ⟨1 / 2, by constructor <;> norm_num⟩)

instance (k : ℕ) : Nonempty (_root_.GD.N0232.N0719.N0988.d019777 k) := ⟨_root_.GD.N0232.N0719.N0988.d019778 k⟩

variable {k d : ℕ}

def d019779 (block : Fin (d + 1) → Fin k)
    (q : _root_.GD.N0232.N0719.N0988.d019777 k) : _root_.GD.N0232.N0720.N1316.d004440 d := (q.1, fun i => q.2 (block i))

theorem d019780 (block : Fin (d + 1) → Fin k) :
    Continuous (_root_.GD.N0232.N0719.N0988.d019779 block) := by
  unfold _root_.GD.N0232.N0719.N0988.d019779
  fun_prop

@[simp] theorem d019781 (block : Fin (d + 1) → Fin k) :
    _root_.GD.N0232.N0719.N0988.d019779 block (_root_.GD.N0232.N0719.N0988.d019778 k) = _root_.GD.N0232.N0720.N1316.d004489 d := rfl

def d019782 (block : Fin (d + 1) → Fin k) (q : _root_.GD.N0232.N0719.N0988.d019777 k) (h : _root_.GD.N0232.N0720.N1341.d004417 d) : ℝ :=
  _root_.GD.N0232.N0720.N1316.d004469 (_root_.GD.N0232.N0719.N0988.d019779 block q) h

theorem d019783 (block : Fin (d + 1) → Fin k) (q : _root_.GD.N0232.N0719.N0988.d019777 k) :
    Continuous (_root_.GD.N0232.N0719.N0988.d019782 block q) := _root_.GD.N0232.N0720.N1316.d004483 (_root_.GD.N0232.N0719.N0988.d019779 block q)

theorem d019784 (block : Fin (d + 1) → Fin k) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    Continuous (fun q => _root_.GD.N0232.N0719.N0988.d019782 block q h) :=
  (_root_.GD.N0232.N0720.N1316.d004484 h).comp (_root_.GD.N0232.N0719.N0988.d019780 block)

theorem d019785 (block : Fin (d + 1) → Fin k) (q : _root_.GD.N0232.N0719.N0988.d019777 k) :
    ConvexOn ℝ univ (_root_.GD.N0232.N0719.N0988.d019782 block q) := _root_.GD.N0232.N0720.N1316.d004488 (_root_.GD.N0232.N0719.N0988.d019779 block q)

theorem d019786 (block : Fin (d + 1) → Fin k) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    _root_.GD.N0232.N0719.N0988.d019782 block (_root_.GD.N0232.N0719.N0988.d019778 k) h =
      (_root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 d) * _root_.GD.N0232.N0720.N1341.d004428 d) * ‖h‖ ^ 2 :=
  _root_.GD.N0232.N0720.N1316.d004491 h

section FinitePacket
variable {J : Type*} [Fintype J]

def d019787 (block : Fin (d + 1) → Fin k)
    (q : J → _root_.GD.N0232.N0719.N0988.d019777 k) : Option J → _root_.GD.N0232.N0720.N1316.d004440 d
  | none => _root_.GD.N0232.N0719.N0988.d019779 block (_root_.GD.N0232.N0719.N0988.d019778 k)
  | some j => _root_.GD.N0232.N0719.N0988.d019779 block (q j)

theorem d019788 (block : Fin (d + 1) → Fin k)
    (q : J → _root_.GD.N0232.N0719.N0988.d019777 k) (w : J → ℝ) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    _root_.GD.N0232.N0720.N1314.d019701 (_root_.GD.N0232.N0719.N0988.d019787 block q) (_root_.GD.N0232.N0720.N1314.d019720 w) h =
      _root_.GD.N0232.N0719.N0988.d019782 block (_root_.GD.N0232.N0719.N0988.d019778 k) h + ∑ j, w j * _root_.GD.N0232.N0719.N0988.d019782 block (q j) h := by
  simp [_root_.GD.N0232.N0720.N1314.d019701, Fintype.sum_option, _root_.GD.N0232.N0719.N0988.d019787, _root_.GD.N0232.N0720.N1314.d019720, _root_.GD.N0232.N0719.N0988.d019782]

theorem d019789 (block : Fin (d + 1) → Fin k)
    (q : J → _root_.GD.N0232.N0719.N0988.d019777 k) (w : J → ℝ) (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (hbayes : _root_.GD.N0230.N0622.d000607 univ (_root_.GD.N0232.N0719.N0988.d019782 block) (_root_.GD.N0232.N0719.N0988.d019778 k) q w h) :
    h = _root_.GD.N0232.N0720.N1314.d019708 (_root_.GD.N0232.N0719.N0988.d019787 block q) (_root_.GD.N0232.N0720.N1314.d019720 w)
      (_root_.GD.N0232.N0720.N1314.d019721 w hbayes.1) (_root_.GD.N0232.N0720.N1314.d019722 w) := by
  apply _root_.GD.N0232.N0720.N1314.d019710
  intro z
  rw [_root_.GD.N0232.N0719.N0988.d019788, _root_.GD.N0232.N0719.N0988.d019788]
  exact hbayes.2 z (mem_univ z)

end FinitePacket

def d019790 (k : ℕ) : ℕ → _root_.GD.N0232.N0719.N0988.d019777 k :=
  TopologicalSpace.denseSeq (_root_.GD.N0232.N0719.N0988.d019777 k)

theorem d019791 (k : ℕ) : DenseRange (_root_.GD.N0232.N0719.N0988.d019790 k) :=
  TopologicalSpace.denseRange_denseSeq (_root_.GD.N0232.N0719.N0988.d019777 k)

set_option maxHeartbeats 800000 in


theorem d019792
    (block : Fin (d + 1) → Fin k) (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (hadmissible : _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0719.N0988.d019782 block) h) :
    ∃ (p : ℕ → _root_.GD.N0232.N0720.N1341.d004417 d) (w : ∀ j, Fin j → ℝ),
      Tendsto p atTop (𝓝 h) ∧ (∀ j i, 0 ≤ w j i) ∧ ∀ j,
        p j =ᵐ[_root_.GD.N0232.N0720.N1341.d004416 d] fun u =>
          _root_.GD.N0232.N0720.N1314.d019699 (_root_.GD.N0232.N0719.N0988.d019787 block (fun i : Fin j => _root_.GD.N0232.N0719.N0988.d019790 k i))
              (_root_.GD.N0232.N0720.N1314.d019720 (w j)) u /
            _root_.GD.N0232.N0720.N1314.d019698 (_root_.GD.N0232.N0719.N0988.d019787 block (fun i : Fin j => _root_.GD.N0232.N0719.N0988.d019790 k i))
              (_root_.GD.N0232.N0720.N1314.d019720 (w j)) u := by
  have hadmissible' : _root_.GD.N0230.N0556.d000031
      (fun q (z : (univ : Set (_root_.GD.N0232.N0720.N1341.d004417 d))) => _root_.GD.N0232.N0719.N0988.d019782 block q z)
      ⟨h, mem_univ h⟩ := by
    rintro ⟨z, hweak, q, hstrict⟩
    exact hadmissible ⟨z.1, hweak, q, hstrict⟩
  have hscale : 0 < _root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 d) * _root_.GD.N0232.N0720.N1341.d004428 d :=
    mul_pos (_root_.GD.N0232.N0720.N1316.d004446 _) (_root_.GD.N0232.N0720.N1341.d004429 d)
  obtain ⟨p, w, hlimit, hcertificate⟩ :=
    _root_.GD.N0230.N0622.d000623
      (H := _root_.GD.N0232.N0720.N1341.d004417 d) (Θ := _root_.GD.N0232.N0719.N0988.d019777 k)
      (univ : Set (_root_.GD.N0232.N0720.N1341.d004417 d)) (_root_.GD.N0232.N0719.N0988.d019782 block) (_root_.GD.N0232.N0719.N0988.d019790 k)
      (_root_.GD.N0232.N0719.N0988.d019778 k) h (mem_univ h) isClosed_univ convex_univ
      (_root_.GD.N0232.N0719.N0988.d019783 block) (_root_.GD.N0232.N0719.N0988.d019785 block)
      (fun z _ => _root_.GD.N0232.N0719.N0988.d019784 block z) (_root_.GD.N0232.N0719.N0988.d019791 k)
      (_root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 d) * _root_.GD.N0232.N0720.N1341.d004428 d) 0 hscale
      (fun z _ => by simpa only [add_zero] using _root_.GD.N0232.N0719.N0988.d019786 block z)
      hadmissible' _root_.GD.N0232.N0720.N1314.d019727 _root_.GD.N0232.N0720.N1314.d019728 _root_.GD.N0232.N0720.N1314.d019729 _root_.GD.N0232.N0720.N1314.d019730
  refine ⟨p, w, hlimit, fun j => (hcertificate j).2.1, fun j => ?_⟩
  have heq := _root_.GD.N0232.N0719.N0988.d019789 block
    (fun i : Fin j => _root_.GD.N0232.N0719.N0988.d019790 k i) (w j) (p j) (hcertificate j).2
  rw [heq]
  exact _root_.GD.N0232.N0720.N1314.d019709 _ _ _ _

theorem d019793
    (block : Fin (d + 1) → Fin k) (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (hadmissible : _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0719.N0988.d019782 block) h) :
    ∃ (w : ∀ j, Fin j → ℝ) (ns : ℕ → ℕ),
      (∀ j i, 0 ≤ w j i) ∧ StrictMono ns ∧ ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d,
        Tendsto (fun j =>
          _root_.GD.N0232.N0720.N1314.d019699 (_root_.GD.N0232.N0719.N0988.d019787 block
              (fun i : Fin (ns j) => _root_.GD.N0232.N0719.N0988.d019790 k i)) (_root_.GD.N0232.N0720.N1314.d019720 (w (ns j))) u /
            _root_.GD.N0232.N0720.N1314.d019698 (_root_.GD.N0232.N0719.N0988.d019787 block
              (fun i : Fin (ns j) => _root_.GD.N0232.N0719.N0988.d019790 k i)) (_root_.GD.N0232.N0720.N1314.d019720 (w (ns j))) u)
          atTop (𝓝 (h u)) := by
  obtain ⟨p, w, hlimit, hw, hratio⟩ := _root_.GD.N0232.N0719.N0988.d019792 block h hadmissible
  obtain ⟨ns, hns, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hlimit).exists_seq_tendsto_ae
  refine ⟨w, ns, hw, hns, ?_⟩
  have hratios : ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d, ∀ j,
      p j u = _root_.GD.N0232.N0720.N1314.d019699
          (_root_.GD.N0232.N0719.N0988.d019787 block (fun i : Fin j => _root_.GD.N0232.N0719.N0988.d019790 k i))
          (_root_.GD.N0232.N0720.N1314.d019720 (w j)) u /
        _root_.GD.N0232.N0720.N1314.d019698
          (_root_.GD.N0232.N0719.N0988.d019787 block (fun i : Fin j => _root_.GD.N0232.N0719.N0988.d019790 k i))
          (_root_.GD.N0232.N0720.N1314.d019720 (w j)) u := ae_all_iff.mpr hratio
  filter_upwards [hpoint, hratios] with u hu huratio
  simpa only [huratio] using hu



def d019794 (sigma : Fin k → ℝ) : ℝ := 1 + ∑ i, sigma i ^ 2

theorem d019795 (sigma : Fin k → ℝ) : 0 < _root_.GD.N0232.N0719.N0988.d019794 sigma := by
  unfold _root_.GD.N0232.N0719.N0988.d019794
  positivity

def d019796 (sigma : Fin k → ℝ) : ℝ := Real.sqrt (_root_.GD.N0232.N0719.N0988.d019794 sigma)

theorem d019797 (sigma : Fin k → ℝ) : 0 < _root_.GD.N0232.N0719.N0988.d019796 sigma :=
  Real.sqrt_pos.mpr (_root_.GD.N0232.N0719.N0988.d019795 sigma)

theorem d019798 (sigma : Fin k → ℝ) : _root_.GD.N0232.N0719.N0988.d019796 sigma ^ 2 = _root_.GD.N0232.N0719.N0988.d019794 sigma :=
  Real.sq_sqrt (_root_.GD.N0232.N0719.N0988.d019795 sigma).le

def d019799 (mu : ℝ) (sigma : Fin k → ℝ) (hs : ∀ i, 0 < sigma i) :
    _root_.GD.N0232.N0719.N0988.d019777 k :=
  (mu / _root_.GD.N0232.N0719.N0988.d019796 sigma, fun i => ⟨sigma i ^ 2 / _root_.GD.N0232.N0719.N0988.d019794 sigma, by
    constructor
    · exact div_pos (sq_pos_of_pos (hs i)) (_root_.GD.N0232.N0719.N0988.d019795 sigma)
    · apply (div_lt_one (_root_.GD.N0232.N0719.N0988.d019795 sigma)).2
      have hle : sigma i ^ 2 ≤ ∑ j, sigma j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (sigma j)) (Finset.mem_univ i)
      unfold _root_.GD.N0232.N0719.N0988.d019794
      linarith⟩)

theorem d019800 (mu : ℝ) (sigma : Fin k → ℝ)
    (hs : ∀ i, 0 < sigma i) :
    _root_.GD.N0232.N0719.N0988.d019796 sigma * (_root_.GD.N0232.N0719.N0988.d019799 mu sigma hs).1 = mu := by
  exact mul_div_cancel₀ mu (_root_.GD.N0232.N0719.N0988.d019797 sigma).ne'

theorem d019801 (mu : ℝ) (sigma : Fin k → ℝ)
    (hs : ∀ i, 0 < sigma i) (i : Fin k) :
    _root_.GD.N0232.N0719.N0988.d019796 sigma ^ 2 * ((_root_.GD.N0232.N0719.N0988.d019799 mu sigma hs).2 i : ℝ) = sigma i ^ 2 := by
  rw [_root_.GD.N0232.N0719.N0988.d019798]
  exact mul_div_cancel₀ _ (_root_.GD.N0232.N0719.N0988.d019795 sigma).ne'

theorem d019802 (mu : ℝ) (sigma : Fin k → ℝ)
    (hs : ∀ i, 0 < sigma i) (i : Fin k) :
    _root_.GD.N0232.N0719.N0988.d019796 sigma * Real.sqrt ((_root_.GD.N0232.N0719.N0988.d019799 mu sigma hs).2 i : ℝ) = sigma i := by
  have hsq : (_root_.GD.N0232.N0719.N0988.d019796 sigma *
      Real.sqrt ((_root_.GD.N0232.N0719.N0988.d019799 mu sigma hs).2 i : ℝ)) ^ 2 = sigma i ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ((_root_.GD.N0232.N0719.N0988.d019799 mu sigma hs).2 i).2.1.le]
    exact _root_.GD.N0232.N0719.N0988.d019801 mu sigma hs i
  have hp : 0 ≤ _root_.GD.N0232.N0719.N0988.d019796 sigma *
      Real.sqrt ((_root_.GD.N0232.N0719.N0988.d019799 mu sigma hs).2 i : ℝ) :=
    mul_nonneg (_root_.GD.N0232.N0719.N0988.d019797 sigma).le (Real.sqrt_nonneg _)
  nlinarith [hs i]

end
end GD.N0232.N0719.N0988

#print axioms _root_.GD.N0232.N0719.N0988.d019792
#print axioms _root_.GD.N0232.N0719.N0988.d019793
#print axioms _root_.GD.N0232.N0719.N0988.d019802
