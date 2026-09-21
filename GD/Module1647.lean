import GD.Module1639
import GD.Module1640
import GD.Module1644
import GD.Module1641
import GD.Module1645

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GD.N0079

noncomputable section

open _root_.GD.N0074
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N1012
open _root_.GD.N0079.N0319 _root_.GD.N0079.N0322
open _root_.GD.N0230.N0642
open _root_.GD.N0230.N0642.d001800

structure d028059 : Prop where
  projection_unique : ∃! P : _root_.GD.N0074.d023618, _root_.GD.N0074.d027962 P
  comparisons : ∀ (k : ℕ) (n : Fin k → ℕ), (∀ i, 2 ≤ n i) →
    ∀ d : _root_.GD.N0074.d023610 k n,
      (_root_.GD.N0079.N0319.d027994 k n d ↔ _root_.GD.N0079.N0319.d027977 k n d) ∧
      (_root_.GD.N0079.N0322.d028031 k n d ↔ _root_.GD.N0079.N0319.d027977 k n d) ∧
      (_root_.GD.N0079.N0319.d027995 k n d ↔ _root_.GD.N0079.N0319.d027978 k n d) ∧
      (_root_.GD.N0079.N0322.d028032 k n d ↔ _root_.GD.N0079.N0319.d027978 k n d)
  finite_comparisons : ∀ (k : ℕ) (n : Fin k → ℕ) (d : _root_.GD.N0074.d023612 k n),
      (_root_.GD.N0079.N0319.d027989 k n d.val ↔ _root_.GD.N0079.N0319.d027977 k n d.val) ∧
      (_root_.GD.N0079.N0319.d027990 k n d.val ↔ _root_.GD.N0079.N0319.d027978 k n d.val)
  admissible_summary : ∀ (k : ℕ) (n : Fin k → ℕ), (∀ i, 2 ≤ n i) →
    ∀ d : _root_.GD.N0074.d023610 k n, _root_.GD.N0079.N0319.d027977 k n d →
      ∃ h : _root_.GD.N0074.N0308.d022069 k → ℝ, Measurable h ∧
        ∀ θ, (d : _root_.GD.N0232.N0719.N0900.d009094 k n → ℝ) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k n θ]
          h ∘ _root_.GD.N0074.N0308.d022071 k n
  strict_residual : ∀ (k : ℕ) (n : Fin k → ℕ) (d : _root_.GD.N0074.d023610 k n),
    ¬ _root_.GD.N0079.N0319.d027973 k n d →
      _root_.GD.N0232.N0719.N0859.d010821 k n (_root_.GD.N0232.N0719.N0859.d010810 k) (_root_.GD.N0232.N0719.N1012.d011399 k n d) <
        _root_.GD.N0232.N0719.N0859.d010821 k n (_root_.GD.N0232.N0719.N0859.d010810 k) d
  strict_transport : ∀ (k : ℕ) (n : Fin k → ℕ), (∀ i, 2 ≤ n i) →
    ∀ (d e : _root_.GD.N0074.d023610 k n) (θ : _root_.GD.N0232.N0719.N0859.d010809 k), _root_.GD.N0232.N0719.N0859.d010821 k n θ e < _root_.GD.N0232.N0719.N0859.d010821 k n θ d →
      _root_.GD.N0232.N0719.N0859.d010821 k n θ (_root_.GD.N0232.N0719.N1012.d011399 k n e) < _root_.GD.N0232.N0719.N0859.d010821 k n θ d
  projection_covariance : ∀ (k : ℕ) (n : Fin k → ℕ) (hn : ∀ i, 2 ≤ n i)
    (a : ℝ) (ha : 0 < a) (b : ℝ) (d : _root_.GD.N0074.d023612 k n),
      (_root_.GD.N0074.d023620 k n hn (_root_.GD.N0074.d027955 k n b a ha d)).val =
        _root_.GD.N0074.d027955 k n b a ha (_root_.GD.N0074.d023620 k n hn d).val
  barycenter_covariance : ∀ (X : Type) [MeasurableSpace X]
    (q : _root_.GD.N0230.N0642.d001800 X) (T : X → X) (a b : ℝ),
    (∀ x, q.kernel (T x) = (q.kernel x).map (fun y : ℝ => a * y + b)) →
      ∀ x, q.d001802 (T x) = a * q.d001802 x + b
  kernel_summary : ∀ (k : ℕ) (n : Fin k → ℕ) (hn : ∀ i, 2 ≤ n i)
    (κ : Kernel (_root_.GD.N0232.N0719.N0900.d009094 k n) ℝ) [IsMarkovKernel κ]
    (hf : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k n θ) θ.location ≠ ∞),
    ∃ h : _root_.GD.N0074.N0308.d022069 k → ℝ, Measurable h ∧
      (∀ θ, MemLp (h ∘ _root_.GD.N0074.N0308.d022071 k n) 2 (_root_.GD.N0232.N0719.N0859.d010812 k n θ)) ∧
      ∀ θ, _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k n θ) θ.location =
        _root_.GD.N0230.N0642.d001800.d001817 (_root_.GD.N0232.N0719.N0859.d010812 k n θ) θ.location (h ∘ _root_.GD.N0074.N0308.d022071 k n) +
        (∫⁻ x, ENNReal.ofReal
          (((_root_.GD.N0079.N0321.d028006 k n κ hf).val x -
            (_root_.GD.N0074.d023620 k n hn (_root_.GD.N0079.N0321.d028006 k n κ hf)).val.val x)
              ^ 2) ∂_root_.GD.N0232.N0719.N0859.d010812 k n θ) +
        (_root_.GD.N0230.N0642.d001800.d001834 κ 0).d001813 (_root_.GD.N0232.N0719.N0859.d010812 k n θ)
  kernel_projection_covariance : ∀ (k : ℕ) (n : Fin k → ℕ) (hn : ∀ i, 2 ≤ n i)
    (κ : Kernel (_root_.GD.N0232.N0719.N0900.d009094 k n) ℝ) [IsMarkovKernel κ]
    (hf : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0719.N0859.d010812 k n θ) θ.location ≠ ∞)
    (b a : ℝ) (ha : 0 < a),
    (∀ᵐ x ∂_root_.GD.N0232.N0719.N0859.d010813 k n,
      κ (_root_.GD.N0232.N0719.N0900.d009095 k n b a x) =
      Measure.map (fun z : ℝ => b + a * z) (κ x)) →
    _root_.GD.N0074.d027955 k n b a ha
      (_root_.GD.N0074.d023620 k n hn (_root_.GD.N0079.N0321.d028006 k n κ hf)).val =
      (_root_.GD.N0074.d023620 k n hn (_root_.GD.N0079.N0321.d028006 k n κ hf)).val

theorem d028060 : _root_.GD.N0079.d028059 where
  projection_unique := _root_.GD.N0074.d027968
  comparisons k n hn d :=
    ⟨_root_.GD.N0079.N0319.d027996 k n hn d, _root_.GD.N0079.N0322.d028036 k n d,
      _root_.GD.N0079.N0319.d027997 k n hn d, _root_.GD.N0079.N0322.d028037 k n d⟩
  finite_comparisons k n d :=
    ⟨(_root_.GD.N0079.N0319.d027992 k n d).trans (_root_.GD.N0079.N0319.d027981 k n d.val).symm,
      (_root_.GD.N0079.N0319.d027993 k n d).trans (_root_.GD.N0079.N0319.d027982 k n d.val).symm⟩
  admissible_summary := _root_.GD.N0079.N0319.d027999
  strict_residual := _root_.GD.N0079.N0319.d028000
  strict_transport k n hn _ e θ h :=
    (_root_.GD.N0232.N0719.N1012.d011407 k n hn θ e).trans_lt h
  projection_covariance := _root_.GD.N0074.d027964
  barycenter_covariance _ _ q T a b h := _root_.GD.N0079.N0320.d028015 q T a b h
  kernel_summary := _root_.GD.N0079.N0321.d028009
  kernel_projection_covariance := _root_.GD.N0079.N0320.d028026

end
end GD.N0079

#print axioms _root_.GD.N0079.d028060
