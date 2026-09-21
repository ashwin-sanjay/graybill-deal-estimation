import GD.Module0948










open MeasureTheory

namespace GD
namespace N0232
namespace N0720
namespace N1215

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1483
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



theorem d014907 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    Measure.QuasiMeasurePreserving
      (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g • omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  refine ⟨?_, ?_⟩
  · simpa only [_root_.GD.N0232.N0720.N1214.d014259] using
      _root_.GD.N0107.d009026
        m n g.shift g.d009239 g.d009239
  · change
      (_root_.GD.N0232.N0720.N1080.d014171 m n _root_.GD.N0232.N0720.N1080.d014169).map
          (_root_.GD.N0107.d009024
            m n g.shift g.d009239 g.d009239) ≪
        _root_.GD.N0232.N0720.N1080.d014172 m n
    rw [_root_.GD.N0232.N0720.N1215.d014282 m n g _root_.GD.N0232.N0720.N1080.d014169]
    exact _root_.GD.N0232.N0720.N1080.d014173
      m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)



theorem d014908
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) := by
  exact (_root_.GD.N0232.N0720.N1214.d014267 m n
    (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hp)).trans
      (_root_.GD.N0232.N0720.N1215.d014288 m n hm hn g p hp).coeFn_toLp



theorem d014909
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    {a b : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hab : a =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] b) :
    _root_.GD.N0232.N0720.N1214.d014261 m n g a =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014261 m n g b := by
  have hpull :=
    (_root_.GD.N0232.N0720.N1215.d014907 m n g⁻¹).ae_eq_comp hab
  filter_upwards [hpull] with omega homega
  simp only [Function.comp_apply] at homega
  unfold _root_.GD.N0232.N0720.N1214.d014261
  rw [homega]


@[simp] theorem d014910
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1215.d014298 m n hm hn 1 p = p := by
  apply Subtype.ext
  change _root_.GD.N0232.N0720.N1215.d014289 m n hm hn 1 p.1 p.2 = p.1
  unfold _root_.GD.N0232.N0720.N1215.d014289
  calc
    MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014261 m n 1 (_root_.GD.N0232.N0720.N1214.d014265 m n p.1))
        (_root_.GD.N0232.N0720.N1215.d014288 m n hm hn 1 p.1 p.2) =
      MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n p.1)
        (_root_.GD.N0232.N0720.N1214.d014268 m n p.1) := by
          apply MemLp.toLp_congr
          exact Filter.Eventually.of_forall fun omega ↦
            congrFun (_root_.GD.N0232.N0720.N1214.d014263 m n (_root_.GD.N0232.N0720.N1214.d014265 m n p.1)) omega
    _ = p.1 := _root_.GD.N0232.N0720.N1214.d014269 m n p.1


theorem d014911
    (g h : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn h p) =
      _root_.GD.N0232.N0720.N1215.d014298 m n hm hn (g * h) p := by
  apply Subtype.ext
  unfold _root_.GD.N0232.N0720.N1215.d014298
  change
    _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g
        (_root_.GD.N0232.N0720.N1215.d014289 m n hm hn h p.1 p.2)
        (_root_.GD.N0232.N0720.N1215.d014297 m n hm hn h p.1 p.2) =
      _root_.GD.N0232.N0720.N1215.d014289 m n hm hn (g * h) p.1 p.2
  unfold _root_.GD.N0232.N0720.N1215.d014289
  apply MemLp.toLp_congr
  have hrepresentative :=
    _root_.GD.N0232.N0720.N1215.d014908 m n hm hn h p.1 p.2
  have houter := _root_.GD.N0232.N0720.N1215.d014909 m n g hrepresentative
  exact houter.trans (Filter.Eventually.of_forall fun omega ↦
    congrFun (_root_.GD.N0232.N0720.N1214.d014264 m n g h (_root_.GD.N0232.N0720.N1214.d014265 m n p.1)) omega)




@[reducible] noncomputable def d014912 :
    MulAction _root_.GD.N0232.N0719.N0946.d009229 (_root_.GD.N0232.N0720.N1080.d014187 m n hm hn) where
  smul := _root_.GD.N0232.N0720.N1215.d014298 m n hm hn
  one_smul := _root_.GD.N0232.N0720.N1215.d014910 m n hm hn
  mul_smul g h p := (_root_.GD.N0232.N0720.N1215.d014911 m n hm hn g h p).symm



noncomputable def d014913 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1080.d014187 m n hm hn ≃ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn where
  toFun := _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
  invFun := _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g⁻¹
  left_inv p := by
    rw [_root_.GD.N0232.N0720.N1215.d014911]
    simp
  right_inv p := by
    rw [_root_.GD.N0232.N0720.N1215.d014911]
    simp




@[simp] theorem d014914
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1025.d014316 m n hm hn 1 p = p := by
  simp [_root_.GD.N0232.N0720.N1025.d014316]


theorem d014915
    (g h : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn h p) =
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn (g * h) p := by
  simp only [_root_.GD.N0232.N0720.N1025.d014317, Equiv.symm_apply_apply]
  rw [_root_.GD.N0232.N0720.N1215.d014911]


@[reducible] noncomputable def d014916 :
    MulAction _root_.GD.N0232.N0719.N0946.d009229 (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) where
  smul := _root_.GD.N0232.N0720.N1025.d014316 m n hm hn
  one_smul := _root_.GD.N0232.N0720.N1215.d014914 m n hm hn
  mul_smul g h p := (_root_.GD.N0232.N0720.N1215.d014915 m n hm hn g h p).symm



noncomputable def d014917 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1025.d014304 m n hm hn ≃ₜ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn where
  toFun := _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g
  invFun := _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g⁻¹
  left_inv p := by
    rw [_root_.GD.N0232.N0720.N1215.d014915]
    simp
  right_inv p := by
    rw [_root_.GD.N0232.N0720.N1215.d014915]
    simp
  continuous_toFun := _root_.GD.N0232.N0720.N1483.d014904 m n hm hn g
  continuous_invFun := _root_.GD.N0232.N0720.N1483.d014904 m n hm hn g⁻¹

#print axioms _root_.GD.N0232.N0720.N1215.d014907
#print axioms _root_.GD.N0232.N0720.N1215.d014908
#print axioms _root_.GD.N0232.N0720.N1215.d014909
#print axioms _root_.GD.N0232.N0720.N1215.d014910
#print axioms _root_.GD.N0232.N0720.N1215.d014911
#print axioms _root_.GD.N0232.N0720.N1215.d014912
#print axioms _root_.GD.N0232.N0720.N1215.d014913
#print axioms _root_.GD.N0232.N0720.N1215.d014914
#print axioms _root_.GD.N0232.N0720.N1215.d014915
#print axioms _root_.GD.N0232.N0720.N1215.d014916
#print axioms _root_.GD.N0232.N0720.N1215.d014917

end
end N1215
end N0720
end N0232
end GD
