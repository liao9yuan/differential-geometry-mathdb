import Submission.DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Interval _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X]
  [FiniteDimensional Real X]

namespace timeH1

theorem exists_of_absolutelyContinuousOnInterval {T : Real} (f : Real → X)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hderiv : _root_.MeasureTheory.MemLp (_root_.deriv f) 2 (timeMeasure T)) :
    ∃ u : timeH1 X T,
      _root_.Set.EqOn u.toFun f (_root_.Set.Icc (0 : Real) T) ∧
        u.deriv =ᵐ[timeMeasure T] _root_.deriv f := by
  let u : timeH1 X T := mk (f 0) (hderiv.toLp (_root_.deriv f))
  have huDeriv : u.deriv =ᵐ[timeMeasure T] _root_.deriv f :=
    hderiv.coeFn_toLp
  refine ⟨u, ?_, huDeriv⟩
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hsub : Ι (0 : Real) t ⊆ _root_.Set.Icc (0 : Real) T := by
    rw [_root_.Set.uIoc_of_le ht.1]
    exact Ioc_subset_Icc_self.trans (_root_.Set.Icc_subset_Icc le_rfl ht.2)
  have hae : (fun s ↦ u.deriv s) =ᵐ[volume.restrict (Ι 0 t)]
      _root_.deriv f := by
    change ∀ᵐ s ∂volume.restrict (Ι 0 t), u.deriv s = _root_.deriv f s
    exact _root_.MeasureTheory.ae_mono (Measure.restrict_mono hsub le_rfl) huDeriv
  rw [toFun_apply, show u.initial = f 0 by rfl,
    intervalIntegral.integral_congr_ae_restrict hae]
  have hft : AbsolutelyContinuousOnInterval f 0 t :=
    hf.mono (by
      rw [_root_.Set.uIcc_of_le ht.1, _root_.Set.uIcc_of_le hT]
      exact _root_.Set.Icc_subset_Icc le_rfl ht.2)
  rw [hft.integral_deriv_eq_sub_vector]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.exists_of_absolutelyContinuousOnInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.exists_of_absolutelyContinuousOnInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.exists_of_absolutelyContinuousOnInterval ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.exists_of_absolutelyContinuousOnInterval

end timeH1

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
