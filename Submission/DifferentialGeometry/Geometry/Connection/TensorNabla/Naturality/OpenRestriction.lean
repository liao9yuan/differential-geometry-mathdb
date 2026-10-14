import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.InducedConnection
import Submission.DifferentialGeometry.Bundle.TangentOpenRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Topology _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [CompleteSpace E] in
theorem tensor0SModelAt_opens (s : ℕ) {V : _root_.TopologicalSpace.Opens M} (p x : V)
    (hxp : (x : M) ∈ (chartAt H (p : M)).source)
    (A : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      s (x : M)) :
    TensorLieDeriv.tensor0SModelAt (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := V) s p x
        (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x)
          (Tensor0SBundle.Tensor0SSpace.toModel A))
      = TensorLieDeriv.tensor0SModelAt (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
          s (p : M) (x : M) A := by
  have hsrc : x ∈ (chartAt H p).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hxp
  have hL : (_root_.FiberBundle.trivializationAt E (TangentSpace I (M := V)) p).symmL ℝ x
      = (tangentBundleCore I V).coordChange (achart H p) (achart H x) x :=
    TangentBundle.symmL_trivializationAt_eq_core hsrc
  have hR : (_root_.FiberBundle.trivializationAt E (TangentSpace I (M := M)) (p : M)).symmL ℝ (x : M)
      = (tangentBundleCore I M).coordChange (achart H (p : M)) (achart H (x : M)) (x : M) :=
    TangentBundle.symmL_trivializationAt_eq_core hxp
  change ContinuousMultilinearMap.compContinuousLinearMap
      (Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x
        (Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x)
          (Tensor0SBundle.Tensor0SSpace.toModel A)))
      (fun _ => (_root_.FiberBundle.trivializationAt E (TangentSpace I (M := V)) p).symmL ℝ x)
    = ContinuousMultilinearMap.compContinuousLinearMap
      (Tensor0SBundle.tensor0SSpaceFiberContinuousLinearEquiv (I := I) s (x : M) A)
      (fun _ => (_root_.FiberBundle.trivializationAt E (TangentSpace I (M := M)) (p : M)).symmL ℝ (x : M))
  rw [hL, hR, tangentCoordChange_opens (I := I) p x x hxp]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor0SModelAt_opens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor0SModelAt_opens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor0SModelAt_opens ``Submission.DifferentialGeometry.tensor0SModelAt_opens

end DifferentialGeometry

namespace DifferentialGeometry

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Topology _root_.TopologicalSpace
open scoped _root_.Manifold _root_.ContDiff
noncomputable def restrictOpen0S {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (s : ℕ) [IsManifold I 1 M] {V : _root_.TopologicalSpace.Opens M}
    (δ : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := V) (n := (∞ : WithTop ℕ∞)) s :=
  letI := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := V) s
  { toFun := fun x =>
      Tensor0SBundle.Tensor0SSpace.ofModel (I := I) (x := x)
        (Tensor0SBundle.Tensor0SSpace.toModel (δ (x : M)))
    contMDiff_toFun := by
      intro x₀
      rw [Bundle.contMDiffAt_section]
      have hM := δ.contMDiff_toFun.contMDiffAt (x := (x₀ : M))
      rw [Bundle.contMDiffAt_section] at hM
      have hval : ContMDiffAt I I (∞ : WithTop ℕ∞) (Subtype.val : V → M) x₀ :=
        (contMDiff_subtype_val (I := I) (U := V)).contMDiffAt
      have hcomp := hM.comp x₀ hval
      refine hcomp.congr_of_eventuallyEq ?_
      have hnb : {x : V | (x : M) ∈ (chartAt H (x₀ : M)).source} ∈ 𝓝 x₀ :=
        ((chartAt H (x₀ : M)).open_source.preimage continuous_subtype_val).mem_nhds
          (mem_chart_source H (x₀ : M))
      filter_upwards [hnb] with x hx
      exact tensor0SModelAt_opens s x₀ x hx (δ (x : M)) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.restrictOpen0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.restrictOpen0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.restrictOpen0S ``Submission.DifferentialGeometry.restrictOpen0S

end DifferentialGeometry
