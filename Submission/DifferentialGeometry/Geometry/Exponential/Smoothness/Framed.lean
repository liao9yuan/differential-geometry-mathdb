import Submission.DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative
import Submission.DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Framed
import Submission.DifferentialGeometry.Geometry.Exponential.Smoothness.Domain

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

universe u uE uH

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

theorem contMDiffAt_framedExpMap
    (g : SmoothRiemannianMetric I M) (p : M) {z : E}
    (hz : normalFrame (I := I) g p z ∈ expDomain (I := I) g p) :
    ContMDiffAt 𝓘(Real, E) I ∞ (framedExpMap (I := I) g p) z := by
  let L : E →L[Real] E :=
    (normalFrame (I := I) g p).toContinuousLinearMap
  have hframe : ContMDiffAt 𝓘(Real, E) 𝓘(Real, E) ∞
      (L : E → E) z := L.contDiff.contMDiff.contMDiffAt
  have hexp := contMDiffAt_expMap (I := I) g p hz
  exact hexp.comp z hframe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.contMDiffAt_framedExpMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.contMDiffAt_framedExpMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.contMDiffAt_framedExpMap ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.contMDiffAt_framedExpMap

theorem mfderiv_framedExpMap
    (g : SmoothRiemannianMetric I M) (p : M) {z : E}
    (hz : normalFrame (I := I) g p z ∈ expDomain (I := I) g p) :
    mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z =
      (mfderiv 𝓘(Real, E) I
        (fun u : E => expMap (I := I) g p
          (show TangentSpace I p from u))
        (show E from normalFrame (I := I) g p z)).comp
          (show E →L[Real] E from (normalFrame (I := I) g p).toContinuousLinearMap) := by
  let L : E →L[Real] E :=
    (normalFrame (I := I) g p).toContinuousLinearMap
  let F : E → M := fun u =>
    expMap (I := I) g p (show TangentSpace I p from u)
  have hF : MDifferentiableAt 𝓘(Real, E) I F (L z) :=
    (contMDiffAt_expMap (I := I) g p hz).mdifferentiableAt (by decide)
  have hL : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, E)
      (fun w : E => L w) z :=
    L.contMDiff.mdifferentiableAt one_ne_zero
  have hchain := mfderiv_comp
    (I := 𝓘(Real, E)) (I' := 𝓘(Real, E)) (I'' := I)
    z hF hL
  have hLderiv :
      mfderiv 𝓘(Real, E) 𝓘(Real, E) (fun w : E => L w) z = L := by
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rw [hLderiv] at hchain
  change mfderiv 𝓘(Real, E) I (F ∘ fun w : E => L w) z =
    (mfderiv 𝓘(Real, E) I F (L z)).comp L
  exact hchain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.mfderiv_framedExpMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.mfderiv_framedExpMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.mfderiv_framedExpMap ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.mfderiv_framedExpMap

theorem isLocalDiffeomorphOn_framedExpMap
    (g : SmoothRiemannianMetric I M) (p : M) {U : Set E}
    (hU : IsOpen U)
    (hdom : ∀ z ∈ U,
      normalFrame (I := I) g p z ∈ expDomain (I := I) g p)
    (hinj : ∀ z ∈ U, Function.Injective
      (mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z)) :
    IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) U := by
  have hsmooth : ContMDiffOn 𝓘(Real, E) I ∞
      (framedExpMap (I := I) g p) U := by
    intro z hz
    exact (contMDiffAt_framedExpMap (I := I) g p (hdom z hz)).contMDiffWithinAt
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  apply hsmooth.isLocalDiffeomorphOn_of_isInvertible_mfderiv hU (by simp)
  intro z hz
  have hDinj := hinj z hz
  have hDsurj : Function.Surjective
      (mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z) :=
    LinearMap.surjective_of_injective hDinj
  let D : E ≃L[Real] E :=
    ContinuousLinearEquiv.ofBijective
      (mfderiv 𝓘(Real, E) I (framedExpMap (I := I) g p) z)
      (LinearMap.ker_eq_bot.mpr hDinj)
      (LinearMap.range_eq_top.mpr hDsurj)
  have hDinv :
      (mfderiv 𝓘(Real, E) I
        (framedExpMap (I := I) g p) z).IsInvertible := by
    refine ⟨D, ?_⟩
    rfl
  exact hDinv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.isLocalDiffeomorphOn_framedExpMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.isLocalDiffeomorphOn_framedExpMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.isLocalDiffeomorphOn_framedExpMap ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.isLocalDiffeomorphOn_framedExpMap

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
