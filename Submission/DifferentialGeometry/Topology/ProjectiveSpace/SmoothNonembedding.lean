import Submission.DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import Submission.DifferentialGeometry.Topology.Manifold.AmbientNormalOrientation
import Submission.DifferentialGeometry.Topology.Manifold.AmbientSectionExtension
import Submission.DifferentialGeometry.Topology.Manifold.TransverseFlow
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.AntipodalCylinderOrientation
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Manifold
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Analysis.ODE
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem not_cooriented_projective_embedding
    (f : SphereAntipodalQuotient → ThreeSpace)
    (C : CoorientedSmoothEmbeddingRealNormalAtlas (𝓡 2) ThreeModel ∞ f)
    (hf : Function.Injective f) : False := by
  obtain ⟨V, hsupp, _, htrans⟩ := C.exists_compactlySupported_transverseField hf
  let v : ∀ a : ThreeSpace, TangentSpace ThreeModel a := V
  have hv : ContMDiff ThreeModel ThreeModel.tangent ∞
      (fun a => (⟨a, v a⟩ : TangentBundle ThreeModel ThreeSpace)) := V.contMDiff
  let hc := exists_globalIntegralCurve_of_compactSupport v hv hsupp
  let F : SphereAntipodalQuotient × ℝ → ThreeSpace :=
    fun p => curveAt v hc (f p.1) p.2
  let q : S × ℝ → ThreeSpace := F ∘ SphereAntipodalQuotient.productProjection
  have hproj : IsLocalDiffeomorph CI CI ∞ SphereAntipodalQuotient.productProjection :=
    isLocalDiffeomorph_prod_real SphereAntipodalQuotient.proj
      SphereAntipodalQuotient.isLocalDiffeomorph_proj
  have hF (x : SphereAntipodalQuotient) :
      IsLocalDiffeomorphAt CI ThreeModel ∞ F (x, 0) :=
    C.toSmoothEmbeddingRealNormalAtlas.isLocalDiffeomorphAt_flowMap
      (by simp [ThreeSpace]) v hv hsupp x (htrans x)
  have hq (y : S) : IsLocalDiffeomorphAt CI ThreeModel ∞ q (y, 0) :=
    IsLocalDiffeomorphAt.comp (P := ThreeSpace) ThreeModel (hproj (y, 0))
      (hF (SphereAntipodalQuotient.proj y))
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  let os : DifferentialGeometry.Topology.Manifold.SmoothOrientation ThreeModel ThreeSpace :=
    DifferentialGeometry.Topology.Manifold.euclideanSmoothOrientation ThreeSpace
      (Orientation.reindex ℝ ThreeSpace (finCongr hdim).symm
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation))
  obtain ⟨om, _⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation
      ThreeModel os
  let om3 : DifferentialGeometry.ManifoldOrientation ThreeModel ThreeSpace 3 :=
    cast (congrArg
      (fun n => DifferentialGeometry.ManifoldOrientation ThreeModel ThreeSpace n) hdim) om
  let o : TangentOrientationSection ThreeSpace :=
    { orientation := om3.orientation
      locally_constant := om3.locally_constant }
  apply not_antipodal_product_localDiffeomorphAt_zero o q hq
  intro p
  apply congrArg F
  exact (SphereAntipodalQuotient.productProjection_eq_iff p (-p.1, p.2)).mpr
    (Or.inr rfl) |>.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_cooriented_projective_embedding
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_cooriented_projective_embedding target :: scope.openDecls } }

theorem SphereAntipodalQuotient.not_isSmoothEmbedding_euclideanThree
    (f : SphereAntipodalQuotient → EuclideanSpace ℝ (Fin 3)) :
    ¬ _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f := by
  intro hf
  let C := smoothEmbeddingRealNormalAtlasOfIsImmersionOfComplement hf.isEmbedding
    (isImmersionOfComplement_real_of_isSmoothEmbedding_finrank_succ hf (by simp))
  obtain ⟨O⟩ := C.toEmbeddingRealNormalAtlas.nonempty_coorientation_of_simplyConnected_ambient
    hf.isEmbedding (isCompact_range hf.contMDiff.continuous).isClosed
  exact not_cooriented_projective_embedding f (C.coorientedAtlas O) hf.isEmbedding.injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.not_isSmoothEmbedding_euclideanThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.not_isSmoothEmbedding_euclideanThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.not_isSmoothEmbedding_euclideanThree ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.not_isSmoothEmbedding_euclideanThree

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

section
set_option autoImplicit false

noncomputable section

open _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

theorem SphereAntipodalQuotient.not_range_subset_partialDiffeomorph_target
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (e : SphereAntipodalQuotient → M)
    (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (chart : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) M ∞) :
    ¬ _root_.Set.range e ⊆ chart.target := by
  intro hsub
  exact SphereAntipodalQuotient.not_isSmoothEmbedding_euclideanThree (chart.symm ∘ e)
    (DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph
      chart.symm he hsub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.not_range_subset_partialDiffeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.not_range_subset_partialDiffeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.not_range_subset_partialDiffeomorph_target ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereAntipodalQuotient.not_range_subset_partialDiffeomorph_target

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
