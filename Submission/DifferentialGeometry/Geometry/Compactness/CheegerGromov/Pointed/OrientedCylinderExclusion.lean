import Submission.DifferentialGeometry.Topology.ProjectiveSpace.AntipodalCylinderOrientation
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotientSmoothModels
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private local instance orientedCylinderDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.orientedCylinderDimension target :: scope.openDecls } }

variable {X : PointedRiemannianSeq.{u, 0, 0} (I := ThreeModel)}
  {L : PointedRiemannianManifold.{u, 0, 0} (I := ThreeModel)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps X L subseq)

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth

private theorem productProjection_localDiffeomorph :
    IsLocalDiffeomorph CI CI ∞ SphereAntipodalQuotient.productProjection :=
  isLocalDiffeomorph_prod_real SphereAntipodalQuotient.proj
    SphereAntipodalQuotient.isLocalDiffeomorph_proj

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productProjection_localDiffeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.productProjection_localDiffeomorph target :: scope.openDecls } }

include Phi in
theorem pointedLimit_not_antipodalProduct_diffeomorph
    (orient : ∀ k, TangentOrientationSection (X.obj k).M) :
    ¬ Nonempty ((SphereAntipodalQuotient × ℝ) ≃ₘ⟮CI, ThreeModel⟯ L.M) := by
  rintro ⟨d⟩
  let q : S × ℝ → L.M := d ∘ SphereAntipodalQuotient.productProjection
  have hq : IsLocalDiffeomorph CI ThreeModel ∞ q :=
    isLocalDiffeomorph_comp d.isLocalDiffeomorph productProjection_localDiffeomorph
  have hcompact : IsCompact (Set.range (fun y : S => q (y, 0))) :=
    isCompact_range (hq.contMDiff.continuous.comp (continuous_id.prodMk continuous_const))
  obtain ⟨k, hk⟩ := Phi.source_exhausts.subset _ hcompact
  have hsource (y : S) : q (y, 0) ∈ (Phi.partialDiffeomorph k).source :=
    hk k le_rfl (Set.mem_range_self y)
  let f : S × ℝ → (X.obj (subseq k)).M := (Phi.partialDiffeomorph k) ∘ q
  have hf (y : S) : IsLocalDiffeomorphAt CI ThreeModel ∞ f (y, 0) :=
    IsLocalDiffeomorphAt.comp (P := (X.obj (subseq k)).M) ThreeModel (hq (y, 0))
      ((Phi.partialDiffeomorph k).isLocalDiffeomorphAt ThreeModel ThreeModel ∞ (hsource y))
  apply not_antipodal_product_localDiffeomorphAt_zero (orient (subseq k)) f hf
  intro p
  apply congrArg (fun z => (Phi.partialDiffeomorph k) (d z))
  exact (SphereAntipodalQuotient.productProjection_eq_iff p (-p.1, p.2)).mpr
    (Or.inr rfl) |>.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedLimit_not_antipodalProduct_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedLimit_not_antipodalProduct_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedLimit_not_antipodalProduct_diffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedLimit_not_antipodalProduct_diffeomorph

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
