import Submission.DifferentialGeometry.Geometry.Neck.Spatial
import Submission.DifferentialGeometry.Topology.Manifold.ImmersionCriterion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

theorem SpatialNeck.isSmoothEmbedding_level
    (nk : SpatialNeck g eps p) {level : ℝ} (hlevel : |level| < eps⁻¹) :
    IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, level)) := by
  have hsource (q : Sphere 2) : (q, level) ∈ nk.map.source :=
    nk.domain ⟨mem_univ _, (abs_lt.mp hlevel).1, (abs_lt.mp hlevel).2⟩
  have hc : ContMDiff I2 I3 ∞ (fun q : Sphere 2 => nk.map (q, level)) :=
    contMDiffOn_univ.mp (nk.map.contMDiffOn_toFun.comp
      (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun q _ => hsource q))
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by decide) hc ?_,
    hc.continuous.isClosedEmbedding (fun q z h =>
      congrArg Prod.fst (nk.map.toPartialEquiv.injOn (hsource q) (hsource z) h)) |>.isEmbedding⟩
  intro q
  have hmd : nk.map.toOpenPartialHomeomorph.MDifferentiable IC I3 :=
    ⟨nk.map.contMDiffOn_toFun.mdifferentiableOn (by decide),
      nk.map.contMDiffOn_invFun.mdifferentiableOn (by decide)⟩
  change Function.Injective (mfderiv I2 I3 (nk.map ∘ fun z : Sphere 2 => (z, level)) q)
  have hinc : ContMDiff I2 IC ∞ (fun z : Sphere 2 => (z, level)) :=
    contMDiff_id.prodMk contMDiff_const
  rw [mfderiv_comp q (nk.map.mdifferentiableAt (by decide) (hsource q))
    (hinc.mdifferentiableAt (by decide)), mfderiv_prod_left]
  exact (hmd.mfderiv_injective (hsource q)).comp (fun _ _ h => congrArg Prod.fst h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.isSmoothEmbedding_level then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.isSmoothEmbedding_level"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.isSmoothEmbedding_level ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.SpatialNeck.isSmoothEmbedding_level

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
