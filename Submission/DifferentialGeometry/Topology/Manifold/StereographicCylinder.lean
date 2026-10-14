import Submission.DifferentialGeometry.Topology.Manifold.RoundCylinderOrientation
import Submission.DifferentialGeometry.Topology.Manifold.OpenEmbedding
import Submission.DifferentialGeometry.Geometry.Metric.PolarCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.E4 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S2 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.S3 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.IC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

def stereographicCylinderMap (v : S3) (q : S2 × ℝ) : S3 :=
  (stereographic' 3 v).symm (exponentialPolarMap q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicCylinderMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicCylinderMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicCylinderMap ``Submission.DifferentialGeometry.Topology.Manifold.stereographicCylinderMap

theorem stereographicCylinderMap_coordinates (v : S3) (q : S2 × ℝ) :
    stereographic' 3 v (stereographicCylinderMap v q) = Real.exp q.2 • (q.1 : E3) :=
  (stereographic' 3 v).right_inv (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_coordinates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_coordinates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_coordinates ``Submission.DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_coordinates

theorem stereographicCylinderMap_coordinate_norm (v : S3) (q : S2 × ℝ) :
    ‖stereographic' 3 v (stereographicCylinderMap v q)‖ = Real.exp q.2 := by
  rw [stereographicCylinderMap_coordinates, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_eq_of_mem_sphere, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_coordinate_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_coordinate_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_coordinate_norm ``Submission.DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_coordinate_norm

private theorem stereo_inverse_local (v : S3) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (stereographic' 3 v).symm := by
  have he : chartAt E3 (-v) = stereographic' 3 v := by
    change stereographic' 3 (-(-v)) = stereographic' 3 v
    rw [neg_neg]
  let D : PartialDiffeomorph (𝓡 3) (𝓡 3) S3 E3 ∞ :=
    { toPartialEquiv := (chartAt E3 (-v)).toPartialEquiv
      open_source := (chartAt E3 (-v)).open_source
      open_target := (chartAt E3 (-v)).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  intro x
  have h := PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ D.symm
    (show x ∈ D.target from by change x ∈ (chartAt E3 (-v)).target; rw [he]; simp)
  change IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (chartAt E3 (-v)).symm x at h
  simpa only [he] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.stereo_inverse_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.stereo_inverse_local target :: scope.openDecls } }

theorem stereographicCylinderMap_isLocalDiffeomorph (v : S3) :
    IsLocalDiffeomorph IC (𝓡 3) ∞ (stereographicCylinderMap v) := by
  have hp : IsLocalDiffeomorph IC (𝓡 3) ∞ exponentialPolarMap :=
    isLocalDiffeomorph_of_injective_mfderiv _ exponentialPolarMap_contMDiff
      (fun q => (exponentialPolarMap_mfderiv_bijective q).injective) (by simp)
  intro q
  exact (hp q).comp (𝓡 3) S3 (stereo_inverse_local v (exponentialPolarMap q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_isLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_isLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_isLocalDiffeomorph ``Submission.DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_isLocalDiffeomorph

private theorem exponential_injective : _root_.Function.Injective exponentialPolarMap := by
  intro a b h
  have hn := congrArg _root_.Norm.norm h
  change ‖euclideanPolarMap (positiveCylinderReparametrization a)‖ =
    ‖euclideanPolarMap (positiveCylinderReparametrization b)‖ at hn
  rw [euclideanPolarMap_norm_of_pos (Real.exp_pos a.2),
    euclideanPolarMap_norm_of_pos (Real.exp_pos b.2)] at hn
  have ht : a.2 = b.2 := Real.exp_injective hn
  apply Prod.ext _ ht
  apply Subtype.ext
  change Real.exp a.2 • (a.1 : E3) = Real.exp b.2 • (b.1 : E3) at h
  rw [ht] at h
  exact (smul_right_injective E3 (Real.exp_ne_zero b.2)) h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.exponential_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.exponential_injective target :: scope.openDecls } }

theorem stereographicCylinderMap_isOpenEmbedding (v : S3) :
    _root_.Topology.IsOpenEmbedding (stereographicCylinderMap v) := by
  have hi : _root_.Topology.IsOpenEmbedding (stereographic' 3 v).symm :=
    (stereographic' 3 v).symm.isOpenEmbedding (by simp)
  exact .of_continuous_injective_isOpenMap
    (stereographicCylinderMap_isLocalDiffeomorph v).contMDiff.continuous
    (hi.injective.comp exponential_injective)
    (stereographicCylinderMap_isLocalDiffeomorph v).isOpenMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_isOpenEmbedding

theorem stereographicCylinderMap_ne_pole (v : S3) (q : S2 × ℝ) :
    stereographicCylinderMap v q ≠ v := by
  have h := (stereographic' 3 v).map_target
    (show exponentialPolarMap q ∈ (stereographic' 3 v).target by simp)
  simpa only [stereographicCylinderMap, stereographic'_source, _root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_ne_pole then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_ne_pole"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_ne_pole ``Submission.DifferentialGeometry.Topology.Manifold.stereographicCylinderMap_ne_pole
end DifferentialGeometry.Topology.Manifold
