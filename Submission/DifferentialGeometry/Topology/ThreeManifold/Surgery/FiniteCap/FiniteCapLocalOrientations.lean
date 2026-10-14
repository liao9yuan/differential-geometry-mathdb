import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeighborhoodSmooth
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreInteriorSmooth
import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.IC target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
local notation "LocalOrientationQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCapRadialCoordinateMap (b : ι × Bool) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    finiteCapNeighborhoodOpens hL hδ f hf hdisj b → E3 := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact Subtype.val ∘ finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap

theorem finiteCapRadialCoordinateMap_eq_openChart (b : ι × Bool)
    (p : finiteCapNeighborhoodOpens hL hδ f hf hdisj b) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b p =
      finiteCapOpenChart hL hδ f hf hdisj b p.val := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact (finiteCapOpenChart_apply hL hδ f hf hdisj b p).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap_eq_openChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap_eq_openChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap_eq_openChart ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap_eq_openChart

theorem finiteCapRadialCoordinateMap_contMDiff (b : ι × Bool) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff (𝓡 3) (𝓡 3) ∞ (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact (contMDiff_subtype_val (I := 𝓡 3) (U := finiteCapRadialBall (L := L) (precision := precision) b)).comp
    (finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap_contMDiff

theorem finiteCapRadialCoordinateMap_mfderiv_bijective (b : ι × Bool)
    (p : finiteCapNeighborhoodOpens hL hδ f hf hdisj b) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Bijective (mfderiv (𝓡 3) (𝓡 3) (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b) p) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let V := finiteCapRadialBall (L := L) (precision := precision) b
  let D := finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b
  exact bijective_mfderiv_comp (𝓡 3) (𝓡 3) (𝓡 3) D (Subtype.val : V → E3) D.contMDiff
    (contMDiff_subtype_val (I := 𝓡 3) (U := V))
    (fun q => (D.mfderivToContinuousLinearEquiv (by simp) q).bijective)
    (bijective_mfderiv_open_val (𝓡 3) V) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialCoordinateMap_mfderiv_bijective

def finiteCapNeighborhoodSmoothOrientation (b : ι × Bool)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3))) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    SmoothOrientation (𝓡 3) (finiteCapNeighborhoodOpens hL hδ f hf hdisj b) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  exact pullbackSmoothOrientation (𝓡 3) (𝓡 3) (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b)
    (finiteCapRadialCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs b)
    (finiteCapRadialCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs b)
    (euclideanSmoothOrientation E3 o)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodSmoothOrientation ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodSmoothOrientation

theorem finiteCapNeighborhoodSmoothOrientation_pushforward (b : ι × Bool)
    (o : Orientation ℝ E3 (Fin (Module.finrank ℝ E3)))
    (p : finiteCapNeighborhoodOpens hL hδ f hf hdisj b) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    tangentOrientationEquiv (differentialEquivOfBijective (𝓡 3) (𝓡 3)
      (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b)
      (finiteCapRadialCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs b) p).toLinearEquiv
        ((finiteCapNeighborhoodSmoothOrientation I hdim hL hδ f hf hdisj hs b o).val p) = o := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  exact pullbackSmoothOrientation_pushforward (𝓡 3) (𝓡 3)
    (finiteCapRadialCoordinateMap I hdim hL hδ f hf hdisj hs b)
    (finiteCapRadialCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs b)
    (finiteCapRadialCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs b)
    (euclideanSmoothOrientation E3 o) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodSmoothOrientation_pushforward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodSmoothOrientation_pushforward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodSmoothOrientation_pushforward ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodSmoothOrientation_pushforward

def finiteOldAmbientCoordinateMap :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    finiteCoreInteriorOpens hL hδ f hf hdisj → M := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact Subtype.val ∘ (finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldAmbientCoordinateMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldAmbientCoordinateMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldAmbientCoordinateMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldAmbientCoordinateMap

theorem finiteOldAmbientCoordinateMap_contMDiff :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ContMDiff (𝓡 3) I ∞ (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact (contMDiff_subtype_val (I := I) (U := coreInteriorDomain f)).comp
    (finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs).symm.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldAmbientCoordinateMap_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldAmbientCoordinateMap_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldAmbientCoordinateMap_contMDiff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldAmbientCoordinateMap_contMDiff

theorem finiteOldAmbientCoordinateMap_mfderiv_bijective
    (p : finiteCoreInteriorOpens hL hδ f hf hdisj) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Bijective (mfderiv (𝓡 3) I (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs) p) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let D := (finiteCoreInteriorDiffeomorph I hdim hL hδ f hf hdisj hs).symm
  exact bijective_mfderiv_comp (𝓡 3) I I D (Subtype.val : coreInteriorDomain f → M) D.contMDiff
    (contMDiff_subtype_val (I := I) (U := coreInteriorDomain f))
    (fun q => (D.mfderivToContinuousLinearEquiv (by simp) q).bijective)
    (bijective_mfderiv_open_val I (coreInteriorDomain f)) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldAmbientCoordinateMap_mfderiv_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldAmbientCoordinateMap_mfderiv_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldAmbientCoordinateMap_mfderiv_bijective ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldAmbientCoordinateMap_mfderiv_bijective

def finiteOldSmoothOrientation (o : SmoothOrientation I M) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    SmoothOrientation (𝓡 3) (finiteCoreInteriorOpens hL hδ f hf hdisj) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  exact pullbackSmoothOrientation (𝓡 3) I (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs)
    (finiteOldAmbientCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs)
    (finiteOldAmbientCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs) o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldSmoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldSmoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldSmoothOrientation ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldSmoothOrientation

theorem finiteOldSmoothOrientation_pushforward (o : SmoothOrientation I M)
    (p : finiteCoreInteriorOpens hL hδ f hf hdisj) :
    let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
    tangentOrientationEquiv (differentialEquivOfBijective (𝓡 3) I
      (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs)
      (finiteOldAmbientCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs) p).toLinearEquiv
        ((finiteOldSmoothOrientation I hdim hL hδ f hf hdisj hs o).val p) =
          o.val (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs p) := by
  let : ChartedSpace E3 LocalOrientationQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ LocalOrientationQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  exact pullbackSmoothOrientation_pushforward (𝓡 3) I
    (finiteOldAmbientCoordinateMap I hdim hL hδ f hf hdisj hs)
    (finiteOldAmbientCoordinateMap_contMDiff I hdim hL hδ f hf hdisj hs)
    (finiteOldAmbientCoordinateMap_mfderiv_bijective I hdim hL hδ f hf hdisj hs) o p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldSmoothOrientation_pushforward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldSmoothOrientation_pushforward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldSmoothOrientation_pushforward ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteOldSmoothOrientation_pushforward
end DifferentialGeometry.Topology.ThreeManifold.Surgery
