import Submission.DifferentialGeometry.Topology.SimplicialComplex.GeometricRealizationMap
import Submission.DifferentialGeometry.Topology.SimplicialComplex.OrderedMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.Simplicial
namespace DifferentialGeometry.Topology.SimplicialComplex
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  {K L : Geometry.SimplicialComplex ℝ E}

omit [LinearOrder E] in
theorem geometricSpace_mono (h : K ≤ L) : K.space ⊆ L.space := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, h hs, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricSpace_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricSpace_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricSpace_mono ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricSpace_mono


def geometricInclusion (h : K ≤ L) : TopCat.of K.space ⟶ TopCat.of L.space :=
  TopCat.ofHom ⟨Set.inclusion (geometricSpace_mono h), continuous_subtype_val.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricInclusion ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricInclusion

omit [LinearOrder E] in
@[simp]
theorem geometricInclusion_val (h : K ≤ L) (x : K.space) :
    (geometricInclusion h x : E) = x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricInclusion_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricInclusion_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricInclusion_val ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricInclusion_val


@[reassoc]
theorem geometricSingularMap_inclusion (h : K ≤ L) :
    orderedInclusion h ≫ geometricSingularMap L =
      geometricSingularMap K ≫ TopCat.toSSet.map (geometricInclusion h) := by
  ext n s
  apply (TopCat.toSSetObjEquiv (TopCat.of L.space) n).injective
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricSingularMap_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricSingularMap_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricSingularMap_inclusion ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricSingularMap_inclusion

@[reassoc]
theorem geometricRealizationMap_inclusion (h : K ≤ L) :
    SSet.toTop.map (orderedInclusion h) ≫ geometricRealizationMap L =
      geometricRealizationMap K ≫ geometricInclusion h := by
  apply (sSetTopAdj.homEquiv _ _).injective
  rw [sSetTopAdj.homEquiv_naturality_left, sSetTopAdj.homEquiv_naturality_right]
  simp only [geometricRealizationMap, Equiv.apply_symm_apply]
  exact geometricSingularMap_inclusion h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationMap_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationMap_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationMap_inclusion ``Submission.DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationMap_inclusion

end DifferentialGeometry.Topology.SimplicialComplex
