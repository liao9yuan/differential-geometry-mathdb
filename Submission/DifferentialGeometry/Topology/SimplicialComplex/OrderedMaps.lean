import Submission.DifferentialGeometry.Topology.SimplicialComplex.OrderedSimplicialSet

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
variable {ι : Type u} [LinearOrder ι] {K L Q : PreAbstractSimplicialComplex ι}


theorem orderedNerveSubcomplex_mono (h : K ≤ L) : orderedNerveSubcomplex K ≤ orderedNerveSubcomplex L :=
  fun _ _ hx => h hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedNerveSubcomplex_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedNerveSubcomplex_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedNerveSubcomplex_mono ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedNerveSubcomplex_mono


def orderedInclusion (h : K ≤ L) : orderedSimplicialSet K ⟶ orderedSimplicialSet L :=
  SSet.Subcomplex.homOfLE (orderedNerveSubcomplex_mono h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion


@[simp]
theorem orderedInclusion_app_val (h : K ≤ L) (n : SimplexCategoryᵒᵖ)
    (s : (orderedSimplicialSet K).obj n) :
    ((orderedInclusion h).app n s).val = s.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_app_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_app_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_app_val ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_app_val


instance mono_orderedInclusion (h : K ≤ L) : _root_.CategoryTheory.Mono (orderedInclusion h) :=
  inferInstanceAs (_root_.CategoryTheory.Mono (SSet.Subcomplex.homOfLE (orderedNerveSubcomplex_mono h)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.mono_orderedInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.mono_orderedInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.mono_orderedInclusion ``Submission.DifferentialGeometry.Topology.SimplicialComplex.mono_orderedInclusion


@[simp]
theorem orderedInclusion_comp (h : K ≤ L) (h' : L ≤ Q) :
    orderedInclusion h ≫ orderedInclusion h' = orderedInclusion (h.trans h') := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_comp ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_comp


@[simp]
theorem orderedInclusion_refl : orderedInclusion (le_rfl : K ≤ K) = 𝟙 (orderedSimplicialSet K) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_refl ``Submission.DifferentialGeometry.Topology.SimplicialComplex.orderedInclusion_refl

end DifferentialGeometry.Topology.SimplicialComplex
