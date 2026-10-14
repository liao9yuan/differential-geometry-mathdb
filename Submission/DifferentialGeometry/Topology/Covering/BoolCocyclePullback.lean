import Submission.DifferentialGeometry.Topology.Covering.BoolCocycle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Topology.BoolCocycle

variable {ι κ B A : Type*} [TopologicalSpace B] [TopologicalSpace A]
  {C : BoolCocycle ι B} {D : BoolCocycle κ A}

def Coorientation.pullback (O : D.Coorientation)
    (f : B → A) (hf : Continuous f) (indexMap : ι → κ)
    (hbase : ∀ i x, x ∈ C.baseSet i → f x ∈ D.baseSet (indexMap i))
    (hparity : ∀ i j x, x ∈ C.baseSet i ∩ C.baseSet j →
      D.parity (indexMap i) (indexMap j) (f x) = C.parity i j x) :
    C.Coorientation where
  coord i :=
    ⟨fun x => O.coord (indexMap i) ⟨f x.1, hbase i x.1 x.2⟩,
      (O.coord (indexMap i)).continuous.comp
        ((hf.comp continuous_subtype_val).subtype_mk _)⟩
  coord_change := by
    intro i j x hxi hxj
    change O.coord (indexMap j) ⟨f x, hbase j x hxj⟩ =
      Bool.xor (O.coord (indexMap i) ⟨f x, hbase i x hxi⟩) (C.parity i j x)
    simpa only [hparity i j x ⟨hxi, hxj⟩] using
      O.coord_change (indexMap i) (indexMap j) (f x)
        (hbase i x hxi) (hbase j x hxj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoolCocycle.Coorientation.pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoolCocycle.Coorientation.pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoolCocycle.Coorientation.pullback ``Submission.DifferentialGeometry.Topology.BoolCocycle.Coorientation.pullback

theorem nonempty_coorientation_of_simplyConnected_pullback
    [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (f : B → A) (hf : Continuous f) (indexMap : ι → κ)
    (hbase : ∀ i x, x ∈ C.baseSet i → f x ∈ D.baseSet (indexMap i))
    (hparity : ∀ i j x, x ∈ C.baseSet i ∩ C.baseSet j →
      D.parity (indexMap i) (indexMap j) (f x) = C.parity i j x)
    : Nonempty C.Coorientation := by
  obtain ⟨a₀⟩ := (inferInstance : Nonempty A)
  obtain ⟨O⟩ := D.nonempty_coorientation a₀ _root_.Bool.false
  exact ⟨O.pullback f hf indexMap hbase hparity⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BoolCocycle.nonempty_coorientation_of_simplyConnected_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BoolCocycle.nonempty_coorientation_of_simplyConnected_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BoolCocycle.nonempty_coorientation_of_simplyConnected_pullback ``Submission.DifferentialGeometry.Topology.BoolCocycle.nonempty_coorientation_of_simplyConnected_pullback

end DifferentialGeometry.Topology.BoolCocycle
