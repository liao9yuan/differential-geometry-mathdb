import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

open _root_.Set

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralSingularHomologyMap_eq_of_relativeHomologyMap_eq
    (n : ℕ) (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : _root_.Set.MapsTo f A B)
    (a : integralSingularHomology n X) (b : integralSingularHomology n Y)
    (μ : integralRelativeHomology n A) (ν : integralRelativeHomology n B)
    (ha : integralAbsoluteToRelative n A a = μ)
    (hb : integralAbsoluteToRelative n B b = ν)
    (hlocal : integralRelativeHomologyMap n f hf μ = ν)
    (hinj : Function.Injective (integralAbsoluteToRelative n B)) :
    integralSingularHomologyMap n f a = b := by
  apply hinj
  have hnat := LinearMap.congr_fun (integralAbsoluteToRelative_natural n f hf) a
  simpa only [LinearMap.comp_apply, ha, hb, hlocal] using hnat

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyMap_eq_of_relativeHomologyMap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyMap_eq_of_relativeHomologyMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyMap_eq_of_relativeHomologyMap_eq ``Submission.DifferentialGeometry.Topology.integralSingularHomologyMap_eq_of_relativeHomologyMap_eq

theorem integralSingularHomologyMap_eq_of_singleton_fiber
    (n : ℕ) (f : C(X, Y)) {x : X} {y : Y} (hf : f ⁻¹' {y} = {x})
    (a : integralSingularHomology n X) (b : integralSingularHomology n Y)
    (μ : integralRelativeHomology n ({x}ᶜ : Set X))
    (ν : integralRelativeHomology n ({y}ᶜ : Set Y))
    (ha : integralAbsoluteToRelative n ({x}ᶜ : Set X) a = μ)
    (hb : integralAbsoluteToRelative n ({y}ᶜ : Set Y) b = ν)
    (hlocal : integralRelativeHomologyMap n f
      (show _root_.Set.MapsTo f ({x}ᶜ) ({y}ᶜ) from fun _ hz hzy => hz (hf ▸ hzy)) μ = ν)
    (hinj : Function.Injective (integralAbsoluteToRelative n ({y}ᶜ : Set Y))) :
    integralSingularHomologyMap n f a = b :=
  integralSingularHomologyMap_eq_of_relativeHomologyMap_eq n f
    (show _root_.Set.MapsTo f ({x}ᶜ) ({y}ᶜ) from fun _ hz hzy => hz (hf ▸ hzy))
    a b μ ν ha hb hlocal hinj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyMap_eq_of_singleton_fiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyMap_eq_of_singleton_fiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyMap_eq_of_singleton_fiber ``Submission.DifferentialGeometry.Topology.integralSingularHomologyMap_eq_of_singleton_fiber

end DifferentialGeometry.Topology
