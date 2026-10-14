import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.LocalCharts

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

open _root_.Set

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [T1Space X] [T1Space Y]

theorem integralRelativeHomologyMap_eq_of_eqOn_openPartialHomeomorph
    (n : ℕ) (f : C(X, Y)) (e : OpenPartialHomeomorph X Y) (x : X)
    (U : Set X) (hU : IsOpen U) (hx : x ∈ U) (hUs : U ⊆ e.source)
    (hfe : _root_.Set.EqOn f e U) (hf : _root_.Set.MapsTo f ({x}ᶜ : Set X) ({e x}ᶜ : Set Y)) :
    integralRelativeHomologyMap n f hf =
      (integralLocalHomologyOpenPartialHomeomorphIso n e x (hUs hx)).hom.hom := by
  let J := integralLocalHomologyNeighborhoodIso n x U hU hx
  have hcomp : (integralRelativeHomologyMap n f hf).comp J.hom.hom =
      (integralLocalHomologyOpenPartialHomeomorphIso n e x (hUs hx)).hom.hom.comp
        J.hom.hom := by
    rw [integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood n e x U hU hx hUs]
    change (integralRelativeHomologyMap n f hf).comp
      (integralRelativeHomologyMap n _ _) = _
    rw [← integralRelativeHomologyMap_comp]
    have hmaps : f.comp (singularSubspaceInclusion U) =
        (⟨fun z : U => e z, (e.continuousOn.mono hUs).domRestrict⟩ : C(U, Y)) := by
      ext z
      exact hfe z.property
    simp only [hmaps]
  apply LinearMap.ext
  intro a
  have h := LinearMap.congr_fun hcomp (J.inv.hom a)
  have ha : J.hom.hom (J.inv.hom a) = a := congrArg (fun k => k.hom a) J.inv_hom_id
  simpa only [LinearMap.comp_apply, ha] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_eq_of_eqOn_openPartialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_eq_of_eqOn_openPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_eq_of_eqOn_openPartialHomeomorph ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_eq_of_eqOn_openPartialHomeomorph

end DifferentialGeometry.Topology
