import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # Naturality of the original affine subdivision under face maps -/

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

/-- Original continuous-map chain images commute with the original boundary. -/
theorem integralSingularChainMap_boundary {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y)) (c : (integralSingularChains X).X (n + 1)) :
    (integralSingularChainMap f).f n ((integralSingularChains X).d (n + 1) n c) =
      (integralSingularChains Y).d (n + 1) n ((integralSingularChainMap f).f (n + 1) c) :=
  (congrArg (fun h : (integralSingularChains X).X (n + 1) ⟶
    (integralSingularChains Y).X n => h c) ((integralSingularChainMap f).comm (n + 1) n)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainMap_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainMap_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainMap_boundary ``Submission.DifferentialGeometry.Topology.integralSingularChainMap_boundary

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The original continuous-linear chain map commutes with the constructed
affine subdivision, even for maps collapsing the simplex dimension. -/
theorem affineSingularSubdivision_linear (n : ℕ) (f : E →L[ℝ] F)
    {A : Set E} (hA : Convex ℝ A)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A) :
    (integralSingularChainMap ⟨f, f.continuous⟩).f n (affineSingularSubdivision n c) =
      affineSingularSubdivision n ((integralSingularChainMap ⟨f, f.continuous⟩).f n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let D := ((integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1)).hom.comp
      (affineSingularSubdivision (n + 1)) - (affineSingularSubdivision (n + 1)).comp
        ((integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1)).hom
    have h : affineSingularChainsIn (n + 1) A ≤ LinearMap.ker D := by
      apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      change D (affineSingularChain (n + 1) v) = 0
      apply sub_eq_zero.mpr
      have hgen := affineSingularChain_mem (n + 1) A v hv
      have hδ := affineSingularChainsIn_boundary n A hgen
      have hS := affineSingularSubdivision_mem n hA hδ
      change (integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1)
        (affineSingularSubdivision (n + 1) (affineSingularChain (n + 1) v)) =
          affineSingularSubdivision (n + 1) ((integralSingularChainMap ⟨f, f.continuous⟩).f (n + 1)
            (affineSingularChain (n + 1) v))
      rw [affineSingularSubdivision_succ, affineSingularCone_linear n f _ A hS, ih hδ,
        integralSingularChainMap_boundary, affineSingularChain_linear, affineSimplexBarycenter_linear,
        affineSingularSubdivision_succ]
    exact sub_eq_zero.mp (h hc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSingularSubdivision_linear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSingularSubdivision_linear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSingularSubdivision_linear ``Submission.DifferentialGeometry.Topology.affineSingularSubdivision_linear

end DifferentialGeometry.Topology
