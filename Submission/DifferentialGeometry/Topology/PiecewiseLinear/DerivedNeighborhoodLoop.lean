/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homotopy.DeformationRetractPath
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRetraction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.unitInterval
open _root_.Submission.DifferentialGeometry.Topology.Homotopy

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]

open _root_.Classical in
noncomputable def derivedNeighborhoodRetractLoop (hL : L.faces ⊆ K.faces)
    {x : derivedNeighborhoodSpace K L} (hx : x ∈ derivedNeighborhoodSubcomplex K L)
    (ℓ : Path x x) : Path x x :=
  (derivedNeighborhoodStrongDeformationRetract hL).retractLoop hx ℓ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetractLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetractLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetractLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetractLoop

open _root_.Classical in
theorem homotopic_derivedNeighborhoodRetractLoop (hL : L.faces ⊆ K.faces)
    {x : derivedNeighborhoodSpace K L} (hx : x ∈ derivedNeighborhoodSubcomplex K L)
    (ℓ : Path x x) : ℓ.Homotopic (derivedNeighborhoodRetractLoop hL hx ℓ) :=
  (derivedNeighborhoodStrongDeformationRetract hL).homotopic_retractLoop hx ℓ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.homotopic_derivedNeighborhoodRetractLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.homotopic_derivedNeighborhoodRetractLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.homotopic_derivedNeighborhoodRetractLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.homotopic_derivedNeighborhoodRetractLoop

open _root_.Classical in
theorem derivedNeighborhoodRetractLoop_mem_space (hL : L.faces ⊆ K.faces)
    {x : derivedNeighborhoodSpace K L} (hx : x ∈ derivedNeighborhoodSubcomplex K L)
    (ℓ : Path x x) (s : I) :
    ((derivedNeighborhoodRetractLoop hL hx ℓ s : derivedNeighborhoodSpace K L) : E) ∈ L.space :=
  (derivedNeighborhoodStrongDeformationRetract hL).retractLoop_mem hx ℓ s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetractLoop_mem_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetractLoop_mem_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetractLoop_mem_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetractLoop_mem_space

open _root_.Classical in
theorem derivedNeighborhoodRetractLoop_apply (hL : L.faces ⊆ K.faces)
    {x : derivedNeighborhoodSpace K L} (hx : x ∈ derivedNeighborhoodSubcomplex K L)
    (ℓ : Path x x) (s : I) :
    ((derivedNeighborhoodRetractLoop hL hx ℓ s : derivedNeighborhoodSpace K L) : E) =
      subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L)
        ((ℓ s : derivedNeighborhoodSpace K L) : E) :=
  derivedNeighborhoodStrongDeformationRetract_retraction_apply hL (ℓ s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetractLoop_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetractLoop_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetractLoop_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetractLoop_apply

end DifferentialGeometry.Topology.PiecewiseLinear
