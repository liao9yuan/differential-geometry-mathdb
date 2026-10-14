/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonCarrier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLModelTopology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem bijective_fundamentalGroup_map_homeomorph
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    Function.Bijective (FundamentalGroup.map (e : C(X, Y)) x) := by
  have h := fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv
    e.toHomotopyEquiv x (e x) rfl
  change Function.Bijective (FundamentalGroup.mapOfEq (e : C(X, Y))
    (rfl : e x = e x)) at h
  have heq : FundamentalGroup.mapOfEq (e : C(X, Y)) (rfl : e x = e x) =
      FundamentalGroup.map (e : C(X, Y)) x := by
    ext a
    rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
    rfl
  rwa [heq] at h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bijective_fundamentalGroup_map_homeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.bijective_fundamentalGroup_map_homeomorph target :: scope.openDecls } }

theorem IsPLHomeomorphInto.carriesFundamentalGroupOnto_of_image
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {u : E3 → M} {P J : Set E3} (hu : IsPLHomeomorphInto 3 u P) (hP : IsCompact P)
    (hJ : IsPolyhedron J) (hJP : J ⊆ P)
    (hcarry : CarriesFundamentalGroupOnto (u '' J) (u '' P)) :
    CarriesFundamentalGroupOnto J P := by
  have huJ : IsPLHomeomorphInto 3 u J :=
    (hu.isPLOn.mono_of_isPolyhedron hJ hJP).isPLHomeomorphInto_of_isCompact
      hJ.isCompact (hu.injOn.mono hJP)
  let eP := hu.compactModelHomeomorph hP
  let eJ := huJ.compactModelHomeomorph hJ.isCompact
  refine ⟨hJP, fun hsub x γ => ?_⟩
  let i : C(J, P) := ⟨inclusion hsub, continuous_inclusion hsub⟩
  let j : C(u '' J, u '' P) :=
    ⟨inclusion (_root_.Set.image_mono hsub), continuous_inclusion (_root_.Set.image_mono hsub)⟩
  have hmap (a : FundamentalGroup J x) :
      FundamentalGroup.map j (eJ x) (FundamentalGroup.map (eJ : C(J, u '' J)) x a) =
        FundamentalGroup.map (eP : C(P, u '' P)) (i x) (FundamentalGroup.map i x a) := by
    refine Quotient.inductionOn a ?_
    intro p
    rfl
  obtain ⟨β, hβ⟩ := hcarry.2 (_root_.Set.image_mono hsub) (eJ x)
    (FundamentalGroup.map (eP : C(P, u '' P)) (i x) γ)
  obtain ⟨α, hα⟩ := (bijective_fundamentalGroup_map_homeomorph eJ x).2 β
  refine ⟨α, (bijective_fundamentalGroup_map_homeomorph eP (i x)).1 ?_⟩
  rw [← hmap, hα]
  exact hβ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.carriesFundamentalGroupOnto_of_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.carriesFundamentalGroupOnto_of_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.carriesFundamentalGroupOnto_of_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.carriesFundamentalGroupOnto_of_image

theorem IsCombinatorialSolidTorus.carriesFirstHomologyOnto_of_image
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {u : E3 → M} {P J : Set E3} (hP : IsCombinatorialSolidTorus P)
    (hu : IsPLHomeomorphInto 3 u P) (hJ : IsPolyhedron J) (hconn : IsPathConnected J)
    (hJP : J ⊆ P) (hcarry : CarriesFirstHomologyOnto (u '' J) (u '' P)) :
    CarriesFirstHomologyOnto J P := by
  have htop := hP.isTopologicalSolidTorus_image hu
  have htarget := htop.carriesFundamentalGroupOnto_of_carriesFirstHomologyOnto hcarry
      (hconn.image' (hu.continuousOn.mono hJP))
  have hmodel := hu.carriesFundamentalGroupOnto_of_image
    hP.isPolyhedron.isCompact hJ hJP htarget
  exact hmodel.carriesFirstHomologyOnto hconn.nonempty hP.1.isPathConnected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus.carriesFirstHomologyOnto_of_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus.carriesFirstHomologyOnto_of_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus.carriesFirstHomologyOnto_of_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus.carriesFirstHomologyOnto_of_image

end DifferentialGeometry.Topology.PiecewiseLinear
