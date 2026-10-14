/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SourceFacets
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34SourceIncidence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Cut

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

theorem Section34CutFrame.cutLe_iff_source_subset
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) {m l : Section34CutLabelOf 𝒦 𝒦'} :
    Section34CutLe m l ↔ src m ⊆ src l := by
  refine ⟨hcut.src_subset_of_cutLe, ?_⟩
  have aux : ∀ d, ∀ l : Section34CutLabelOf 𝒦 𝒦',
      section34Dim l = d → ∀ m, src m ⊆ src l → Section34CutLe m l := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro l hld m hml
        by_cases h : m = l
        · subst m
          exact Relation.ReflTransGen.refl
        obtain ⟨k, hkd, hmk, hkl⟩ := hcut.exists_facet_above_of_source_subset hml h
        have hklt : section34Dim k < d := by omega
        have hstep : Section34CutStep k l :=
          (hcut.cutStep_iff_codimension_one_source_subset (by omega)).2 hkl
        exact Relation.ReflTransGen.tail (ih _ hklt k rfl m hmk) hstep
  exact aux _ l rfl m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Section34CutFrame.cutLe_iff_source_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Section34CutFrame.cutLe_iff_source_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Section34CutFrame.cutLe_iff_source_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CutFrame.cutLe_iff_source_subset

end Cut

section Diagram

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}
  {tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

theorem section34SourceFace_iff_cutLe
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd) :
    ∀ l m : Section34CutLabelOf 𝒦 𝒦', src m ⊆ src l ↔ Section34CutLe m l := by
  intro l m
  exact hdata.1.cutLe_iff_source_subset.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.section34SourceFace_iff_cutLe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.section34SourceFace_iff_cutLe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.section34SourceFace_iff_cutLe ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.section34SourceFace_iff_cutLe

end Diagram

end DifferentialGeometry.Topology.PiecewiseLinear
