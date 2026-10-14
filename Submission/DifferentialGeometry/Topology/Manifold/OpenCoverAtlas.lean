import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Submission.DifferentialGeometry.Topology.Manifold.InteriorChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {ι E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]

@[instance_reducible]
def chartedSpaceOfOpenCover (e : ι → OpenPartialHomeomorph M E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source) : ChartedSpace E M where
  atlas := _root_.Set.range e
  chartAt x := e (hcover x).choose
  mem_chart_source x := (hcover x).choose_spec
  chart_mem_atlas _ := _root_.Set.mem_range_self _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover ``Submission.DifferentialGeometry.Topology.Manifold.chartedSpaceOfOpenCover

theorem isManifold_chartedSpaceOfOpenCover
    (e : ι → OpenPartialHomeomorph M E) (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {n : ℕ∞ω}
    (hcompat : ∀ i j, ContDiffOn ℝ n ((e i).symm.trans (e j)) ((e i).symm.trans (e j)).source) :
    let _ := chartedSpaceOfOpenCover e hcover
    IsManifold 𝓘(ℝ, E) n M := by
  let _ := chartedSpaceOfOpenCover e hcover
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, _root_.Set.preimage_id, _root_.Set.range_id, _root_.Set.inter_univ] using hcompat i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.isManifold_chartedSpaceOfOpenCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.isManifold_chartedSpaceOfOpenCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.isManifold_chartedSpaceOfOpenCover ``Submission.DifferentialGeometry.Topology.Manifold.isManifold_chartedSpaceOfOpenCover

end DifferentialGeometry.Topology.Manifold

set_option autoImplicit false

open _root_.Set _root_.Function _root_.Manifold
open scoped _root_.Topology

namespace DifferentialGeometry.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [TopologicalSpace X] {ι : Type*}
  (F H N : ι → Type*) [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i, TopologicalSpace (H i)] [∀ i, TopologicalSpace (N i)] [∀ i, ChartedSpace (H i) (N i)]
  (J : ∀ i, ModelWithCorners ℝ (F i) (H i))
  [∀ i, IsManifold (J i) ∞ (N i)]
  (L : ∀ i, F i ≃L[ℝ] E)
  (e : ∀ i, OpenPartialHomeomorph (N i) X)
  (hcover : ∀ x : X, ∃ i, x ∈ (e i).target)
  (hinterior : ∀ i p, p ∈ (e i).source → (J i).IsInteriorPoint p)

private def coverCoordinate (p : Σ i, N i) : PartialDiffeomorph (J p.1) 𝓘(ℝ, E) (N p.1) E ∞ :=
  let d : Diffeomorph 𝓘(ℝ, F p.1) 𝓘(ℝ, E) (F p.1) E ∞ :=
    ⟨(L p.1).toEquiv, (L p.1).contDiff.contMDiff, (L p.1).symm.contDiff.contMDiff⟩
  (interiorChart (J p.1) ∞ p.2).trans d.toPartialDiffeomorph

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.coverCoordinate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.coverCoordinate target :: scope.openDecls } }

private def coverChart (p : Σ i, N i) : OpenPartialHomeomorph X E :=
  (e p.1).symm.trans (coverCoordinate F H N J L p).toOpenPartialHomeomorph

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.coverChart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.coverChart target :: scope.openDecls } }

@[reducible]
def openCoverChartedSpace : ChartedSpace E X where
  atlas := _root_.Set.range (coverChart F H N J L e)
  chartAt x := coverChart F H N J L e ⟨(hcover x).choose, (e (hcover x).choose).symm x⟩
  mem_chart_source x := by
    refine ⟨(hcover x).choose_spec, ?_⟩
    exact ⟨(mem_interiorChart_source_iff (J _) ∞ _).mpr
      (hinterior _ _ ((e _).map_target (hcover x).choose_spec)), trivial⟩
  chart_mem_atlas x := ⟨_, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.openCoverChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.openCoverChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.openCoverChartedSpace ``Submission.DifferentialGeometry.Manifold.openCoverChartedSpace

theorem isManifold_openCoverChartedSpace
    (htrans : ∀ i j, ContMDiffOn (J i) (J j) ∞
      ((e i).trans (e j).symm) ((e i).trans (e j).symm).source) :
    let _ := openCoverChartedSpace F H N J L e hcover hinterior
    IsManifold 𝓘(ℝ, E) ∞ X := by
  let _ := openCoverChartedSpace F H N J L e hcover hinterior
  apply isManifold_of_contDiffOn
  rintro f g ⟨p, rfl⟩ ⟨q, rfl⟩
  let d : PartialDiffeomorph (J p.1) (J q.1) (N p.1) (N q.1) ∞ :=
    { ((e p.1).trans (e q.1).symm).toPartialEquiv with
      open_source := ((e p.1).trans (e q.1).symm).open_source
      open_target := ((e p.1).trans (e q.1).symm).open_target
      contMDiffOn_toFun := htrans p.1 q.1
      contMDiffOn_invFun := htrans q.1 p.1 }
  let d' := (coverCoordinate F H N J L p).symm.trans
    (d.trans (coverCoordinate F H N J L q))
  have hh := contMDiffOn_iff_contDiffOn.mp d'.contMDiffOn
  change ContDiffOn ℝ ∞ d'.toOpenPartialHomeomorph d'.toOpenPartialHomeomorph.source at hh
  have heq : d'.toOpenPartialHomeomorph =
      (coverCoordinate F H N J L p).toOpenPartialHomeomorph.symm.trans
        (((e p.1).trans (e q.1).symm).trans
          (coverCoordinate F H N J L q).toOpenPartialHomeomorph) := rfl
  rw [heq] at hh
  simpa only [coverChart, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, _root_.Set.preimage_id, _root_.Set.range_id, _root_.Set.inter_univ,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.trans_assoc] using! hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.isManifold_openCoverChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.isManifold_openCoverChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.isManifold_openCoverChartedSpace ``Submission.DifferentialGeometry.Manifold.isManifold_openCoverChartedSpace

theorem contMDiffOn_openCover_parametrization
    (htrans : ∀ i j, ContMDiffOn (J i) (J j) ∞
      ((e i).trans (e j).symm) ((e i).trans (e j).symm).source) (i : ι) :
    let _ := openCoverChartedSpace F H N J L e hcover hinterior
    ContMDiffOn (J i) 𝓘(ℝ, E) ∞ (e i) (e i).source := by
  let _ := openCoverChartedSpace F H N J L e hcover hinterior
  change ContMDiffOn (J i) 𝓘(ℝ, E) ∞ (e i) (e i).source
  intro p hp
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_target]
  refine ⟨(e i).continuousOn.continuousAt ((e i).open_source.mem_nhds hp), ?_⟩
  let j := (hcover (e i p)).choose
  let q : Σ i, N i := ⟨j, (e j).symm (e i p)⟩
  have hq : q.2 ∈ (coverCoordinate F H N J L q).source :=
    ⟨(mem_interiorChart_source_iff (J j) ∞ _).mpr
      (hinterior j _ ((e j).map_target (hcover (e i p)).choose_spec)), trivial⟩
  have ht : p ∈ ((e i).trans (e j).symm).source := ⟨hp, (hcover (e i p)).choose_spec⟩
  have hfirst := (htrans i j).contMDiffAt (((e i).trans (e j).symm).open_source.mem_nhds ht)
  have hsecond := (coverCoordinate F H N J L q).contMDiffOn.contMDiffAt
    ((coverCoordinate F H N J L q).open_source.mem_nhds hq)
  change ContMDiffAt (J i) 𝓘(ℝ, E) ∞
    ((coverCoordinate F H N J L q) ∘ ((e i).trans (e j).symm)) p
  exact hsecond.comp p hfirst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.contMDiffOn_openCover_parametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.contMDiffOn_openCover_parametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.contMDiffOn_openCover_parametrization ``Submission.DifferentialGeometry.Manifold.contMDiffOn_openCover_parametrization

theorem contMDiffOn_openCover_inverse
    (htrans : ∀ i j, ContMDiffOn (J i) (J j) ∞
      ((e i).trans (e j).symm) ((e i).trans (e j).symm).source) (i : ι) :
    let _ := openCoverChartedSpace F H N J L e hcover hinterior
    ContMDiffOn 𝓘(ℝ, E) (J i) ∞ (e i).symm (e i).target := by
  let _ := openCoverChartedSpace F H N J L e hcover hinterior
  change ContMDiffOn 𝓘(ℝ, E) (J i) ∞ (e i).symm (e i).target
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  let j := (hcover x).choose
  let q : Σ i, N i := ⟨j, (e j).symm x⟩
  have hq : q.2 ∈ (coverCoordinate F H N J L q).source :=
    ⟨(mem_interiorChart_source_iff (J j) ∞ _).mpr
      (hinterior j _ ((e j).map_target (hcover x).choose_spec)), trivial⟩
  have ht : q.2 ∈ ((e j).trans (e i).symm).source := by
    refine ⟨(e j).map_target (hcover x).choose_spec, ?_⟩
    change (e j) ((e j).symm x) ∈ (e i).target
    rwa [(e j).right_inv (hcover x).choose_spec]
  have hfirst := (coverCoordinate F H N J L q).symm.contMDiffOn.contMDiffAt
    ((coverCoordinate F H N J L q).open_target.mem_nhds
      ((coverCoordinate F H N J L q).map_source hq))
  have hsecond := (htrans j i).contMDiffAt (((e j).trans (e i).symm).open_source.mem_nhds ht)
  have hsecond' : ContMDiffAt (J j) (J i) ∞ ((e j).trans (e i).symm)
      ((coverCoordinate F H N J L q).symm ((coverCoordinate F H N J L q) q.2)) := by
    have heq : (coverCoordinate F H N J L q).symm ((coverCoordinate F H N J L q) q.2) = q.2 :=
      (coverCoordinate F H N J L q).left_inv hq
    rw [heq]
    exact hsecond
  have hh := hsecond'.comp ((coverCoordinate F H N J L q) q.2) hfirst
  change ContMDiffWithinAt 𝓘(ℝ, E) (J i) ∞
    (((e j).trans (e i).symm) ∘ (coverCoordinate F H N J L q).symm)
    (_root_.Set.range (𝓘(ℝ, E))) ((coverCoordinate F H N J L q) q.2)
  exact hh.contMDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.contMDiffOn_openCover_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.contMDiffOn_openCover_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.contMDiffOn_openCover_inverse ``Submission.DifferentialGeometry.Manifold.contMDiffOn_openCover_inverse

end DifferentialGeometry.Manifold
