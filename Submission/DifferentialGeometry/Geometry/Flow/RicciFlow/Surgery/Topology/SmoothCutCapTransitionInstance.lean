import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapPresentation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctEventModelConstruction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalTransitionBridge
import Submission.DifferentialGeometry.Topology.Manifold.InteriorAtlas
import Submission.DifferentialGeometry.Topology.SphereSeparation.HalfSpaceClosure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.E3 target :: scope.openDecls } }

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N]
variable (s : Set N) (hs : IsOpen s)

open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation in
noncomputable def subsetAmbientChart (p : s) : OpenPartialHomeomorph s E3 :=
  (chartAt E3 p.1).subtypeRestr (s := ⟨s, hs⟩) ⟨p⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetAmbientChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetAmbientChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetAmbientChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetAmbientChart

open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation in
noncomputable def subsetChart (p : s) :
    OpenPartialHomeomorph s (EuclideanHalfSpace 3) :=
  (subsetAmbientChart s hs p).trans InteriorHalfSpace.chart

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart

open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation in
theorem subsetChart_mem_source (p : s) : p ∈ (subsetChart s hs p).source := by
  rw [subsetChart, OpenPartialHomeomorph.trans_source]
  refine ⟨?_, Set.mem_univ _⟩
  rw [subsetAmbientChart, OpenPartialHomeomorph.subtypeRestr_source]
  exact mem_chart_source E3 p.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart_mem_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart_mem_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart_mem_source ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart_mem_source

open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation in
@[instance_reducible]
noncomputable def subsetChartedSpace :
    ChartedSpace (EuclideanHalfSpace 3) s where
  atlas := Set.range (subsetChart s hs)
  chartAt := subsetChart s hs
  mem_chart_source p := subsetChart_mem_source s hs p
  chart_mem_atlas p := ⟨p, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChartedSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChartedSpace

open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation in
theorem subsetIsManifold [IsManifold (modelWithCornersSelf ℝ E3) ∞ N] :
    letI := subsetChartedSpace s hs
    IsManifold (𝓡∂ 3) ∞ s := by
  let _ := subsetChartedSpace s hs
  apply isManifold_of_contDiffOn (𝓡∂ 3) ∞
  rintro e e' ⟨p, rfl⟩ ⟨q, rfl⟩
  let U : TopologicalSpace.Opens N := ⟨s, hs⟩
  let _ : ChartedSpace E3 U := TopologicalSpace.Opens.instChartedSpace U
  let _ : HasGroupoid U (contDiffGroupoid ∞ (modelWithCornersSelf ℝ E3)) :=
    TopologicalSpace.Opens.instHasGroupoid (contDiffGroupoid ∞ (modelWithCornersSelf ℝ E3)) U
  let a := subsetAmbientChart s hs p
  let b := subsetAmbientChart s hs q
  have ha : a ∈ atlas E3 U := by
    simpa only [a, subsetAmbientChart, TopologicalSpace.Opens.chartAt_eq] using
      (chart_mem_atlas E3 (x := (⟨p.1, p.2⟩ : U)))
  have hb : b ∈ atlas E3 U := by
    simpa only [b, subsetAmbientChart, TopologicalSpace.Opens.chartAt_eq] using
      (chart_mem_atlas E3 (x := (⟨q.1, q.2⟩ : U)))
  have habG : a.symm.trans b ∈ contDiffGroupoid ∞ (modelWithCornersSelf ℝ E3) :=
    (contDiffGroupoid ∞ (modelWithCornersSelf ℝ E3)).compatible ha hb
  have hab := (mem_groupoid_of_pregroupoid.mp habG).1
  have hab' : ContDiffOn ℝ ∞ (a.symm.trans b) (a.symm.trans b).source := by
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, _root_.Set.preimage_id_eq, _root_.Set.range_id, _root_.Set.inter_univ, id_eq] using hab
  have hgoal := InteriorHalfSpace.contDiffOn_interiorized_transition a b hab'
  simpa only [subsetChart, a, b, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc] using hgoal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetIsManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetIsManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetIsManifold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetIsManifold

open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation in
theorem subset_inclusion_isSmoothEmbedding [IsManifold (modelWithCornersSelf ℝ E3) ∞ N] :
    letI := subsetChartedSpace s hs
    letI := subsetIsManifold s hs
    IsSmoothEmbedding (𝓡∂ 3) (modelWithCornersSelf ℝ E3) ∞ (Subtype.val : s → N) := by
  let _ := subsetChartedSpace s hs
  let _ := subsetIsManifold s hs
  refine ⟨?_, Topology.IsEmbedding.subtypeVal⟩
  apply Manifold.IsImmersionOfComplement.isImmersion (F := PUnit)
  intro p
  let a := chartAt E3 p.1
  let dom := subsetChart s hs p
  let cod := a.trans InteriorHalfSpace.ambientChart
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtype_val.continuousAt
    (ContinuousLinearEquiv.prodUnique ℝ E3 PUnit)
    dom cod
  · exact subsetChart_mem_source s hs p
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨mem_chart_source E3 p.1, Set.mem_univ _⟩
  · exact IsManifold.chart_mem_maximalAtlas p
  · apply InteriorHalfSpace.trans_mem_maximalAtlas
    · exact IsManifold.chart_mem_maximalAtlas p.1
    · exact InteriorHalfSpace.ambientChart_mem_contDiffGroupoid
  · intro z hz
    rw [dom.extend_target_eq_image_source] at hz
    rcases hz with ⟨y, hy, rfl⟩
    have hy' : (dom.extend (𝓡∂ 3)).symm ((dom.extend (𝓡∂ 3)) y) = y :=
      (dom.extend (𝓡∂ 3)).left_inv (by simpa using hy)
    rw [Function.comp_apply, Function.comp_apply, hy']
    change (a.trans InteriorHalfSpace.ambientChart) y.1 =
      ((𝓡∂ 3) ((subsetAmbientChart s hs p).trans InteriorHalfSpace.chart y))
    rw [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.trans_apply]
    have hyval : (subsetAmbientChart s hs p) y = a y.1 := rfl
    rw [hyval]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subset_inclusion_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subset_inclusion_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subset_inclusion_isSmoothEmbedding ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subset_inclusion_isSmoothEmbedding

open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation in
theorem subsetChart_apply_zero_pos (p : s) : 0 < ((subsetChart s hs p) p).1 0 := by
  rw [subsetChart, OpenPartialHomeomorph.trans_apply]
  change 0 < (InteriorHalfSpace.chart ((subsetAmbientChart s hs p) p)).1 0
  rw [show (InteriorHalfSpace.chart ((subsetAmbientChart s hs p) p)).1 0 =
      Real.exp (((subsetAmbientChart s hs p) p) 0) from rfl]
  exact Real.exp_pos _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart_apply_zero_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart_apply_zero_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart_apply_zero_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart_apply_zero_pos

open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation in
theorem subset_isInteriorPoint (p : s) :
    letI := subsetChartedSpace s hs
    (𝓡∂ 3).IsInteriorPoint p := by
  let _ := subsetChartedSpace s hs
  rw [ModelWithCorners.IsInteriorPoint, interior_range_modelWithCornersEuclideanHalfSpace]
  change 0 < (extChartAt (𝓡∂ 3) p p) 0
  rw [extChartAt_coe]
  change 0 < ((subsetChart s hs p) p).1 0
  exact subsetChart_apply_zero_pos s hs p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subset_isInteriorPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subset_isInteriorPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subset_isInteriorPoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subset_isInteriorPoint

open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation in
theorem subset_boundary_eq_empty :
    letI := subsetChartedSpace s hs
    (𝓡∂ 3).boundary s = ∅ := by
  let _ := subsetChartedSpace s hs
  rw [← ModelWithCorners.compl_interior]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact hp (subset_isInteriorPoint s hs p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subset_boundary_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subset_boundary_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subset_boundary_eq_empty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subset_boundary_eq_empty

namespace halfSpaceLogTwist

open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation

theorem setFirst_ofLp_zero (z : E3) (a : ℝ) :
    (InteriorHalfSpace.setFirst z a).ofLp 0 = a := by
  simp [InteriorHalfSpace.setFirst, WithLp.ofLp_toLp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.setFirst_ofLp_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.setFirst_ofLp_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.setFirst_ofLp_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.setFirst_ofLp_zero

theorem setFirst_setFirst_same (z : E3) (a : ℝ) :
    InteriorHalfSpace.setFirst (InteriorHalfSpace.setFirst z a) (z 0) = z := by
  apply WithLp.ofLp_injective 2
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [InteriorHalfSpace.setFirst, WithLp.ofLp_toLp]
  · simp [InteriorHalfSpace.setFirst, WithLp.ofLp_toLp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.setFirst_setFirst_same then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.setFirst_setFirst_same"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.setFirst_setFirst_same ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.setFirst_setFirst_same

theorem contMDiffOn_log :
    ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞
      (fun y : E3 => InteriorHalfSpace.setFirst y (Real.log (y 0))) {y | 0 < y 0} :=
  contMDiffOn_iff_contDiffOn.mpr InteriorHalfSpace.contDiffOn_setFirst_log

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.contMDiffOn_log then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.contMDiffOn_log"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.contMDiffOn_log ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.contMDiffOn_log

theorem contMDiff_exp :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E3) ∞
      (fun y : E3 => InteriorHalfSpace.setFirst y (Real.exp (y 0))) :=
  contMDiff_iff_contDiff.mpr InteriorHalfSpace.contDiff_setFirst_exp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.contMDiff_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.contMDiff_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.contMDiff_exp ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.contMDiff_exp

noncomputable def partialDiffeomorph :
    PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ where
  toPartialEquiv :=
    { toFun := fun y => InteriorHalfSpace.setFirst y (Real.log (y 0))
      invFun := fun y => InteriorHalfSpace.setFirst y (Real.exp (y 0))
      source := {y | 0 < y 0}
      target := _root_.Set.univ
      map_source' := fun y _ => Set.mem_univ _
      map_target' := fun y _ =>
        show (0 : ℝ) < (InteriorHalfSpace.setFirst y (Real.exp (y 0))).ofLp 0 from by
          rw [setFirst_ofLp_zero]
          exact Real.exp_pos _
      left_inv' := fun y hy => by
        rw [setFirst_ofLp_zero y (Real.log (y 0)), Real.exp_log hy, setFirst_setFirst_same]
      right_inv' := fun y _ => by
        rw [setFirst_ofLp_zero y (Real.exp (y 0)), Real.log_exp, setFirst_setFirst_same] }
  open_source := isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0)
  open_target := isOpen_univ
  contMDiffOn_toFun := contMDiffOn_log
  contMDiffOn_invFun := contMDiff_exp.contMDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.partialDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.partialDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.partialDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.partialDiffeomorph

theorem apply_exp (w : E3) :
    partialDiffeomorph (InteriorHalfSpace.setFirst w (Real.exp (w 0))) = w := by
  change InteriorHalfSpace.setFirst (InteriorHalfSpace.setFirst w (Real.exp (w 0)))
    (Real.log ((InteriorHalfSpace.setFirst w (Real.exp (w 0))) 0)) = w
  rw [show (InteriorHalfSpace.setFirst w (Real.exp (w 0))).ofLp 0 = Real.exp (w 0) from
      setFirst_ofLp_zero w (Real.exp (w 0))]
  rw [Real.log_exp, setFirst_setFirst_same]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.apply_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.apply_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.apply_exp ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.halfSpaceLogTwist.apply_exp

end halfSpaceLogTwist

open _root_.Submission.DifferentialGeometry.Topology.SphereSeparation

theorem subsetChart_apply_val (x z : s) :
    ((subsetChart s hs x) z).val =
      InteriorHalfSpace.setFirst ((chartAt E3 x.1) z.1)
        (Real.exp (((chartAt E3 x.1) z.1) 0)) := by
  rw [subsetChart, OpenPartialHomeomorph.trans_apply]
  rw [subsetAmbientChart, OpenPartialHomeomorph.subtypeRestr_coe, Set.domRestrict_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart_apply_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart_apply_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart_apply_val ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.subsetChart_apply_val

section CoreLocal

variable [IsManifold (modelWithCornersSelf ℝ E3) ∞ N]

noncomputable def chartAtHalfEqData (x : s) :
    letI := subsetChartedSpace s hs
    PLift (chartAt (EuclideanHalfSpace 3) x = subsetChart s hs x) := by
  letI := subsetChartedSpace s hs
  exact ⟨rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAtHalfEqData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAtHalfEqData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAtHalfEqData ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAtHalfEqData

omit [IsManifold (modelWithCornersSelf ℝ E3) ∞ N] in
theorem chartAt_half_eq (x : s) :
    letI := subsetChartedSpace s hs
    chartAt (EuclideanHalfSpace 3) x = subsetChart s hs x :=
  (chartAtHalfEqData s hs x).down

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_half_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_half_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_half_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_half_eq

noncomputable def extChartAtHalfApplyData (x z : s) :
    letI := subsetChartedSpace s hs
    PLift ((extChartAt (𝓡∂ 3) x) z = ((subsetChart s hs x) z).val) := by
  letI := subsetChartedSpace s hs
  exact ⟨by rw [extChartAt_coe]; rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extChartAtHalfApplyData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extChartAtHalfApplyData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extChartAtHalfApplyData ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extChartAtHalfApplyData

omit [IsManifold (modelWithCornersSelf ℝ E3) ∞ N] in
theorem extChartAt_half_apply (x z : s) :
    letI := subsetChartedSpace s hs
    (extChartAt (𝓡∂ 3) x) z = ((subsetChart s hs x) z).val :=
  (extChartAtHalfApplyData s hs x z).down

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extChartAt_half_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extChartAt_half_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extChartAt_half_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.extChartAt_half_apply

noncomputable def chartAtHalfSourceSubsetData (x z : s) :
    letI := subsetChartedSpace s hs
    PLift (z ∈ (chartAt (EuclideanHalfSpace 3) x).source →
      z.1 ∈ (chartAt E3 x.1).source) := by
  letI := subsetChartedSpace s hs
  exact ⟨by
    intro h1
    rw [chartAt_half_eq s hs x] at h1
    rw [subsetChart, OpenPartialHomeomorph.trans_source] at h1
    have h2 : z ∈ (subsetAmbientChart s hs x).source := h1.1
    rw [subsetAmbientChart, OpenPartialHomeomorph.subtypeRestr_source] at h2
    exact h2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAtHalfSourceSubsetData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAtHalfSourceSubsetData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAtHalfSourceSubsetData ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAtHalfSourceSubsetData

omit [IsManifold (modelWithCornersSelf ℝ E3) ∞ N] in
theorem chartAt_half_source_subset (x z : s) :
    letI := subsetChartedSpace s hs
    z ∈ (chartAt (EuclideanHalfSpace 3) x).source → z.1 ∈ (chartAt E3 x.1).source :=
  (chartAtHalfSourceSubsetData s hs x z).down

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_half_source_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_half_source_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_half_source_subset ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.chartAt_half_source_subset

noncomputable def coreLocalDiffeomorphWitness (x : s) :
    letI := subsetChartedSpace s hs
    letI := subsetIsManifold s hs
    (𝓡∂ 3).IsInteriorPoint x →
      Subtype (fun F : PartialDiffeomorph (𝓡∂ 3) (modelWithCornersSelf ℝ E3) s N ∞ =>
        x ∈ F.source ∧ _root_.Set.EqOn (Subtype.val : s → N) F F.source) := by
  letI := subsetChartedSpace s hs
  letI := subsetIsManifold s hs
  intro hx
  let c := DifferentialGeometry.Manifold.interiorChart (𝓡∂ 3) ∞ x
  let d := DifferentialGeometry.Manifold.interiorChart (modelWithCornersSelf ℝ E3) ∞ x.1
  let Ψ := halfSpaceLogTwist.partialDiffeomorph
  let Φ : PartialDiffeomorph (𝓡∂ 3) (modelWithCornersSelf ℝ E3) s N ∞ :=
    (c.trans Ψ).trans d.symm
  have hxC : x ∈ c.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff _ _ _).mpr hx
  have hcval (z : s) (hz : z ∈ c.toOpenPartialHomeomorph.source) :
      c z = InteriorHalfSpace.setFirst ((chartAt E3 x.1) z.1)
        (Real.exp (((chartAt E3 x.1) z.1) 0)) := by
    rw [show c z = (extChartAt (𝓡∂ 3) x) z from rfl]
    rw [extChartAt_half_apply s hs x z]
    exact subsetChart_apply_val s hs x z
  have hPsi (w : E3) : Ψ (InteriorHalfSpace.setFirst w (Real.exp (w 0))) = w :=
    halfSpaceLogTwist.apply_exp w
  have hd (z : s) (hz : z.1 ∈ (chartAt E3 x.1).source) :
      d.symm ((chartAt E3 x.1) z.1) = z.1 := by
    rw [show d.symm ((chartAt E3 x.1) z.1) =
      (extChartAt (modelWithCornersSelf ℝ E3) x.1).symm ((chartAt E3 x.1) z.1) from rfl]
    have hext : (extChartAt (modelWithCornersSelf ℝ E3) x.1) z.1 =
        (chartAt E3 x.1) z.1 := by
      rw [extChartAt_coe]
      rfl
    rw [← hext]
    exact (extChartAt (modelWithCornersSelf ℝ E3) x.1).left_inv (by
      rw [extChartAt_source]; exact hz)
  have hPsiC (z : s) (hz : z ∈ c.toOpenPartialHomeomorph.source) :
      Ψ (c z) = (chartAt E3 x.1) z.1 := by
    rw [hcval z hz]
    exact hPsi _
  have hxPsi : c x ∈ Ψ.source := by
    rw [hcval x hxC]
    change (0 : ℝ) <
      (InteriorHalfSpace.setFirst ((chartAt E3 x.1) x.1)
        (Real.exp (((chartAt E3 x.1) x.1) 0))).ofLp 0
    rw [halfSpaceLogTwist.setFirst_ofLp_zero]
    exact Real.exp_pos _
  have hxPsiVal : Ψ (c x) ∈ d.symm.source := by
    rw [hPsiC x hxC]
    change (chartAt E3 x.1) x.1 ∈ d.target
    rw [show d.target = interior (extChartAt (modelWithCornersSelf ℝ E3) x.1).target from rfl]
    have hext : (extChartAt (modelWithCornersSelf ℝ E3) x.1) x.1 =
        (chartAt E3 x.1) x.1 := by
      rw [extChartAt_coe]
      rfl
    rw [← hext]
    exact (chartAt E3 x.1).mem_interior_extend_target
      ((chartAt E3 x.1).map_source (mem_chart_source E3 x.1)) (by simp)
  have hxΦ : x ∈ Φ.source := by
    rw [show Φ.source = ((c.trans Ψ).toOpenPartialHomeomorph.trans
      d.symm.toOpenPartialHomeomorph).source from rfl,
      OpenPartialHomeomorph.trans_source]
    refine ⟨?_, hxPsiVal⟩
    rw [show (c.trans Ψ).toOpenPartialHomeomorph.source = (c.toOpenPartialHomeomorph.trans
      Ψ.toOpenPartialHomeomorph).source from rfl,
      OpenPartialHomeomorph.trans_source]
    exact ⟨hxC, hxPsi⟩
  refine ⟨Φ, hxΦ, ?_⟩
  intro z hz
  have hz1 : z ∈ (c.trans Ψ).toOpenPartialHomeomorph.source := by
    have h := hz
    rw [show Φ.source = ((c.trans Ψ).toOpenPartialHomeomorph.trans
      d.symm.toOpenPartialHomeomorph).source from rfl,
      OpenPartialHomeomorph.trans_source] at h
    exact h.1
  have hzC : z ∈ c.toOpenPartialHomeomorph.source := by
    have h := hz1
    rw [show (c.trans Ψ).toOpenPartialHomeomorph.source = (c.toOpenPartialHomeomorph.trans
      Ψ.toOpenPartialHomeomorph).source from rfl,
      OpenPartialHomeomorph.trans_source] at h
    exact h.1
  have hzsrc : z.1 ∈ (chartAt E3 x.1).source := by
    have h : z ∈ c.source := hzC
    rw [DifferentialGeometry.Manifold.interiorChart_source] at h
    exact chartAt_half_source_subset s hs x z h.1
  have hfun : Φ z = d.symm (Ψ (c z)) := by
    rw [show Φ z = (d.symm) ((c.trans Ψ) z) from rfl]
    rw [show (c.trans Ψ) z = Ψ (c z) from rfl]
  rw [hfun, hPsiC z hzC]
  exact (hd z hzsrc).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.coreLocalDiffeomorphWitness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.coreLocalDiffeomorphWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.coreLocalDiffeomorphWitness ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.coreLocalDiffeomorphWitness

theorem exists_localDiffeomorph (x : s) :
    letI := subsetChartedSpace s hs
    letI := subsetIsManifold s hs
    (𝓡∂ 3).IsInteriorPoint x →
      ∃ F : PartialDiffeomorph (𝓡∂ 3) (modelWithCornersSelf ℝ E3) s N ∞,
        x ∈ F.source ∧ _root_.Set.EqOn (Subtype.val : s → N) F F.source := by
  intro hx
  obtain ⟨F, hF⟩ := coreLocalDiffeomorphWitness s hs x hx
  exact ⟨F, hF⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_localDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_localDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_localDiffeomorph ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_localDiffeomorph

noncomputable def localDiffeomorphAtData (x : s) :
    letI := subsetChartedSpace s hs
    letI := subsetIsManifold s hs
    (𝓡∂ 3).IsInteriorPoint x →
      PLift (IsLocalDiffeomorphAt (𝓡∂ 3) (modelWithCornersSelf ℝ E3) ∞
        (Subtype.val : s → N) x) := by
  letI := subsetChartedSpace s hs
  letI := subsetIsManifold s hs
  intro hx
  exact PLift.up ⟨(coreLocalDiffeomorphWitness s hs x hx).1,
    (coreLocalDiffeomorphWitness s hs x hx).2.1,
    (coreLocalDiffeomorphWitness s hs x hx).2.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localDiffeomorphAtData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localDiffeomorphAtData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localDiffeomorphAtData ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.localDiffeomorphAtData

theorem isLocalDiffeomorphAt_subtype_val (x : s) :
    letI := subsetChartedSpace s hs
    letI := subsetIsManifold s hs
    (𝓡∂ 3).IsInteriorPoint x →
      IsLocalDiffeomorphAt (𝓡∂ 3) (modelWithCornersSelf ℝ E3) ∞
        (Subtype.val : s → N) x :=
  fun hx => (localDiffeomorphAtData s hs x hx).down

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isLocalDiffeomorphAt_subtype_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isLocalDiffeomorphAt_subtype_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isLocalDiffeomorphAt_subtype_val ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isLocalDiffeomorphAt_subtype_val

noncomputable def bijectiveMfderivData (x : s) :
    letI := subsetChartedSpace s hs
    letI := subsetIsManifold s hs
    (𝓡∂ 3).IsInteriorPoint x →
      PLift (Function.Bijective
        (mfderiv (𝓡∂ 3) (modelWithCornersSelf ℝ E3) (Subtype.val : s → N) x)) := by
  letI := subsetChartedSpace s hs
  letI := subsetIsManifold s hs
  intro hx
  have h := isLocalDiffeomorphAt_subtype_val s hs x hx
  rw [← h.mfderivToContinuousLinearEquiv_coe (by simp)]
  exact ⟨(h.mfderivToContinuousLinearEquiv (by simp)).bijective⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijectiveMfderivData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijectiveMfderivData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijectiveMfderivData ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijectiveMfderivData

theorem bijective_mfderiv_subtype_val (x : s) :
    letI := subsetChartedSpace s hs
    letI := subsetIsManifold s hs
    (𝓡∂ 3).IsInteriorPoint x →
      Function.Bijective
        (mfderiv (𝓡∂ 3) (modelWithCornersSelf ℝ E3) (Subtype.val : s → N) x) :=
  fun hx => (bijectiveMfderivData s hs x hx).down

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijective_mfderiv_subtype_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijective_mfderiv_subtype_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijective_mfderiv_subtype_val ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.bijective_mfderiv_subtype_val

end CoreLocal

@[instance_reducible]
noncomputable instance emptyChartedSpacePEmpty : ChartedSpace ThreeSpace PEmpty.{1} :=
  ChartedSpace.empty ThreeSpace PEmpty.{1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyChartedSpacePEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyChartedSpacePEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyChartedSpacePEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyChartedSpacePEmpty

@[reducible]
noncomputable def emptyStage : OrientedThreeStage where
  Carrier := PEmpty.{1}
  orientation :=
    { orientation := fun x => PEmpty.elim x
      locally_constant := fun p _ _ => PEmpty.elim p }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyStage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyStage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyStage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.emptyStage

@[reducible]
noncomputable def sphereStage : OrientedThreeStage where
  Carrier := Sphere 3
  orientation := TangentOrientationSection.ofManifoldOrientation
    (DifferentialGeometry.sphereOrientation 3 (by decide))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereStage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereStage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereStage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereStage

@[reducible]
noncomputable def sphereThreeEmptyStage : OrientedThreeStage where
  Carrier := PEmpty.{1} ⊕ Sphere 3
  topology := inferInstanceAs (TopologicalSpace (PEmpty.{1} ⊕ Sphere 3))
  charts := inferInstanceAs (ChartedSpace ThreeSpace (PEmpty.{1} ⊕ Sphere 3))
  smooth := inferInstanceAs (IsManifold ThreeModel ∞ (PEmpty.{1} ⊕ Sphere 3))
  hausdorff := inferInstanceAs (T2Space (PEmpty.{1} ⊕ Sphere 3))
  compact := inferInstanceAs (CompactSpace (PEmpty.{1} ⊕ Sphere 3))
  orientation := (emptyStage.sum sphereStage).orientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyStage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyStage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyStage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyStage

@[reducible]
noncomputable def sphereThreeEmptyTubes :
    @TubeSystem (PEmpty.{1} ⊕ Sphere 3) sphereThreeEmptyStage.topology where
  Index := PEmpty.{1}
  finiteIndex := ⟨∅, fun x => PEmpty.elim x⟩
  tube := fun a => PEmpty.elim a
  embedding := fun a => PEmpty.elim a
  disjoint := fun a => PEmpty.elim a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes

theorem sphereThreeEmptyTubes_core : sphereThreeEmptyTubes.core = univ := by
  change (⋃ a : PEmpty.{1}, sphereThreeEmptyTubes.removedBand a)ᶜ = _root_.Set.univ
  rw [Set.iUnion_of_empty, Set.compl_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes_core

theorem sphereThreeEmptyTubes_index_isEmpty : IsEmpty sphereThreeEmptyTubes.Index :=
  inferInstanceAs (IsEmpty PEmpty.{1})

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes_index_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes_index_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes_index_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes_index_isEmpty

theorem sphereThreeEmptyTubes_boundary_isEmpty : IsEmpty sphereThreeEmptyTubes.Boundary :=
  inferInstanceAs (IsEmpty (PEmpty.{1} × Bool))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes_boundary_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes_boundary_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes_boundary_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTubes_boundary_isEmpty

@[reducible]
noncomputable def sphereThreeEmptyTrace :
    @CutCapTopology (PEmpty.{1} ⊕ Sphere 3) PEmpty.{1} (Sphere 3) (PEmpty.{1} ⊕ Sphere 3)
      sphereThreeEmptyStage.topology emptyStage.topology sphereStage.topology
      sphereThreeEmptyStage.topology where
  tubes := sphereThreeEmptyTubes
  capping :=
    { coreInclusion := ⟨Subtype.val, continuous_subtype_val⟩
      coreEmbedding := Topology.IsEmbedding.subtypeVal
      cap := fun b => (sphereThreeEmptyTubes_boundary_isEmpty.false b).elim
      capEmbedding := fun b => (sphereThreeEmptyTubes_boundary_isEmpty.false b).elim
      attaching := fun b => (sphereThreeEmptyTubes_boundary_isEmpty.false b).elim
      boundary_eq := fun b => (sphereThreeEmptyTubes_boundary_isEmpty.false b).elim
      exhaustive := by
        rw [Set.iUnion_eq_empty.mpr
          (fun b => (sphereThreeEmptyTubes_boundary_isEmpty.false b).elim), Set.union_empty]
        exact Set.range_eq_univ.mpr fun n =>
          ⟨⟨n, by rw [sphereThreeEmptyTubes_core]; exact Set.mem_univ n⟩, rfl⟩
      core_cap_intersection := fun b =>
        (sphereThreeEmptyTubes_boundary_isEmpty.false b).elim
      cap_disjoint := fun b =>
        (sphereThreeEmptyTubes_boundary_isEmpty.false b).elim }
  presentation := Homeomorph.refl _
  nontrivial := Or.inr ⟨sphereThreeStage_nonempty.some⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTrace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTrace

theorem sphereThreeEmptyTrace_core : sphereThreeEmptyTrace.tubes.core = univ :=
  sphereThreeEmptyTubes_core

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTrace_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTrace_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTrace_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTrace_core

theorem isOpen_sphereThreeEmptyTrace_core :
    IsOpen sphereThreeEmptyTrace.tubes.core :=
  sphereThreeEmptyTrace_core.symm ▸ isOpen_univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isOpen_sphereThreeEmptyTrace_core then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isOpen_sphereThreeEmptyTrace_core"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isOpen_sphereThreeEmptyTrace_core ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isOpen_sphereThreeEmptyTrace_core

theorem sphereThreeEmptyTrace_coreInclusion_eq :
    (⇑sphereThreeEmptyTrace.capping.coreInclusion :
      sphereThreeEmptyTrace.tubes.core → (PEmpty.{1} ⊕ Sphere 3)) = Subtype.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTrace_coreInclusion_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTrace_coreInclusion_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTrace_coreInclusion_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereThreeEmptyTrace_coreInclusion_eq

noncomputable def smoothCutCapTransitionInstance :
    SmoothCutCapTransition sphereThreeEmptyStage emptyStage sphereStage
      sphereThreeEmptyStage := by
  letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
  letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := threeBallChartedSpace
  letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := threeBall_isManifold
  letI : ChartedSpace (EuclideanHalfSpace 3) sphereThreeEmptyTrace.tubes.core :=
    subsetChartedSpace sphereThreeEmptyTrace.tubes.core isOpen_sphereThreeEmptyTrace_core
  letI : IsManifold (𝓡∂ 3) ∞ sphereThreeEmptyTrace.tubes.core :=
    subsetIsManifold sphereThreeEmptyTrace.tubes.core isOpen_sphereThreeEmptyTrace_core
  refine
  { trace := sphereThreeEmptyTrace
    source_nonempty := ⟨Sum.inr sphereThreeStage_nonempty.some⟩
    tube_smooth := fun a => PEmpty.elim a
    coreCharts := subsetChartedSpace sphereThreeEmptyTrace.tubes.core
      isOpen_sphereThreeEmptyTrace_core
    coreSmooth := subsetIsManifold sphereThreeEmptyTrace.tubes.core
      isOpen_sphereThreeEmptyTrace_core
    core_induced := subset_inclusion_isSmoothEmbedding sphereThreeEmptyTrace.tubes.core
      isOpen_sphereThreeEmptyTrace_core
    core_boundary := ?_
    core_inclusion_smooth := subset_inclusion_isSmoothEmbedding sphereThreeEmptyTrace.tubes.core
      isOpen_sphereThreeEmptyTrace_core
    ballCharts := threeBallChartedSpace
    ballSmooth := threeBall_isManifold
    ball_induced := isSmoothEmbedding_threeBall_inclusion
    ball_boundary := threeBall_boundary_eq_sphere
    cap_smooth := fun b => (sphereThreeEmptyTubes_boundary_isEmpty.false b).elim
    attaching := fun b => (sphereThreeEmptyTubes_boundary_isEmpty.false b).elim
    attaching_eq := fun b => (sphereThreeEmptyTubes_boundary_isEmpty.false b).elim
    core_positive := ?_
    cap_positive := fun b => (sphereThreeEmptyTubes_boundary_isEmpty.false b).elim
    presentation := Diffeomorph.refl ThreeModel (PEmpty.{1} ⊕ Sphere 3) ∞
    presentation_eq := rfl
    presentation_positive := fun x => by
      have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel
          (Diffeomorph.refl ThreeModel (PEmpty.{1} ⊕ Sphere 3) ∞) x) := by
        rw [Diffeomorph.coe_refl, mfderiv_id]
        exact ⟨fun _ _ hab => hab, fun y => ⟨y, by simp⟩⟩
      refine ⟨hbij, ?_⟩
      have hlin : LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel
          (Diffeomorph.refl ThreeModel (PEmpty.{1} ⊕ Sphere 3) ∞) x).toLinearMap hbij =
          LinearEquiv.refl ℝ (TangentSpace ThreeModel x) := by
        apply LinearEquiv.ext
        intro v
        rw [LinearEquiv.ofBijective_apply, Diffeomorph.coe_refl, mfderiv_id]
        simp
      rw [hlin]
      erw [Orientation.map_refl]
      cases x <;> rfl }
  · rw [subset_boundary_eq_empty sphereThreeEmptyTrace.tubes.core
      isOpen_sphereThreeEmptyTrace_core]
    exact (Set.iUnion_of_empty _).symm
  · intro x hx
    have hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : sphereThreeEmptyTrace.tubes.core →
          sphereThreeEmptyStage.Carrier) x) :=
      bijective_mfderiv_subtype_val sphereThreeEmptyTrace.tubes.core
        isOpen_sphereThreeEmptyTrace_core x hx
    rw [sphereThreeEmptyTrace_coreInclusion_eq]
    refine ⟨hi, hi, ?_⟩
    have hcomp : (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : sphereThreeEmptyTrace.tubes.core →
            sphereThreeEmptyStage.Carrier) x).toLinearMap hi).symm.trans
        (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : sphereThreeEmptyTrace.tubes.core →
            sphereThreeEmptyStage.Carrier) x).toLinearMap hi) =
        LinearEquiv.refl ℝ E3 := by
      apply LinearEquiv.ext
      intro v
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      rfl
    rw [hcomp]
    erw [Orientation.map_refl]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothCutCapTransitionInstance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothCutCapTransitionInstance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothCutCapTransitionInstance ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothCutCapTransitionInstance

theorem nonempty_smoothCutCapTransition :
    Nonempty (SmoothCutCapTransition sphereThreeEmptyStage emptyStage sphereStage
      sphereThreeEmptyStage) :=
  ⟨smoothCutCapTransitionInstance⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_smoothCutCapTransition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_smoothCutCapTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_smoothCutCapTransition ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_smoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
