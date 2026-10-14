import Submission.DifferentialGeometry.Topology.Manifold.SmoothOrientationOpen
import Submission.DifferentialGeometry.Topology.Manifold.Orientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function _root_.Manifold _root_.TopologicalSpace _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_manifoldOrientation_eq_of_compatibleOrientation {n : ℕ}
    (hdim : Module.finrank ℝ E = n)
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin n))
    (ho : DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace I) o) :
    ∃ O : ManifoldOrientation I M n, O.orientation = o := by
  classical
  refine ⟨{ dimension_eq := hdim, orientation := o, locally_constant := ?_ }, rfl⟩
  intro p x hx
  obtain ⟨t, ht, U, hUx, hU, q, hq⟩ := ho x
  have ht_mem : MemTrivializationAtlas t := ht
  let S : _root_.Bundle.Trivialization E (TotalSpace.proj : _root_.Bundle.TotalSpace E (TangentSpace I) → M) :=
    _root_.FiberBundle.trivializationAt E (TangentSpace I) p
  have hSinst : MemTrivializationAtlas S := by
    change MemTrivializationAtlas (_root_.FiberBundle.trivializationAt E (TangentSpace I) p)
    infer_instance
  let C : M → E ≃L[ℝ] E := fun y => Trivialization.coordChangeL ℝ t S y
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ E := by simpa using hdim.symm
  have hxS : x ∈ S.baseSet := hx
  have hxT : x ∈ t.baseSet := hU (mem_of_mem_nhds hUx)
  have hcont : ContinuousOn (fun y : M =>
      (Trivialization.coordChangeL ℝ t S y : E →L[ℝ] E)) (t.baseSet ∩ S.baseSet) :=
    continuousOn_coordChange (R := ℝ) (B := M) (F := E) (E := TangentSpace I) t S
  have hC : ContinuousAt (fun y => (C y : E →L[ℝ] E)) x :=
    hcont.continuousAt ((t.open_baseSet.inter S.open_baseSet).mem_nhds ⟨hxT, hxS⟩)
  have hqL : ∀ y (hy : y ∈ U),
      Orientation.map (Fin n) (t.linearEquivAt ℝ y (hU hy)) (o y) = q := by
    intro y hy
    have h := hq y hy
    rwa [show (t.continuousLinearEquivAt ℝ y (hU hy)).toLinearEquiv =
      t.linearEquivAt ℝ y (hU hy) from LinearEquiv.ext fun v => rfl] at h
  have hdet : ContinuousAt
      (fun y => LinearMap.det (((C y).toLinearEquiv) : E →ₗ[ℝ] E)) x :=
    ContinuousLinearMap.continuous_det.continuousAt.comp hC
  have hxC : LinearMap.det (((C x).toLinearEquiv) : E →ₗ[ℝ] E) ≠ 0 :=
    (C x).toLinearEquiv.isUnit_det'.ne_zero
  have htrans (y : M) (hyT : y ∈ t.baseSet) (hyS : y ∈ S.baseSet) :
      (S.linearEquivAt ℝ y hyS) =
        (t.linearEquivAt ℝ y hyT).trans ((C y).toLinearEquiv) := by
    have hC' : (C y).toLinearEquiv =
        (t.linearEquivAt ℝ y hyT).symm.trans (S.linearEquivAt ℝ y hyS) :=
      LinearEquiv.coe_injective (Trivialization.coe_coordChangeL (R := ℝ) t S ⟨hyT, hyS⟩)
    calc (S.linearEquivAt ℝ y hyS)
        = (t.linearEquivAt ℝ y hyT).trans
            ((t.linearEquivAt ℝ y hyT).symm.trans (S.linearEquivAt ℝ y hyS)) := by
          rw [← LinearEquiv.trans_assoc, LinearEquiv.self_trans_symm, LinearEquiv.refl_trans]
      _ = (t.linearEquivAt ℝ y hyT).trans ((C y).toLinearEquiv) := by rw [← hC']
  rcases lt_or_gt_of_ne hxC with hneg | hpos
  · have hmem : {y : M | y ∈ U ∧ y ∈ S.baseSet ∧
        LinearMap.det (((C y).toLinearEquiv) : E →ₗ[ℝ] E) < 0} ∈ nhds x :=
      Filter.inter_mem hUx
        (Filter.inter_mem (S.open_baseSet.mem_nhds hxS)
          (hdet.eventually (isOpen_Iio.mem_nhds hneg)))
    obtain ⟨U', hU'sub, hU'open, hxU'⟩ := _root_.mem_nhds_iff.mp hmem
    refine ⟨U', hU'open, hxU', fun y hy => (hU'sub hy).2.1, fun y hy => ?_⟩
    obtain ⟨hyU, hyS, hyneg⟩ := hU'sub hy
    have hyT : y ∈ t.baseSet := hU hyU
    have hmapy : Orientation.map (Fin n) (S.linearEquivAt ℝ y hyS) (o y) = -q := by
      rw [htrans y hyT hyS, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between,
        hqL y hyU, (Orientation.map_eq_neg_iff_det_neg q (C y).toLinearEquiv hcard).2 hyneg]
    have hmapx : Orientation.map (Fin n) (S.linearEquivAt ℝ x hxS) (o x) = -q := by
      rw [htrans x hxT hxS, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between,
        hqL x (mem_of_mem_nhds hUx),
        (Orientation.map_eq_neg_iff_det_neg q (C x).toLinearEquiv hcard).2 hneg]
    simp only [tangentChartEquiv]
    rw [hmapy, hmapx]
  · have hmem : {y : M | y ∈ U ∧ y ∈ S.baseSet ∧
        0 < LinearMap.det (((C y).toLinearEquiv) : E →ₗ[ℝ] E)} ∈ nhds x :=
      Filter.inter_mem hUx
        (Filter.inter_mem (S.open_baseSet.mem_nhds hxS)
          (hdet.eventually (isOpen_Ioi.mem_nhds hpos)))
    obtain ⟨U', hU'sub, hU'open, hxU'⟩ := _root_.mem_nhds_iff.mp hmem
    refine ⟨U', hU'open, hxU', fun y hy => (hU'sub hy).2.1, fun y hy => ?_⟩
    obtain ⟨hyU, hyS, hypos⟩ := hU'sub hy
    have hyT : y ∈ t.baseSet := hU hyU
    have hmapy : Orientation.map (Fin n) (S.linearEquivAt ℝ y hyS) (o y) = q := by
      rw [htrans y hyT hyS, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between,
        hqL y hyU, (Orientation.map_eq_iff_det_pos q (C y).toLinearEquiv hcard).2 hypos]
    have hmapx : Orientation.map (Fin n) (S.linearEquivAt ℝ x hxS) (o x) = q := by
      rw [htrans x hxT hxS, ← DifferentialGeometry.VectorBundle.map_orientation_trans_between,
        hqL x (mem_of_mem_nhds hUx),
        (Orientation.map_eq_iff_det_pos q (C x).toLinearEquiv hcard).2 hpos]
    simp only [tangentChartEquiv]
    rw [hmapy, hmapx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_compatibleOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_compatibleOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_compatibleOrientation ``Submission.DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_compatibleOrientation

set_option backward.isDefEq.respectTransparency false in
theorem trivializationAt_continuousLinearMapAt_eq_preferredChartTangentEquiv
    (p y : M) (hy : y ∈ (chartAt H p).source) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ y =
      (preferredChartTangentEquiv I p y hy : E →L[ℝ] E) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hy]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.trivializationAt_continuousLinearMapAt_eq_preferredChartTangentEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.trivializationAt_continuousLinearMapAt_eq_preferredChartTangentEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.trivializationAt_continuousLinearMapAt_eq_preferredChartTangentEquiv ``Submission.DifferentialGeometry.Topology.Manifold.trivializationAt_continuousLinearMapAt_eq_preferredChartTangentEquiv

set_option backward.isDefEq.respectTransparency false in
theorem continuousLinearEquivAt_trivializationAt_eq_preferredChartTangentEquiv
    (p y : M) (hy : y ∈ (chartAt H p).source) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ y hy =
      preferredChartTangentEquiv I p y hy := by
  apply ContinuousLinearEquiv.ext
  funext v
  rw [Trivialization.coe_continuousLinearEquivAt_eq (_root_.FiberBundle.trivializationAt E (TangentSpace I) p)]
  exact DFunLike.congr_fun
    (trivializationAt_continuousLinearMapAt_eq_preferredChartTangentEquiv I p y hy) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.continuousLinearEquivAt_trivializationAt_eq_preferredChartTangentEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.continuousLinearEquivAt_trivializationAt_eq_preferredChartTangentEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.continuousLinearEquivAt_trivializationAt_eq_preferredChartTangentEquiv ``Submission.DifferentialGeometry.Topology.Manifold.continuousLinearEquivAt_trivializationAt_eq_preferredChartTangentEquiv

set_option backward.isDefEq.respectTransparency false in
theorem tangentChartEquiv_eq_preferredChartTangentEquiv
    (p y : M) (hy : y ∈ (chartAt H p).source) :
    tangentChartEquiv I M p y hy =
      (preferredChartTangentEquiv I p y hy).toLinearEquiv :=
  congrArg ContinuousLinearEquiv.toLinearEquiv
    (continuousLinearEquivAt_trivializationAt_eq_preferredChartTangentEquiv I p y hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.tangentChartEquiv_eq_preferredChartTangentEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.tangentChartEquiv_eq_preferredChartTangentEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.tangentChartEquiv_eq_preferredChartTangentEquiv ``Submission.DifferentialGeometry.Topology.Manifold.tangentChartEquiv_eq_preferredChartTangentEquiv

set_option backward.isDefEq.respectTransparency false in
theorem isCompatibleOrientation_of_smoothOrientation (o : SmoothOrientation I M) :
    DifferentialGeometry.VectorBundle.IsCompatibleOrientation (F := E) (TangentSpace I)
      o.val := by
  intro p
  obtain ⟨U, hUopen, hpU, hUeq⟩ :=
    (o.property p).exists_open ⟨p, mem_chart_source H p⟩
  refine ⟨trivializationAt E (TangentSpace I) p, inferInstance,
    Subtype.val '' U, ?_, ?_,
    Orientation.map (Fin (Module.finrank ℝ E))
      (preferredChartTangentEquiv I p p (mem_chart_source H p)).toLinearEquiv (o.val p), ?_⟩
  · exact ((chartAt H p).open_source.isOpenMap_subtype_val U hUopen).mem_nhds
      ⟨⟨p, mem_chart_source H p⟩, hpU, rfl⟩
  · rintro _ ⟨z, -, rfl⟩
    exact z.property
  · rintro y ⟨z, hz, rfl⟩
    rw [continuousLinearEquivAt_trivializationAt_eq_preferredChartTangentEquiv I p z.val
      z.property]
    exact hUeq z hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.isCompatibleOrientation_of_smoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.isCompatibleOrientation_of_smoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.isCompatibleOrientation_of_smoothOrientation ``Submission.DifferentialGeometry.Topology.Manifold.isCompatibleOrientation_of_smoothOrientation

theorem exists_manifoldOrientation_eq_of_smoothOrientation (o : SmoothOrientation I M) :
    ∃ O : ManifoldOrientation I M (Module.finrank ℝ E), O.orientation = o.val :=
  exists_manifoldOrientation_eq_of_compatibleOrientation I rfl o.val
    (isCompatibleOrientation_of_smoothOrientation I o)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation ``Submission.DifferentialGeometry.Topology.Manifold.exists_manifoldOrientation_eq_of_smoothOrientation

def smoothOrientationOfManifoldOrientation
    (o : ManifoldOrientation I M (Module.finrank ℝ E)) : SmoothOrientation I M := by
  refine ⟨o.orientation, ?_⟩
  intro p
  have hfun : (fun y : (chartAt H p).source =>
      Orientation.map (Fin (Module.finrank ℝ E))
        (preferredChartTangentEquiv I p y.val y.property).toLinearEquiv (o.orientation y.val)) =
      (fun y : (chartAt H p).source =>
        Orientation.map (Fin (Module.finrank ℝ E))
          (tangentChartEquiv I M p y.val y.property) (o.orientation y.val)) := by
    funext y
    exact congrArg (fun L => Orientation.map (Fin (Module.finrank ℝ E)) L (o.orientation y.val))
      (tangentChartEquiv_eq_preferredChartTangentEquiv I p y.val y.property).symm
  rw [hfun]
  apply isLocallyConstant_of_open_neighborhoods
  intro x
  obtain ⟨U, hUopen, hxU, hUsrc, hconst⟩ := o.locally_constant p x.val x.property
  refine ⟨⟨Subtype.val ⁻¹' U, hUopen.preimage continuous_subtype_val⟩, hxU, ?_⟩
  refine (IsLocallyConstant.iff_exists_open _).2 ?_
  intro z
  exact ⟨Set.univ, isOpen_univ, _root_.Set.mem_univ z, fun y _ =>
    (hconst y.val y.property).trans (hconst z.val z.property).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation ``Submission.DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation

end DifferentialGeometry.Topology.Manifold
