import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.GoodFrame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable (P : OrientedThreeStage.{u})

theorem normSq_continuous_in_frame {Q : Type*} [TopologicalSpace Q] {r : ℕ}
    (p : P.Carrier) (b : Module.Basis (Fin 3) ℝ ThreeSpace)
    (x : Q → P.Carrier) (g : Q → P.Metric)
    (A : (q : Q) → Tensor0SSpace r ThreeModel (x q))
    (hx : ∀ q, x q ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)
    (hg : ∀ i j, Continuous (fun q => (g q).inner (x q)
      ((_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).localFrame b i (x q))
      ((_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).localFrame b j (x q))))
    (hA : ∀ n : Fin r → Fin 3, Continuous (fun q => A q (fun k =>
      (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).localFrame b (n k) (x q)))) :
    Continuous (fun q => normSq0S (g q) (x q) r (A q)) := by
  classical
  let e := _root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p
  let G : Q → Matrix (Fin 3) (Fin 3) ℝ := fun q => gramE e (g q) b (x q)
  have hG : Continuous G := continuous_pi fun i => continuous_pi fun j => hg i j
  have hd : ∀ q, (G q).det ≠ 0 := fun q => (gramE_posDef e (g q) b (hx q)).det_pos.ne'
  have hInv : Continuous (fun q => (G q)⁻¹) := by
    have h := (hG.matrix_det.inv₀ hd).smul hG.matrix_adjugate
    change Continuous (fun q => (G q).det⁻¹ • (G q).adjugate) at h
    simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using h
  have hEntry : ∀ i j, Continuous (fun q => (G q)⁻¹ i j) :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp hInv)
  let F : Q → ℝ := fun q =>
    ∑ n : Fin r → Fin 3, ∑ m : Fin r → Fin 3,
      (∏ k : Fin r, (G q)⁻¹ (n k) (m k)) *
        A q (fun k => e.localFrame b (n k) (x q)) *
        A q (fun k => e.localFrame b (m k) (x q))
  have hF : Continuous F := by
    apply continuous_finsetSum
    intro n _
    apply continuous_finsetSum
    intro m _
    exact ((continuous_finsetProd _ fun k _ => hEntry (n k) (m k)).mul (hA n)).mul (hA m)
  have heq : (fun q => normSq0S (g q) (x q) r (A q)) = F := by
    funext q
    rw [normSq0S_eq_coord (g q) (x q) r
      ((e.isLocalFrameOn_localFrame_baseSet ThreeModel 1 b).toBasisAt (hx q))
      (fun i j => (G q)⁻¹ i j) (gramInv_inverse e (g q) b (hx q)) (A q)]
    simp only [coordInner0S, tensor0SComponent_apply, IsLocalFrameOn.toBasisAt_coe]
    rfl
  rw [heq]
  exact hF

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.normSq_continuous_in_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.normSq_continuous_in_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.normSq_continuous_in_frame ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.normSq_continuous_in_frame

theorem tensorFamily_frame_continuousOn {r : ℕ} {J : Set ℝ}
    {A : (t : ℝ) → (x : P.Carrier) → Tensor0SSpace r ThreeModel x}
    (hA : tensor0SFamilyContinuousOnSet r J A) (p : P.Carrier)
    (b : Module.Basis (Fin 3) ℝ ThreeSpace) (n : Fin r → Fin 3) :
    ContinuousOn (fun q : ℝ × P.Carrier => A q.1 q.2 (fun k =>
      (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).localFrame b (n k) q.2))
      (J ×ˢ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet) := by
  let e := _root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p
  let Q := ↥(J ×ˢ e.baseSet)
  rw [continuousOn_iff_continuous_domRestrict]
  apply hA.eval_continuous
    (continuous_fst.comp continuous_subtype_val) (fun q : Q => q.2.1)
    (continuous_snd.comp continuous_subtype_val)
  intro k
  exact ((e.isLocalFrameOn_localFrame_baseSet ThreeModel ∞ b).contMDiffOn (n k)).continuousOn
    |>.comp_continuous (continuous_snd.comp continuous_subtype_val) (fun q : Q => q.2.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.tensorFamily_frame_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.tensorFamily_frame_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.tensorFamily_frame_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.tensorFamily_frame_continuousOn

theorem tensorFamily_normSq_continuousOn {r : ℕ} {J : Set ℝ} {g : ℝ → P.Metric}
    {A : (t : ℝ) → (x : P.Carrier) → Tensor0SSpace r ThreeModel x}
    (hg : tensor0SFamilyContinuousOnSet 2 J (fun t x => metricTensorField (g t) x))
    (hA : tensor0SFamilyContinuousOnSet r J A) :
    ContinuousOn (fun q : ℝ × P.Carrier => normSq0S (g q.1) q.2 r (A q.1 q.2))
      (J ×ˢ _root_.Set.univ) := by
  intro q hq
  let e := _root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) q.2
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hx : q.2 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' q.2
  have hlocal : ContinuousOn
      (fun z : ℝ × P.Carrier => normSq0S (g z.1) z.2 r (A z.1 z.2))
      (J ×ˢ e.baseSet) := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine P.normSq_continuous_in_frame (Q := ↥(J ×ˢ e.baseSet)) q.2 b
      (fun z => z.1.2) (fun z => g z.1.1)
      (fun z => A z.1.1 z.1.2) (fun z => z.2.2) ?_ ?_
    · intro i j
      have h := continuousOn_iff_continuous_domRestrict.mp
        (P.tensorFamily_frame_continuousOn hg q.2 b ![i, j])
      simp only [metricTensorField_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
      exact h
    · intro n
      exact continuousOn_iff_continuous_domRestrict.mp
        (P.tensorFamily_frame_continuousOn hA q.2 b n)
  have hn : J ×ˢ e.baseSet ∈ 𝓝[J ×ˢ (_root_.Set.univ : Set P.Carrier)] q := by
    rw [mem_nhdsWithin]
    refine ⟨univ ×ˢ e.baseSet, isOpen_univ.prod e.open_baseSet, ⟨mem_univ _, hx⟩, ?_⟩
    intro z hz
    exact ⟨hz.2.1, hz.1.2⟩
  exact (hlocal q ⟨hq.1, hx⟩).mono_of_mem_nhdsWithin hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.tensorFamily_normSq_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.tensorFamily_normSq_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.tensorFamily_normSq_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.tensorFamily_normSq_continuousOn

theorem ClosedSlab.riemannNorm_continuousOn {u v : ℝ} (G : P.ClosedSlab u v) :
    ContinuousOn (fun q : ℝ × P.Carrier =>
      Real.sqrt (normSq0S (G.flow.base.metric q.1) q.2 4 (G.flow.base.rm04 q.1 q.2)))
      (_root_.Set.Icc u v ×ˢ _root_.Set.univ) :=
  (P.tensorFamily_normSq_continuousOn G.equation.smoothMetric.metricTensor_cont
    G.equation.rm04Cont).sqrt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.riemannNorm_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.riemannNorm_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.riemannNorm_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.riemannNorm_continuousOn

theorem ClosedSlab.curvature_bound {u v : ℝ} (G : P.ClosedSlab u v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ _root_.Set.Icc u v, ∀ x : P.Carrier,
      Real.sqrt (normSq0S (G.flow.base.metric t) x 4 (G.flow.base.rm04 t x)) ≤ K := by
  have hcompact : IsCompact (_root_.Set.Icc u v ×ˢ (_root_.Set.univ : Set P.Carrier)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨K, hK⟩ := (hcompact.image_of_continuousOn (G.riemannNorm_continuousOn P)).bddAbove
  refine ⟨max K 0, le_max_right _ _, fun t ht x => ?_⟩
  exact (hK ⟨(t, x), ⟨ht, _root_.Set.mem_univ x⟩, rfl⟩).trans (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.curvature_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.curvature_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.curvature_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.curvature_bound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
