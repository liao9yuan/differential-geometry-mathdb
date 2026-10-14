import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import Submission.DifferentialGeometry.Geometry.Connection.Realization.SmoothSectionsLocal
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.IteratedComponents

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable (P : OrientedThreeStage.{u})

theorem spatialLift_contMDiffOn {U : Set P.Carrier} {V : Set ℝ}
    (X : (x : P.Carrier) → TangentSpace ThreeModel x)
    (hX : ContMDiffOn ThreeModel (ThreeModel.prod 𝓘(ℝ, ThreeSpace)) ∞
      (fun x => TotalSpace.mk' ThreeSpace x (X x)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      ((𝓘(ℝ, ℝ).prod ThreeModel).prod 𝓘(ℝ, ℝ × ThreeSpace)) ∞
      (fun q : ℝ × P.Carrier =>
        (⟨q, (0, X q.2)⟩ : TangentBundle (𝓘(ℝ, ℝ).prod ThreeModel) (ℝ × P.Carrier)))
      (V ×ˢ U) := by
  have hzero : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × P.Carrier =>
        (⟨q.1, (0 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) (V ×ˢ U) :=
    ((Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)).comp
      contMDiff_fst).contMDiffOn
  have hspace : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace)) ∞
      (fun q : ℝ × P.Carrier => TotalSpace.mk' ThreeSpace q.2 (X q.2)) (V ×ˢ U) :=
    hX.comp contMDiff_snd.contMDiffOn (fun _ hq => hq.2)
  exact contMDiff_equivTangentBundleProd_symm.comp_contMDiffOn (hzero.prodMk hspace)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.spatialLift_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.spatialLift_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.spatialLift_contMDiffOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.spatialLift_contMDiffOn

theorem spatialDerivative_contMDiffOn {U : Set P.Carrier} {V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (f : ℝ × P.Carrier → ℝ)
    (X : (x : P.Carrier) → TangentSpace ThreeModel x)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞ f (V ×ˢ U))
    (hX : ContMDiffOn ThreeModel (ThreeModel.prod 𝓘(ℝ, ThreeSpace)) ∞
      (fun x => TotalSpace.mk' ThreeSpace x (X x)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × P.Carrier =>
        mvfderiv (I := ThreeModel) (fun x => f (q.1, x)) q.2 (X q.2)) (V ×ˢ U) := by
  have hlift := P.spatialLift_contMDiffOn (V := V) X hX
  have hderiv : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × P.Carrier =>
        mvfderiv (I := 𝓘(ℝ, ℝ).prod ThreeModel) f q (0, X q.2)) (V ×ˢ U) :=
    fun q hq => (contMDiffAt_mvfderiv_apply (hV.prod hU) hq hf hlift).contMDiffWithinAt
  apply hderiv.congr
  intro q hq
  have hdf := (hf.contMDiffAt ((hV.prod hU).mem_nhds hq)).mdifferentiableAt (by simp)
  have hchain := mvfderiv_comp_apply q.2 hdf
    (mdifferentiableAt_const.prodMk mdifferentiableAt_id) (X q.2)
  simp only [id_eq, mfderiv_prod_right] at hchain
  exact hchain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.spatialDerivative_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.spatialDerivative_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.spatialDerivative_contMDiffOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.spatialDerivative_contMDiffOn

theorem spatialIterCovComp_contMDiffOn {U : Set P.Carrier} {V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) {r : ℕ}
    (frame : Fin 3 → (x : P.Carrier) → TangentSpace ThreeModel x)
    (chr : P.Carrier → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (base : ℝ × P.Carrier → (Fin r → Fin 3) → ℝ)
    (hframe : ∀ d, ContMDiffOn ThreeModel (ThreeModel.prod 𝓘(ℝ, ThreeSpace)) ∞
      (fun x => TotalSpace.mk' ThreeSpace x (frame d x)) U)
    (hchr : ∀ d i j, ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ (fun x => chr x d i j) U)
    (hbase : ∀ m, ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q => base q m) (V ×ˢ U)) (a : ℕ) :
    ∀ n : Fin (r + a) → Fin 3,
      ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × P.Carrier => iterCovComp (I := ThreeModel) frame chr
          (fun x => base (q.1, x)) a q.2 n) (V ×ˢ U) := by
  induction a with
  | zero => exact hbase
  | succ a ih =>
    intro n
    change ContMDiffOn _ _ ∞
      (fun q : ℝ × P.Carrier =>
        mvfderiv (I := ThreeModel)
          (fun x => iterCovComp (I := ThreeModel) frame chr
            (fun y => base (q.1, y)) a x (Fin.tail n)) q.2 (frame (n 0) q.2) -
        ∑ s : Fin (r + a), ∑ p : Fin 3,
          chr q.2 (n 0) (Fin.tail n s) p *
            iterCovComp (I := ThreeModel) frame chr (fun y => base (q.1, y))
              a q.2 (Function.update (Fin.tail n) s p)) (V ×ˢ U)
    refine (P.spatialDerivative_contMDiffOn hU hV _ _
      (ih (Fin.tail n)) (hframe (n 0))).sub ?_
    intro q hq
    refine ContMDiffWithinAt.sum fun s _ => ContMDiffWithinAt.sum fun p _ => ?_
    have hc : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × P.Carrier => chr q.2 (n 0) (Fin.tail n s) p) (V ×ˢ U) :=
      (hchr (n 0) (Fin.tail n s) p).comp contMDiff_snd.contMDiffOn (fun _ hq => hq.2)
    exact (hc.mul (ih (Function.update (Fin.tail n) s p))) q hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.spatialIterCovComp_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.spatialIterCovComp_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.spatialIterCovComp_contMDiffOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.spatialIterCovComp_contMDiffOn

theorem localFrame_christoffel_contMDiffOn (p : P.Carrier) (gRef : P.Metric)
    (b : Module.Basis (Fin 3) ℝ ThreeSpace) :
    let e := _root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p
    ∀ i j k : Fin 3, ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞
      (fun x => christoffelSymbolInFrame (leviCivitaConnectionOfMetric gRef)
        (e.localFrame b) (e.isLocalFrameOn_localFrame_baseSet ThreeModel 1 b) x i j k)
      e.baseSet := by
  intro e i j k
  have hf := e.isLocalFrameOn_localFrame_baseSet ThreeModel ∞ b
  have hcov := leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally gRef
  have hD := (hcov e.open_baseSet).contMDiff (by
    simpa using hf.contMDiffOn j)
  have hA := hD.clm_bundle_apply (hf.contMDiffOn i)
  exact contMDiffOn_baseSet_localFrameCoeff (e := e) b hA k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.localFrame_christoffel_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.localFrame_christoffel_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.localFrame_christoffel_contMDiffOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.localFrame_christoffel_contMDiffOn

private theorem localFrame_euclidean_eq_chartVector (p x : P.Carrier)
    (hx : x ∈ (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)
    (i : Fin 3) :
    (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).localFrame
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i x = P.chartVector p x i := by
  rw [Trivialization.localFrame_apply_of_mem_baseSet _ _ hx]
  change _ = (_root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p).symmL ℝ x _
  rw [Trivialization.symmL_apply _ hx]
  simp [Trivialization.basisAt]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.localFrame_euclidean_eq_chartVector
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.localFrame_euclidean_eq_chartVector target :: scope.openDecls } }

theorem MetricSmoothUpTo.exists_covariantComponent_extension
    {g : ℝ → P.Metric} {J : Set ℝ} (hg : P.MetricSmoothUpTo g J)
    (gRef : P.Metric) (p : P.Carrier) {t : ℝ} (ht : t ∈ J) (a : ℕ) :
    let e := _root_.FiberBundle.trivializationAt ThreeSpace (TangentSpace ThreeModel) p
    let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    let frame := e.localFrame b
    let chr := fun x => christoffelSymbolInFrame (leviCivitaConnectionOfMetric gRef)
      frame (e.isLocalFrameOn_localFrame_baseSet ThreeModel 1 b) x
    ∃ U : Set P.Carrier, IsOpen U ∧ p ∈ U ∧ U ⊆ e.baseSet ∧
      ∃ V : Set ℝ, IsOpen V ∧ t ∈ V ∧
        ∃ A : ℝ × P.Carrier → (Fin (2 + a) → Fin 3) → ℝ,
          (∀ n, ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun q => A q n) (V ×ˢ U)) ∧
          ∀ s ∈ V ∩ J, ∀ x ∈ U, ∀ n,
            A (s, x) n = iterCovComp (I := ThreeModel) frame chr
              (frameComp0S (metricTensorField (g s)) frame) a x n := by
  intro e b frame chr
  obtain ⟨U, hU, hpU, hUb, V, hV, htV, B, hB, heq⟩ := hg p t ht
  let base : ℝ × P.Carrier → (Fin 2 → Fin 3) → ℝ :=
    fun q n => B q (n 0) (n 1)
  let A : ℝ × P.Carrier → (Fin (2 + a) → Fin 3) → ℝ :=
    fun q n => iterCovComp (I := ThreeModel) frame chr (fun x => base (q.1, x)) a q.2 n
  refine ⟨U, hU, hpU, hUb, V, hV, htV, A, ?_, ?_⟩
  · exact P.spatialIterCovComp_contMDiffOn hU hV frame chr base
      (fun i => ((e.isLocalFrameOn_localFrame_baseSet ThreeModel ∞ b).contMDiffOn i).mono hUb)
      (fun i j k => (P.localFrame_christoffel_contMDiffOn p gRef b i j k).mono hUb)
      (fun n => hB (n 0) (n 1)) a
  · intro s hs x hx n
    apply congrFun (iterCovComp_congr_on (I := ThreeModel) hU frame chr (fun y hy => ?_) a x hx) n
    funext m
    change B (s, y) (m 0) (m 1) =
      (g s).inner y (frame (m 0) y) (frame (m 1) y)
    rw [heq s hs y hy]
    dsimp only [frame, e, b]
    rw [localFrame_euclidean_eq_chartVector P p y (hUb hy),
      localFrame_euclidean_eq_chartVector P p y (hUb hy)]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.exists_covariantComponent_extension then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.exists_covariantComponent_extension"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.exists_covariantComponent_extension ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.exists_covariantComponent_extension

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
