import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGram.JointSmoothness
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Spectral.PointwiseFlowDerivative
import Submission.DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.Regularity.JointChart
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.Defs
import Submission.DifferentialGeometry.Analysis.Integration.L2.Parametric.FiberInnerSmoothness
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Spectrum.EigenCombination
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.PartitionOfUnityNormComparison
import Submission.DifferentialGeometry.Analysis.Integration.L2.Hilbert.SmoothSectionMap
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.DeTurckRemainderPathTimeJet.JointSmoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

section FiniteOrderPairing

open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.TensorMultilinear
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem contMDiffWithinAt_curriedSection_prod_ofOrder {N : WithTop ℕ∞} {n : ℕ}
    {s : Set (M × ℝ)} {p₀ : M × ℝ}
    (T : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace (n + 1) I p.1)
    (hT : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
        (E := fun x : M => Tensor0SBundle.Tensor0SSpace (n + 1) I x) p.1 (T p)) s p₀) :
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p.1
        (tensor0SCurry (I := I) (M := M) n p.1 (T p))) s p₀ := by
  let : TopologicalSpace (_root_.Bundle.TotalSpace (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
      (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y)) :=
    tensor0SBundleTopology (n + 1)
  rw [Bundle.contMDiffWithinAt_totalSpace
    (F := E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
    (E := fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y)
    (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  have hT_at := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
    (E := fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y)
    (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))).mp hT |>.2
  have hcurry :
      ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
        𝓘(ℝ, E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E) N
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ) :=
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ
      ).toContinuousLinearEquiv.toContinuousLinearMap).contMDiff
  have hcomp := hcurry.contMDiffAt.comp_contMDiffWithinAt p₀ hT_at
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · have hbase : {p : M × ℝ | p.1 ∈ (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace n I y) p₀.1).baseSet} ∈ nhdsWithin p₀ s := by
      apply nhdsWithin_le_nhds
      apply (continuous_fst.continuousAt).preimage_mem_nhds
      exact (_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace n I y) p₀.1).open_baseSet.mem_nhds
        (_root_.FiberBundle.mem_baseSet_trivializationAt _ _ _)
    filter_upwards [hbase] with p hb
    have hpt := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun _ : M => T p) p₀.1 p.1 hb
    change (_root_.FiberBundle.trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p₀.1
        ⟨p.1, tensor0SCurry (I := I) (M := M) n p.1 (T p)⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
        ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y) p₀.1 ⟨p.1, T p⟩).2)
    exact hpt
  · have hpt := trivializationAt_homBundle_curriedSection_eq (I := I) (M := M)
      (fun _ : M => T p₀) p₀.1 p₀.1 (_root_.FiberBundle.mem_baseSet_trivializationAt _ _ _)
    change (_root_.FiberBundle.trivializationAt (E →L[ℝ] Tensor0SBundle.Tensor0SModel n ℝ E)
        (fun y : M => TangentSpace I y →L[ℝ] Tensor0SBundle.Tensor0SSpace n I y) p₀.1
        ⟨p₀.1, tensor0SCurry (I := I) (M := M) n p₀.1 (T p₀)⟩).2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ)
        ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel (n + 1) ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace (n + 1) I y) p₀.1 ⟨p₀.1, T p₀⟩).2)
    exact hpt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.contMDiffWithinAt_curriedSection_prod_ofOrder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.contMDiffWithinAt_curriedSection_prod_ofOrder target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem contMDiffWithinAt_section_apply_prod_ofOrder {N : WithTop ℕ∞} : ∀ (n : ℕ)
    {s : Set (M × ℝ)} {p₀ : M × ℝ}
    (T : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace n I p.1)
    (_hT : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
        (E := fun x : M => Tensor0SBundle.Tensor0SSpace n I x) p.1 (T p)) s p₀)
    (v : Fin n → ∀ p : M × ℝ, TangentSpace I p.1)
    (_hv : ∀ i, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) N
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun x : M => TangentSpace I x) p.1 (v i p)) s p₀),
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
      (fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.toModel (T p)
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) p.1 (v i p))) s p₀
  | 0, s, p₀, T, hT, v, _hv => by
    have hT_at := (Bundle.contMDiffWithinAt_totalSpace
      (F := Tensor0SBundle.Tensor0SModel 0 ℝ E)
      (E := fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y)
      (IB := I) (IM := I.prod 𝓘(ℝ, ℝ))).mp hT |>.2
    have hcurry :
        ContMDiff 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E) 𝓘(ℝ, ℝ) N
          (continuousMultilinearCurryFin0 ℝ E ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
          (fun p : M × ℝ =>
            (continuousMultilinearCurryFin0 ℝ E ℝ)
              ((_root_.FiberBundle.trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
                (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) p₀.1 ⟨p.1, T p⟩).2)) s p₀ :=
      hcurry.contMDiffAt.comp_contMDiffWithinAt p₀ hT_at
    refine hcomp.congr_of_eventuallyEq ?_ ?_
    · filter_upwards with p
      rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) (fun _ : M => T p) p₀.1 p.1]
      have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => E) ((T p) 0)) = (T p) 0 := by
        change (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T p) 0)) 0 = (T p) 0
        rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hev]
      have huniq :
          (fun i : Fin 0 => tangentSpaceModelContinuousLinearEquiv (I := I) p.1 (v i p)) =
            (0 : Fin 0 → E) := Subsingleton.elim _ _
      rw [huniq]
      rfl
    · rw [trivializationAt_tensor0SBundle_zero_fibre (I := I) (M := M) (fun _ : M => T p₀) p₀.1
      p₀.1]
      have hev : (continuousMultilinearCurryFin0 ℝ E ℝ)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => E) ((T p₀) 0)) = (T p₀) 0 := by
        change (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => E) ((T p₀) 0)) 0 = (T p₀) 0
        rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
      rw [hev]
      have huniq :
          (fun i : Fin 0 => tangentSpaceModelContinuousLinearEquiv (I := I) p₀.1 (v i p₀)) =
            (0 : Fin 0 → E) := Subsingleton.elim _ _
      rw [huniq]
      rfl
  | n + 1, s, p₀, T, hT, v, hv => by
    have hCurry := contMDiffWithinAt_curriedSection_prod_ofOrder (I := I) (M := M) T hT
    have hApplied : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel n ℝ E)) N
        (fun p : M × ℝ =>
          TotalSpace.mk' (Tensor0SBundle.Tensor0SModel n ℝ E)
            (E := fun x : M => Tensor0SBundle.Tensor0SSpace n I x) p.1
            ((tensor0SCurry (I := I) (M := M) n p.1 (T p)) (v 0 p))) s p₀ :=
      ContMDiffWithinAt.clm_bundle_apply (𝕜 := ℝ) (n := N)
        (F₁ := E) (F₂ := Tensor0SBundle.Tensor0SModel n ℝ E)
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => Tensor0SBundle.Tensor0SSpace n I x)
        (IM := I.prod 𝓘(ℝ, ℝ)) (IB := I)
        (b := Prod.fst) (ϕ := fun p : M × ℝ => tensor0SCurry (I := I) (M := M) n p.1 (T p))
        (v := fun p : M × ℝ => v 0 p)
        hCurry (hv 0)
    have hRec := contMDiffWithinAt_section_apply_prod_ofOrder n
      (s := s) (p₀ := p₀)
      (fun p : M × ℝ => (tensor0SCurry (I := I) (M := M) n p.1 (T p)) (v 0 p))
      hApplied
      (fun (i : Fin n) (p : M × ℝ) => v i.succ p)
      (fun i => hv i.succ)
    refine hRec.congr_of_eventuallyEq ?_ ?_
    · filter_upwards with p
      rw [tensor0S_curry_toModel_apply_tangent]
      refine Eq.symm ?_
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [Fin.cons_zero]
      · intro k; simp [Fin.cons_succ]
    · rw [tensor0S_curry_toModel_apply_tangent]
      refine Eq.symm ?_
      congr 1
      funext j
      refine Fin.cases ?_ ?_ j
      · simp [Fin.cons_zero]
      · intro k; simp [Fin.cons_succ]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.contMDiffWithinAt_section_apply_prod_ofOrder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.contMDiffWithinAt_section_apply_prod_ofOrder target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem chartTensorInnerPointwise_0s_jointContMDiffOn_args_ofOrder
    {N : WithTop ℕ∞} (hN : N ≤ (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M) (α : M) {T : ℝ} :
    ∀ (n : ℕ)
    (TT SS : M × ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (_hT : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
        (fun p : M × ℝ => (TT p) (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T))
    (_hS : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
        (fun p : M × ℝ => (SS p) (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
        (fun p : M × ℝ =>
          chartTensorInnerPointwise0s (I := I) (M := M) n g α p.1 (TT p) (SS p))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
  intro n
  induction n with
  | zero =>
      intro TT SS hT hS
      have heq : (fun p : M × ℝ =>
          chartTensorInnerPointwise0s (I := I) (M := M) 0 g α p.1 (TT p) (SS p)) =
          fun p : M × ℝ =>
            ((TT p) (fun i => Fin.elim0 i)) * ((SS p) (fun i => Fin.elim0 i)) := by
        funext p
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      have hT0 := hT (fun i : Fin 0 => Fin.elim0 i)
      have hS0 := hS (fun i : Fin 0 => Fin.elim0 i)
      have hempty :
          (fun k : Fin 0 => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))
            = (fun i : Fin 0 => (Fin.elim0 i : E)) := by
        funext i; exact Fin.elim0 i
      have hT_smooth :
          ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
            (fun p : M × ℝ => (TT p) (fun i => Fin.elim0 i))
            ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
        have : (fun p : M × ℝ => (TT p) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun p : M × ℝ => (TT p)
              (fun k : Fin 0 => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext p; congr 1; rw [hempty]
        rw [this]; exact hT0
      have hS_smooth :
          ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
            (fun p : M × ℝ => (SS p) (fun i => Fin.elim0 i))
            ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
        have : (fun p : M × ℝ => (SS p) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun p : M × ℝ => (SS p)
              (fun k : Fin 0 => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext p; congr 1; rw [hempty]
        rw [this]; exact hS0
      exact hT_smooth.mul hS_smooth
  | succ n ih =>
      intro TT SS hT hS
      have heq : (fun p : M × ℝ =>
          chartTensorInnerPointwise0s (I := I) (M := M) (n + 1) g α p.1 (TT p) (SS p)) =
          fun p : M × ℝ =>
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α p.1)⁻¹ i j *
                  chartTensorInnerPointwise0s (I := I) (M := M) n g α p.1
                    ((TT p).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
                    ((SS p).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) := by
        funext p
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finsetSum (fun i _ => ?_)
      refine contMDiffOn_finsetSum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · have hinv := chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
        have hbase_eq : (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
          trivializationAt_baseSet_eq_chartAt_source (I := I) α
        rw [hbase_eq] at hinv
        exact (hinv.of_le hN).comp contMDiffOn_fst (fun p hp => hp.1)
      · refine ih
            (fun p : M × ℝ => (TT p).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
            (fun p : M × ℝ => (SS p).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
            ?_ ?_
        · intro ψ
          set ψ' : Fin (n + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) i ψ with hψ'
          have heq' :
              (fun p : M × ℝ => ((TT p).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
                  (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (ψ k)))
                = fun p : M × ℝ =>
                    (TT p) (fun k : Fin (n + 1) => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (ψ' k)) := by
            funext p
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · simp [hψ']
            · intro k'; simp [hψ']
          rw [heq']
          exact hT ψ'
        · intro ψ
          set ψ' : Fin (n + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) j ψ with hψ'
          have heq' :
              (fun p : M × ℝ => ((SS p).curryLeft ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
                  (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (ψ k)))
                = fun p : M × ℝ =>
                    (SS p) (fun k : Fin (n + 1) => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (ψ' k)) := by
            funext p
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · simp [hψ']
            · intro k'; simp [hψ']
          rw [heq']
          exact hS ψ'

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.chartTensorInnerPointwise_0s_jointContMDiffOn_args_ofOrder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.chartTensorInnerPointwise_0s_jointContMDiffOn_args_ofOrder target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem loweredCompose_zero_basis_eval_jointContMDiffOn_ofOrder
    {N : WithTop ℕ∞} (hN : N ≤ (∞ : WithTop ℕ∞))
    (g : SmoothRiemannianMetric I M) (α : M) {T : ℝ}
    (Tval : ∀ p : M × ℝ, Tensor0SBundle.Tensor0SSpace 2 I p.1)
    (arm : M × ℝ → TensorRSModel 0 2 ℝ E)
    (harm : ∀ p : M × ℝ,
      arm p (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel (Tval p))
    (hTval : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1 (Tval p))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T))
    (φ : Fin (0 + 2) → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
      (fun p : M × ℝ =>
        (loweredCompose (I := I) (M := M) g 0 2 α p.1 (arm p))
          (fun k : Fin (0 + 2) => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
  have heval : ∀ p : M × ℝ,
      (loweredCompose (I := I) (M := M) g 0 2 α p.1 (arm p))
          (fun k : Fin (0 + 2) => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)) =
        Tensor0SBundle.Tensor0SSpace.toModel (Tval p)
          (fun j : Fin 2 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α
            (φ (Fin.natAdd 0 j)) p.1) := by
    intro p
    rw [loweredCompose_apply, lowerAllUpperIndices_apply, separableFormAt_zero, harm p]
    congr 1
  refine ContMDiffOn.congr ?_ (fun p _ => heval p)
  have hv : ∀ j : Fin 2, ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) p.1
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (φ (Fin.natAdd 0 j)) p.1))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro j
    have h := DifferentialGeometry.Geometry.Operator.chartBasisVec_jointContMDiffOn
      (I := I) α (φ (Fin.natAdd 0 j))
    exact h.mono (Set.prod_mono (subset_refl _) (Set.subset_univ _))
  intro p hp
  exact contMDiffWithinAt_section_apply_prod_ofOrder 2
    (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
    (p₀ := p) Tval (hTval p hp)
    (fun j p => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α (φ (Fin.natAdd 0 j)) p.1)
    (fun j => (hv j p hp).of_le hN)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.loweredCompose_zero_basis_eval_jointContMDiffOn_ofOrder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.loweredCompose_zero_basis_eval_jointContMDiffOn_ofOrder target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem tensorInnerPointwise_pair_section_jointContMDiffOn
    {N : WithTop ℕ∞} (hN : N ≤ (∞ : WithTop ℕ∞))
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (A B : ℝ → SmoothCcTensor g₀ 0 2)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((A p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) N
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((B p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          ((A p.2).toFun p.1) ((B p.2).toFun p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, t₀⟩ ⟨_, ht₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  have hinter : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
      ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ Set.Icc (0 : ℝ) T := by
    rw [Set.prod_inter_prod, Set.univ_inter, Set.inter_univ]
  rw [hinter]
  set α : M := x₀ with hα
  have hbridge : ∀ p ∈ (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T,
      DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          ((A p.2).toFun p.1) ((B p.2).toFun p.1) =
        chartTensorInnerPointwise0s (I := I) (M := M) (0 + 2) g₀ α p.1
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((A p.2).toFun p.1))
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((B p.2).toFun p.1)) := by
    rintro ⟨y, u⟩ ⟨hy, _⟩
    have hb : y ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α]; exact hy
    rw [tensorInnerPointwise_bridge_identity (I := I) (M := M) g₀ α 0 2 hb,
      chartTensorInnerPointwise_apply]
  refine ContMDiffOn.congr ?_ hbridge
  have hTvalOf : ∀ (C : ℝ → SmoothCcTensor g₀ 0 2),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) N
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((C p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) →
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) N
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
          ((C p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    intro C hC
    have hconst : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) :=
      contMDiff_constOfIsEmpty_tensor0S_section
    have hCP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E →L[ℝ]
          Tensor0SBundle.Tensor0SModel 2 ℝ E)) N
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E →L[ℝ]
            Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((C p.2).toSection p.1))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
      hC.mono (Set.prod_mono (fun y _ => Set.mem_univ y) (subset_refl _))
    have happ := ContMDiffOn.clm_bundle_apply (𝕜 := ℝ) (n := N)
      (F₁ := Tensor0SBundle.Tensor0SModel 0 ℝ E) (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z)
      (E₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
      (IM := I.prod 𝓘(ℝ, ℝ)) (IB := I)
      (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
      (b := Prod.fst) (ϕ := fun p : M × ℝ => ((C p.2).toSection p.1 : TensorRSSpace 0 2 I p.1))
      (v := fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))
      hCP ((hconst.contMDiffOn).of_le hN)
    refine happ.congr ?_
    rintro ⟨y, u⟩ _
    rfl
  have harmOf : ∀ (C : ℝ → SmoothCcTensor g₀ 0 2) (p : M × ℝ),
      (C p.2).toFun p.1
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((C p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))) := by
    intro C p
    rfl
  have hcoeff_A : ∀ φ : Fin (0 + 2) → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
        (fun p : M × ℝ =>
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((A p.2).toFun p.1))
            (fun k : Fin (0 + 2) => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
    fun φ => loweredCompose_zero_basis_eval_jointContMDiffOn_ofOrder (I := I) (M := M) hN g₀ α
      (fun p => (A p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ)))
      (fun p => (A p.2).toFun p.1) (harmOf A) (hTvalOf A hA) φ
  have hcoeff_B : ∀ φ : Fin (0 + 2) → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) N
        (fun p : M × ℝ =>
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((B p.2).toFun p.1))
            (fun k : Fin (0 + 2) => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
    fun φ => loweredCompose_zero_basis_eval_jointContMDiffOn_ofOrder (I := I) (M := M) hN g₀ α
      (fun p => (B p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ)))
      (fun p => (B p.2).toFun p.1) (harmOf B) (hTvalOf B hB) φ
  exact chartTensorInnerPointwise_0s_jointContMDiffOn_args_ofOrder (I := I) (M := M) hN g₀ α
    (0 + 2)
    (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((A p.2).toFun p.1))
    (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((B p.2).toFun p.1))
    hcoeff_A hcoeff_B

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorInnerPointwise_pair_section_jointContMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorInnerPointwise_pair_section_jointContMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorInnerPointwise_pair_section_jointContMDiffOn ``Submission.DifferentialGeometry.Analysis.Spectral.tensorInnerPointwise_pair_section_jointContMDiffOn

end FiniteOrderPairing

end Spectral
end Analysis
end DifferentialGeometry

end
