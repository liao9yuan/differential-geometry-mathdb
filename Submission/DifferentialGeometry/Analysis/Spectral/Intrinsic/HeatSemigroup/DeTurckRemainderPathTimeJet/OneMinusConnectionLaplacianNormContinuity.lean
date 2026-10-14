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
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
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

section OneMinusConnLapNormSqContinuity

open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.TensorMultilinear
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.Tensor.Tensor0SRiemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem jointTotalSpaceRS_sub {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p))
          ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p))
          ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  let := Tensor0SBundle.tensorRSBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := _root_.FiberBundle.trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.jointTotalSpaceRS_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.jointTotalSpaceRS_sub target :: scope.openDecls } }

private theorem oneMinusConnLapSmooth_section_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (Sfam : ℝ → SmoothCcTensor g₀ 0 2) (S : Set ℝ)
    (hSfam : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((oneMinusConnLapSmooth (I := I) g₀ 0 2 (Sfam p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  have hraw := MetricRealization.rawTensorConnLapSmooth_jointContMDiffOn (I := I) (M := M)
    g₀ Sfam S hSfam
  have hsub := jointTotalSpaceRS_sub (I := I) (r := 0) (s := 2) (S := S)
    (fun p => (Sfam p.2).toSection p.1)
    (fun p => (rawTensorConnLapSmooth (I := I) g₀ 0 2 (Sfam p.2)).toSection p.1)
    hSfam hraw
  refine hsub.congr ?_
  intro p _
  have hsec : (oneMinusConnLapSmooth (I := I) g₀ 0 2 (Sfam p.2)).toSection p.1
      = (Sfam p.2).toSection p.1
        - (rawTensorConnLapSmooth (I := I) g₀ 0 2 (Sfam p.2)).toSection p.1 := by
    rw [show oneMinusConnLapSmooth (I := I) g₀ 0 2 (Sfam p.2)
          = Sfam p.2 - rawTensorConnLapSmooth (I := I) g₀ 0 2 (Sfam p.2) from rfl,
      SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [hsec]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_section_jointContMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_section_jointContMDiffOn target :: scope.openDecls } }

private theorem oneMinusConnLapSmoothIter_section_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (Sfam : ℝ → SmoothCcTensor g₀ 0 2) (S : Set ℝ) (k : ℕ)
    (hSfam : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Sfam p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) := by
  induction k with
  | zero => simpa using hSfam
  | succ k ih =>
      have hstep := oneMinusConnLapSmooth_section_jointContMDiffOn (I := I) (M := M) g₀
        (fun u => oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Sfam u)) S ih
      refine hstep.congr ?_
      intro p _
      rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_section_jointContMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_section_jointContMDiffOn target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem tensorInnerPointwise_diag_section_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (Sfam : ℝ → SmoothCcTensor g₀ 0 2)
    (hSfam : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        DifferentialGeometry.Integral.L2.tensorInnerPointwise (I := I) (M := M) g₀ 0 2 p.1
          ((Sfam p.2).toFun p.1) ((Sfam p.2).toFun p.1))
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
          ((Sfam p.2).toFun p.1) ((Sfam p.2).toFun p.1) =
        chartTensorInnerPointwise0s (I := I) (M := M) (0 + 2) g₀ α p.1
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((Sfam p.2).toFun p.1))
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((Sfam p.2).toFun p.1)) := by
    rintro ⟨y, u⟩ ⟨hy, _⟩
    have hb : y ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I) α]; exact hy
    rw [tensorInnerPointwise_bridge_identity (I := I) (M := M) g₀ α 0 2 hb,
      chartTensorInnerPointwise_apply]
  refine ContMDiffOn.congr ?_ hbridge
  have harm : ∀ p : M × ℝ,
      (Sfam p.2).toFun p.1
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((Sfam p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))) := by
    intro p
    rfl
  have hTval : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z) p.1
        ((Sfam p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ))))
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    have hconst : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (E := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z) p.1
          (Tensor0SBundle.Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))) :=
      contMDiff_constOfIsEmpty_tensor0S_section
    have hSfamP : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.Tensor0SModel 0 ℝ E →L[ℝ]
          Tensor0SBundle.Tensor0SModel 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel 0 ℝ E →L[ℝ]
            Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
      hSfam.mono (Set.prod_mono (fun y _ => Set.mem_univ y) (subset_refl _))
    have happ := ContMDiffOn.clm_bundle_apply (𝕜 := ℝ) (n := (∞ : WithTop ℕ∞))
      (F₁ := Tensor0SBundle.Tensor0SModel 0 ℝ E) (F₂ := Tensor0SBundle.Tensor0SModel 2 ℝ E)
      (E₁ := fun z : M => Tensor0SBundle.Tensor0SSpace 0 I z)
      (E₂ := fun z : M => Tensor0SBundle.Tensor0SSpace 2 I z)
      (IM := I.prod 𝓘(ℝ, ℝ)) (IB := I)
      (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
      (b := Prod.fst) (ϕ := fun p : M × ℝ => ((Sfam p.2).toSection p.1 : TensorRSSpace 0 2 I p.1))
      (v := fun p : M × ℝ => Tensor0SBundle.Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))
      hSfamP (hconst.contMDiffOn)
    refine happ.congr ?_
    rintro ⟨y, u⟩ _
    rfl
  have hcoeff_S : ∀ φ : Fin (0 + 2) → Fin (Module.finrank ℝ E),
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : M × ℝ =>
          (loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((Sfam p.2).toFun p.1))
            (fun k : Fin (0 + 2) => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)))
        ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) :=
    fun φ => loweredCompose_zero_basis_eval_jointContMDiffOn (I := I) (M := M) g₀ α
      (fun p => (Sfam p.2).toSection p.1 (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p.1) (1 : ℝ)))
      (fun p => (Sfam p.2).toFun p.1) harm hTval φ
  exact chartTensorInnerPointwise_0s_jointContMDiffOn_smooth_args (I := I) (M := M) g₀ α
    (0 + 2)
    (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((Sfam p.2).toFun p.1))
    (fun p => loweredCompose (I := I) (M := M) g₀ 0 2 α p.1 ((Sfam p.2).toFun p.1))
    hcoeff_S hcoeff_S

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.tensorInnerPointwise_diag_section_jointContMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.tensorInnerPointwise_diag_section_jointContMDiffOn target :: scope.openDecls } }

theorem deTurckRHSReconSection_oneMinusConnLapIter_normSq_continuousOn
    (g₀ : SmoothRiemannianMetric I M) {T : ℝ}
    (Rjt : ℝ → SmoothCcTensor g₀ 0 2) (k : ℕ)
    (hRjt : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Rjt p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T)) :
    ContinuousOn
      (fun t => ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2)
        (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t))‖ ^ 2)
      (Set.Icc (0 : ℝ) T) := by
  classical
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have : _root_.MeasureTheory.IsFiniteMeasure
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) g₀
    with hμ
  set Sfam : ℝ → SmoothCcTensor g₀ 0 2 :=
    fun t => oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (Rjt t) with hSfam
  have hSfam_joint :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1 ((Sfam p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) :=
    oneMinusConnLapSmoothIter_section_jointContMDiffOn (I := I) (M := M) g₀ Rjt
      (Set.Icc (0 : ℝ) T) k hRjt
  have hdiag := tensorInnerPointwise_diag_section_jointContMDiffOn (I := I) (M := M) g₀ Sfam
    hSfam_joint
  have hnormeq : (fun t : ℝ => ‖SmoothCcTensor.toL2 (g := g₀) (r := 0) (s := 2) (Sfam t)‖ ^ 2)
      = fun t : ℝ => ∫ x, DifferentialGeometry.Integral.L2.tensorInnerPointwise
          (I := I) (M := M) g₀ 0 2 x ((Sfam t).toFun x) ((Sfam t).toFun x) ∂μ := by
    funext t
    rw [SmoothCcTensor.norm_toL2,
      Analysis.Parabolic.TensorSpectral.SmoothCcTensor.norm_sq_eq_inner_self]
    rfl
  rw [hnormeq]
  have hcd := contDiffOn_integral_of_jointContMDiffOn_Icc (I := I) (M := M) μ
    (fun x t => DifferentialGeometry.Integral.L2.tensorInnerPointwise
      (I := I) (M := M) g₀ 0 2 x ((Sfam t).toFun x) ((Sfam t).toFun x)) hdiag
  exact hcd.continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.deTurckRHSReconSection_oneMinusConnLapIter_normSq_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.deTurckRHSReconSection_oneMinusConnLapIter_normSq_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.deTurckRHSReconSection_oneMinusConnLapIter_normSq_continuousOn ``Submission.DifferentialGeometry.Analysis.Spectral.deTurckRHSReconSection_oneMinusConnLapIter_normSq_continuousOn

end OneMinusConnLapNormSqContinuity

end Spectral
end Analysis
end DifferentialGeometry

end
