import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.LocalMapsTransport
import Submission.DifferentialGeometry.Topology.Manifold.Orientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {n : ℕ} {M N P Q : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin n)) P] [IsManifold (𝓡 n) ∞ P]
  [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q] [IsManifold (𝓡 n) ∞ Q]

theorem localDiffeomorph_orientation_of_comp_eq
    (f : M → P) (g : N → Q)
    (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f)
    (hg : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ g)
    (F : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (G : Diffeomorph (𝓡 n) (𝓡 n) P Q ∞)
    (heq : (G : P → Q) ∘ f = g ∘ (F : M → N))
    (oM : ManifoldOrientation (𝓡 n) M n) (oN : ManifoldOrientation (𝓡 n) N n)
    (oP : ManifoldOrientation (𝓡 n) P n) (oQ : ManifoldOrientation (𝓡 n) Q n)
    (hF : F.preservesOrientation oM oN) (hG : G.preservesOrientation oP oQ)
    (hgO : ∀ x, Orientation.map (Fin n)
      (hg.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
        (oN.orientation x) = oQ.orientation (g x)) :
    ∀ x, Orientation.map (Fin n)
      (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
        (oM.orientation x) = oP.orientation (f x) := by
  intro x
  let A := (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  let B := (G.mfderivToContinuousLinearEquiv (by simp) (f x)).toLinearEquiv
  let C := (F.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  let D := (hg.mfderivToContinuousLinearEquiv (by simp) (F x)).toLinearEquiv
  have hlin : A.trans B = C.trans D := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 n) (𝓡 n) G (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) =
      mfderiv (𝓡 n) (𝓡 n) g (F x) (mfderiv (𝓡 n) (𝓡 n) F x v)
    rw [← mfderiv_comp_apply x (G.mdifferentiable (by simp) _) (hf.mdifferentiable (by simp) _) v,
      ← mfderiv_comp_apply x (hg.mdifferentiable (by simp) _) (F.mdifferentiable (by simp) _) v]
    exact congrArg (fun k : M → Q => mfderiv (𝓡 n) (𝓡 n) k x v) heq
  change Orientation.map (Fin n) A (oM.orientation x) = oP.orientation (f x)
  apply (Orientation.map (Fin n) B).injective
  erw [DifferentialGeometry.VectorBundle.map_orientation_trans_between, hlin,
    ← DifferentialGeometry.VectorBundle.map_orientation_trans_between]
  have hFx : Orientation.map (Fin n) C (oM.orientation x) = oN.orientation (F x) := hF x
  erw [hFx]
  have hgx : Orientation.map (Fin n) D (oN.orientation (F x)) = oQ.orientation (g (F x)) :=
    hgO (F x)
  erw [hgx]
  have hGx : Orientation.map (Fin n) B (oP.orientation (f x)) = oQ.orientation (G (f x)) :=
    hG (f x)
  erw [hGx]
  congr 1
  exact (congrFun heq x).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.localDiffeomorph_orientation_of_comp_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.localDiffeomorph_orientation_of_comp_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.localDiffeomorph_orientation_of_comp_eq ``Submission.DifferentialGeometry.Topology.Manifold.localDiffeomorph_orientation_of_comp_eq

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SelfAttachment.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SelfAttachment.E3 target :: scope.openDecls } }

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N] [T2Space N]
  (c d : BallChart 3 (𝓡 3) M) (c' d' : BallChart 3 (𝓡 3) N)
  (F : Diffeomorph (𝓡 3) (𝓡 3) M N ∞)
  (hc : ∀ x ∈ Metric.closedBall (0 : E3) 2, F (c.chart x) = c'.chart x)
  (hd : ∀ x ∈ Metric.closedBall (0 : E3) 2, F (d.chart x) = d'.chart x)

theorem coreInteriorDiffeomorphOfChartTransport_preservesOrientation
    (oM : ManifoldOrientation (𝓡 3) M 3) (oN : ManifoldOrientation (𝓡 3) N 3)
    (hF : F.preservesOrientation oM oN) :
    (coreInteriorDiffeomorphOfChartTransport c d c' d' F hc hd).preservesOrientation
      (oM.restrictOpen (coreInterior c d)) (oN.restrictOpen (coreInterior c' d')) := by
  intro x
  let C := coreInteriorDiffeomorphOfChartTransport c d c' d' F hc hd
  have hder : (C.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
      (F.mfderivToContinuousLinearEquiv (by simp) x.val).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 3) (𝓡 3) C x v = mfderiv (𝓡 3) (𝓡 3) F x.val v
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp C x]
    exact congrArg (fun L => L v)
      (DifferentialGeometry.mfderiv_restrict_open (I := 𝓡 3) (J := 𝓡 3)
        (F : M → N) (coreInterior c d) x)
  change Orientation.map (Fin 3) (C.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
    (oM.orientation x.val) = oN.orientation (F x.val)
  rw [hder]
  exact hF x.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.coreInteriorDiffeomorphOfChartTransport_preservesOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.coreInteriorDiffeomorphOfChartTransport_preservesOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.coreInteriorDiffeomorphOfChartTransport_preservesOrientation ``Submission.DifferentialGeometry.Topology.SelfAttachment.coreInteriorDiffeomorphOfChartTransport_preservesOrientation


variable
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (hcd' : Disjoint (c'.chart '' Metric.closedBall 0 2) (d'.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))
  [ChartedSpace E3 (Quotient c' d' hcd' a)] [IsManifold (𝓡 3) ∞ (Quotient c' d' hcd' a)]

theorem core_orientation_of_chart_transport
    (oM : ManifoldOrientation (𝓡 3) M 3) (oN : ManifoldOrientation (𝓡 3) N 3)
    (hF : F.preservesOrientation oM oN)
    (O' : ManifoldOrientation (𝓡 3) (Quotient c' d' hcd' a) 3)
    (hcore' : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (coreInteriorInclusion c' d' hcd' a))
    (hcoreO' : ∀ x, Orientation.map (Fin 3)
      (hcore'.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
        (oN.orientation x.val) = O'.orientation (coreInteriorInclusion c' d' hcd' a x)) :
    let Hq := homeomorphOfChartTransport c d c' d' hcd hcd' F.toHomeomorph hc hd a
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := E3) Hq
    let _ := DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback (I := 𝓡 3) (n := ∞) Hq
    let G := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph (I := 𝓡 3) (n := ∞) Hq
    ∀ (O : ManifoldOrientation (𝓡 3) (Quotient c d hcd a) 3),
      G.preservesOrientation O O' →
      ∀ (hcore : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (coreInteriorInclusion c d hcd a)),
      ∀ x, Orientation.map (Fin 3)
        (hcore.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
          (oM.orientation x.val) = O.orientation (coreInteriorInclusion c d hcd a x) := by
  intro Hq _ _ G O hG hcore
  exact Manifold.localDiffeomorph_orientation_of_comp_eq
    (coreInteriorInclusion c d hcd a) (coreInteriorInclusion c' d' hcd' a)
    hcore hcore' (coreInteriorDiffeomorphOfChartTransport c d c' d' F hc hd) G
    (funext (homeomorphOfChartTransport_coreInterior c d c' d' F hc hd hcd hcd' a))
    (oM.restrictOpen (coreInterior c d)) (oN.restrictOpen (coreInterior c' d')) O O'
    (coreInteriorDiffeomorphOfChartTransport_preservesOrientation c d c' d' F hc hd oM oN hF)
    hG hcoreO'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SelfAttachment.core_orientation_of_chart_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SelfAttachment.core_orientation_of_chart_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SelfAttachment.core_orientation_of_chart_transport ``Submission.DifferentialGeometry.Topology.SelfAttachment.core_orientation_of_chart_transport

end DifferentialGeometry.Topology.SelfAttachment
