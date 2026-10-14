import Submission.DifferentialGeometry.Topology.LoopSpace.SmoothingC1
import Submission.DifferentialGeometry.Analysis.Calculus.Compactness.Superposition
import Submission.DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Families

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission










noncomputable section

open _root_.Set _root_.Function _root_.ContinuousMap _root_.Manifold
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Topology

variable {K F G : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]



theorem smoothPeriodic_uniform_C1_superposition (Γ : C(K, freeLoop F))
    (hΓ : ∀ k, ContDiff ℝ 1 (fun t : ℝ => Γ k (t : loopCircle)))
    (hd : Continuous (fun p : K × ℝ => deriv (fun t : ℝ => Γ p.1 (t : loopCircle)) p.2))
    {g : F → G} {U : Set F} (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (hmap : ∀ k θ, Γ k θ ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : ℝ), φ.rOut < δ → ∀ k t,
      DifferentialGeometry.Analysis.smoothPeriodic φ (fun s : ℝ => Γ k (s : loopCircle)) t ∈ U ∧
      _root_.Dist.dist (g (DifferentialGeometry.Analysis.smoothPeriodic φ (fun s : ℝ => Γ k (s : loopCircle)) t))
        (g (Γ k (t : loopCircle))) < ε ∧
      _root_.Dist.dist (deriv (fun x => g (DifferentialGeometry.Analysis.smoothPeriodic φ
          (fun s : ℝ => Γ k (s : loopCircle)) x)) t)
        (deriv (fun s : ℝ => g (Γ k (s : loopCircle))) t) < ε := by
  let D : K → freeLoop F := fun k => regularLoopDerivative (id : F → F) contMDiff_id
    ⟨Γ k, (hΓ k).contMDiff⟩
  have hD : Continuous D := continuous_periodicLoop_family hd _
  let c : K × loopCircle → F × F := fun p => (Γ p.1 p.2, D p.1 p.2)
  have hc : Continuous c := Γ.uncurry.continuous.prodMk
    ((FreeLoop.continuous_family_iff D).mp hD)
  let J : F × F → G × G := fun p => (g p.1, fderiv ℝ g p.1 p.2)
  have hJU : ContinuousOn J (U ×ˢ _root_.Set.univ) := by
    have h₀ : ContinuousOn (fun p : F × F => g p.1) (U ×ˢ _root_.Set.univ) :=
      hg.continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
    have h₁ : ContinuousOn (fun p : F × F => fderiv ℝ g p.1) (U ×ˢ _root_.Set.univ) :=
      (hg.continuousOn_fderiv_of_isOpen hU le_rfl).comp
      continuous_fst.continuousOn (fun p hp => hp.1)
    exact h₀.prodMk (h₁.clm_apply continuous_snd.continuousOn)
  have hcU : _root_.Set.range c ⊆ U ×ˢ univ := by
    rintro _ ⟨p, rfl⟩
    exact ⟨hmap p.1 p.2, _root_.Set.mem_univ _⟩
  obtain ⟨a, ha, haJ⟩ := DifferentialGeometry.Analysis.exists_uniform_superposition_radius
    hc (hU.prod isOpen_univ) hcU hJU hε
  obtain ⟨δ, hδ, hδΓ⟩ := smoothPeriodic_uniform_C1_approximation Γ hΓ hd ha
  refine ⟨δ, hδ, fun φ hφ k t => ?_⟩
  let b := DifferentialGeometry.Analysis.smoothPeriodic φ (fun s : ℝ => Γ k (s : loopCircle))
  have hbt := hδΓ φ hφ k t
  have hpair : _root_.Dist.dist (b t, deriv b t) (c (k, (t : loopCircle))) < a := by
    exact max_lt hbt.1 hbt.2
  obtain ⟨hbU, hJ⟩ := haJ (k, (t : loopCircle)) (b t, deriv b t) hpair
  have hb : ContDiff ℝ ∞ b := DifferentialGeometry.Analysis.smoothPeriodic_contDiff φ
    ((Γ k).continuous.comp (AddCircle.continuous_mk' (1 : ℝ)))
  have hgb := ((hg _ hbU.1).contDiffAt (hU.mem_nhds hbU.1)).differentiableAt one_ne_zero
  have hgo := ((hg _ (hmap k (t : loopCircle))).contDiffAt
    (hU.mem_nhds (hmap k (t : loopCircle)))).differentiableAt one_ne_zero
  have hdnew : deriv (fun x => g (b x)) t = fderiv ℝ g (b t) (deriv b t) :=
    (hgb.hasFDerivAt.comp_hasDerivAt t ((hb.differentiable (by simp)) t).hasDerivAt).deriv
  have hdold : deriv (fun s : ℝ => g (Γ k (s : loopCircle))) t =
      fderiv ℝ g (Γ k (t : loopCircle)) (deriv (fun s : ℝ => Γ k (s : loopCircle)) t) :=
    (hgo.hasFDerivAt.comp_hasDerivAt t ((hΓ k).differentiable one_ne_zero t).hasDerivAt).deriv
  change _root_.Max.max (_root_.Dist.dist (g (b t)) (g (Γ k (t : loopCircle))))
    (_root_.Dist.dist (fderiv ℝ g (b t) (deriv b t))
      (fderiv ℝ g (Γ k (t : loopCircle)) (deriv (fun s : ℝ => Γ k (s : loopCircle)) t))) < ε at hJ
  refine ⟨hbU.1, (max_lt_iff.mp hJ).1, ?_⟩
  rw [hdnew, hdold]
  exact (max_lt_iff.mp hJ).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.smoothPeriodic_uniform_C1_superposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.smoothPeriodic_uniform_C1_superposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.smoothPeriodic_uniform_C1_superposition ``Submission.DifferentialGeometry.Topology.smoothPeriodic_uniform_C1_superposition

end DifferentialGeometry.Topology
