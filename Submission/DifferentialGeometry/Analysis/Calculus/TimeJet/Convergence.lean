import Submission.DifferentialGeometry.Analysis.Calculus.ProdWithin
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Topology.UniformSpace.UniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem deriv_prod_fst_eq_fderivWithin
    {f : ℝ × ℝ → E} {s : Set ℝ} {q : ℝ × ℝ}
    (hf : DifferentiableWithinAt ℝ f (_root_.Set.univ ×ˢ s) q) (hq : q.2 ∈ s) :
    deriv (fun x => f (x, q.2)) q.1 =
      fderivWithin ℝ f (_root_.Set.univ ×ˢ s) q (1, 0) := by
  simpa only [derivWithin_univ] using
    Calculus.derivWithin_prod_fst_of_hasFDerivWithinAt f
      (fderivWithin ℝ f (_root_.Set.univ ×ˢ s) q) hq uniqueDiffWithinAt_univ
      hf.hasFDerivWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.deriv_prod_fst_eq_fderivWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.deriv_prod_fst_eq_fderivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.deriv_prod_fst_eq_fderivWithin ``Submission.DifferentialGeometry.Analysis.deriv_prod_fst_eq_fderivWithin

theorem derivWithin_prod_snd_eq_fderivWithin
    {f : ℝ × ℝ → E} {s : Set ℝ} {q : ℝ × ℝ}
    (hs : UniqueDiffWithinAt ℝ s q.2)
    (hf : DifferentiableWithinAt ℝ f (_root_.Set.univ ×ˢ s) q) :
    derivWithin (fun t => f (q.1, t)) s q.2 =
      fderivWithin ℝ f (_root_.Set.univ ×ˢ s) q (0, 1) := by
  have hh : HasDerivWithinAt (fun t : ℝ => (q.1, t)) ((0, 1) : ℝ × ℝ) s q.2 :=
    (hasDerivWithinAt_const q.2 s q.1).prodMk (hasDerivWithinAt_id q.2 s)
  exact (hf.hasFDerivWithinAt.comp_hasDerivWithinAt (t := _root_.Set.univ ×ˢ s) q.2 hh
    (fun _ ht => ⟨mem_univ _, ht⟩)).derivWithin hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.derivWithin_prod_snd_eq_fderivWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.derivWithin_prod_snd_eq_fderivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.derivWithin_prod_snd_eq_fderivWithin ``Submission.DifferentialGeometry.Analysis.derivWithin_prod_snd_eq_fderivWithin

theorem deriv_deriv_prod_fst_eq_iteratedFDerivWithin
    {f : ℝ × ℝ → E} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hf : ContDiffOn ℝ 2 f (_root_.Set.univ ×ˢ s)) {q : ℝ × ℝ} (hq : q.2 ∈ s) :
    deriv (deriv (fun x => f (x, q.2))) q.1 =
      iteratedFDerivWithin ℝ 2 f (_root_.Set.univ ×ˢ s) q (fun _ => (1, 0)) := by
  have hu : UniqueDiffOn ℝ (_root_.Set.univ ×ˢ s) := (uniqueDiffOn_univ : UniqueDiffOn ℝ (_root_.Set.univ : Set ℝ)).prod hs
  have hd : DifferentiableOn ℝ f (_root_.Set.univ ×ˢ s) := hf.differentiableOn (by norm_num)
  have hfd : DifferentiableOn ℝ (fderivWithin ℝ f (_root_.Set.univ ×ˢ s)) (_root_.Set.univ ×ˢ s) :=
    (hf.fderivWithin hu (m := 1) (by norm_num)).differentiableOn (by norm_num)
  have hfun : deriv (fun x => f (x, q.2)) =
      fun x => fderivWithin ℝ f (_root_.Set.univ ×ˢ s) (x, q.2) (1, 0) := by
    funext x
    exact deriv_prod_fst_eq_fderivWithin (hd (x, q.2) ⟨mem_univ _, hq⟩) hq
  rw [hfun, iteratedFDerivWithin_two_apply f hu ⟨mem_univ _, hq⟩]
  have hh : HasDerivAt (fun x : ℝ => (x, q.2)) ((1, 0) : ℝ × ℝ) q.1 :=
    (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  have hcomp := (hfd q ⟨mem_univ _, hq⟩).hasFDerivWithinAt.comp_hasDerivAt (t := _root_.Set.univ ×ˢ s) q.1 hh
    (Eventually.of_forall fun _ => ⟨mem_univ _, hq⟩)
  simpa only [Function.comp_apply, map_zero, add_zero] using
    (hcomp.clm_apply (hasDerivAt_const q.1 ((1, 0) : ℝ × ℝ))).deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.deriv_deriv_prod_fst_eq_iteratedFDerivWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.deriv_deriv_prod_fst_eq_iteratedFDerivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.deriv_deriv_prod_fst_eq_iteratedFDerivWithin ``Submission.DifferentialGeometry.Analysis.deriv_deriv_prod_fst_eq_iteratedFDerivWithin

theorem tendstoUniformlyOn_of_iteratedFDerivWithin_zero
    {ι X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {l : Filter ι} {f : ι → X → E} {g : X → E} {s K : Set X}
    (h : TendstoUniformlyOn (fun j => iteratedFDerivWithin ℝ 0 (f j) s)
      (iteratedFDerivWithin ℝ 0 g s) l K) :
    TendstoUniformlyOn f g l K := by
  have hh := (ContinuousMultilinearMap.uniformContinuous_eval_const (fun _ : Fin 0 => (0 : X))).comp_tendstoUniformlyOn h
  simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendstoUniformlyOn_of_iteratedFDerivWithin_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendstoUniformlyOn_of_iteratedFDerivWithin_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendstoUniformlyOn_of_iteratedFDerivWithin_zero ``Submission.DifferentialGeometry.Analysis.tendstoUniformlyOn_of_iteratedFDerivWithin_zero

theorem tendstoUniformlyOn_spacetime_derivatives_of_iteratedFDerivWithin
    {ι : Type*} {l : Filter ι} {f : ι → ℝ × ℝ → E} {g : ℝ × ℝ → E}
    {s : Set ℝ} {K : Set (ℝ × ℝ)} (hs : UniqueDiffOn ℝ s)
    (hK : K ⊆ _root_.Set.univ ×ˢ s)
    (hf : ∀ᶠ j in l, ContDiffOn ℝ 2 (f j) (_root_.Set.univ ×ˢ s))
    (hg : ContDiffOn ℝ 2 g (_root_.Set.univ ×ˢ s))
    (h : ∀ m ≤ 2, TendstoUniformlyOn (fun j => iteratedFDerivWithin ℝ m (f j) (_root_.Set.univ ×ˢ s))
      (iteratedFDerivWithin ℝ m g (_root_.Set.univ ×ˢ s)) l K) :
    TendstoUniformlyOn f g l K ∧
    TendstoUniformlyOn (fun j q => deriv (fun x => f j (x, q.2)) q.1)
      (fun q => deriv (fun x => g (x, q.2)) q.1) l K ∧
    TendstoUniformlyOn (fun j q => derivWithin (fun t => f j (q.1, t)) s q.2)
      (fun q => derivWithin (fun t => g (q.1, t)) s q.2) l K ∧
    TendstoUniformlyOn (fun j q => deriv (deriv (fun x => f j (x, q.2))) q.1)
      (fun q => deriv (deriv (fun x => g (x, q.2))) q.1) l K := by
  have hu : UniqueDiffOn ℝ (_root_.Set.univ ×ˢ s) := (uniqueDiffOn_univ : UniqueDiffOn ℝ (_root_.Set.univ : Set ℝ)).prod hs
  refine ⟨tendstoUniformlyOn_of_iteratedFDerivWithin_zero (h 0 (by omega)), ?_, ?_, ?_⟩
  · have hh := (ContinuousMultilinearMap.uniformContinuous_eval_const
        (fun _ : Fin 1 => ((1, 0) : ℝ × ℝ))).comp_tendstoUniformlyOn (h 1 (by omega))
    refine (hh.congr ?_).congr_right ?_
    · filter_upwards [hf] with j hj q hq
      dsimp only [Function.comp_apply]
      rw [iteratedFDerivWithin_one_apply (hu q (hK hq))]
      exact (deriv_prod_fst_eq_fderivWithin (hj.differentiableOn (by norm_num) q (hK hq)) (hK hq).2).symm
    · intro q hq
      dsimp only [Function.comp_apply]
      rw [iteratedFDerivWithin_one_apply (hu q (hK hq))]
      exact (deriv_prod_fst_eq_fderivWithin (hg.differentiableOn (by norm_num) q (hK hq)) (hK hq).2).symm
  · have hh := (ContinuousMultilinearMap.uniformContinuous_eval_const
        (fun _ : Fin 1 => ((0, 1) : ℝ × ℝ))).comp_tendstoUniformlyOn (h 1 (by omega))
    refine (hh.congr ?_).congr_right ?_
    · filter_upwards [hf] with j hj q hq
      dsimp only [Function.comp_apply]
      rw [iteratedFDerivWithin_one_apply (hu q (hK hq))]
      exact (derivWithin_prod_snd_eq_fderivWithin (hs q.2 (hK hq).2)
        (hj.differentiableOn (by norm_num) q (hK hq))).symm
    · intro q hq
      dsimp only [Function.comp_apply]
      rw [iteratedFDerivWithin_one_apply (hu q (hK hq))]
      exact (derivWithin_prod_snd_eq_fderivWithin (hs q.2 (hK hq).2)
        (hg.differentiableOn (by norm_num) q (hK hq))).symm
  · have hh := (ContinuousMultilinearMap.uniformContinuous_eval_const
        (fun _ : Fin 2 => ((1, 0) : ℝ × ℝ))).comp_tendstoUniformlyOn (h 2 le_rfl)
    refine (hh.congr ?_).congr_right ?_
    · filter_upwards [hf] with j hj q hq
      exact (deriv_deriv_prod_fst_eq_iteratedFDerivWithin hs hj (hK hq).2).symm
    · intro q hq
      exact (deriv_deriv_prod_fst_eq_iteratedFDerivWithin hs hg (hK hq).2).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendstoUniformlyOn_spacetime_derivatives_of_iteratedFDerivWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendstoUniformlyOn_spacetime_derivatives_of_iteratedFDerivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendstoUniformlyOn_spacetime_derivatives_of_iteratedFDerivWithin ``Submission.DifferentialGeometry.Analysis.tendstoUniformlyOn_spacetime_derivatives_of_iteratedFDerivWithin

end DifferentialGeometry.Analysis
end

noncomputable section

open _root_.Set _root_.Filter

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuousOn_spacetime_derivatives
    {f : ℝ × ℝ → E} {s : Set ℝ} (hs : UniqueDiffOn ℝ s)
    (hf : ContDiffOn ℝ 2 f (_root_.Set.univ ×ˢ s)) :
    ContinuousOn (fun q : ℝ × ℝ =>
      (f q, deriv (fun x => f (x, q.2)) q.1,
        deriv (deriv (fun x => f (x, q.2))) q.1,
        derivWithin (fun t => f (q.1, t)) s q.2)) (_root_.Set.univ ×ˢ s) := by
  have hu : UniqueDiffOn ℝ (_root_.Set.univ ×ˢ s) :=
    (uniqueDiffOn_univ : UniqueDiffOn ℝ (_root_.Set.univ : Set ℝ)).prod hs
  have hd : ContinuousOn (fderivWithin ℝ f (_root_.Set.univ ×ˢ s)) (_root_.Set.univ ×ˢ s) :=
    hf.continuousOn_fderivWithin hu (by norm_num)
  have hx : ContinuousOn (fun q : ℝ × ℝ => deriv (fun x => f (x, q.2)) q.1)
      (_root_.Set.univ ×ˢ s) := by
    apply (hd.clm_apply (continuousOn_const (c := ((1, 0) : ℝ × ℝ)))).congr
    intro q hq
    exact deriv_prod_fst_eq_fderivWithin (hf.differentiableOn (by norm_num) q hq) hq.2
  have ht : ContinuousOn
      (fun q : ℝ × ℝ => derivWithin (fun t => f (q.1, t)) s q.2) (_root_.Set.univ ×ˢ s) := by
    apply (hd.clm_apply (continuousOn_const (c := ((0, 1) : ℝ × ℝ)))).congr
    intro q hq
    exact derivWithin_prod_snd_eq_fderivWithin (hs q.2 hq.2)
      (hf.differentiableOn (by norm_num) q hq)
  have hxx : ContinuousOn
      (fun q : ℝ × ℝ => deriv (deriv (fun x => f (x, q.2))) q.1) (_root_.Set.univ ×ˢ s) := by
    have hjet := hf.continuousOn_iteratedFDerivWithin (m := 2) le_rfl hu
    have heval := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (fun _ : Fin 2 => ((1, 0) : ℝ × ℝ))).continuous.comp_continuousOn hjet
    apply heval.congr
    intro q hq
    exact deriv_deriv_prod_fst_eq_iteratedFDerivWithin hs hf hq.2
  exact hf.continuousOn.prodMk (hx.prodMk (hxx.prodMk ht))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuousOn_spacetime_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuousOn_spacetime_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuousOn_spacetime_derivatives ``Submission.DifferentialGeometry.Analysis.continuousOn_spacetime_derivatives

private theorem tendstoUniformlyOn_prod_same_index
    {ι X Y Z : Type*} [UniformSpace Y] [UniformSpace Z]
    {l : Filter ι} {s : Set X} {f : ι → X → Y} {g : X → Y}
    {f' : ι → X → Z} {g' : X → Z}
    (h : TendstoUniformlyOn f g l s) (h' : TendstoUniformlyOn f' g' l s) :
    TendstoUniformlyOn (fun j x => (f j x, f' j x)) (fun x => (g x, g' x)) l s := by
  intro u hu
  exact (tendsto_id.prodMk _root_.Filter.tendsto_id).eventually ((h.prodMk h') u hu)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.tendstoUniformlyOn_prod_same_index
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.tendstoUniformlyOn_prod_same_index target :: scope.openDecls } }

theorem tendstoUniformlyOn_spacetime_derivatives_prod_of_iteratedFDerivWithin
    {ι : Type*} {l : Filter ι} {f : ι → ℝ × ℝ → E} {g : ℝ × ℝ → E}
    {s : Set ℝ} {K : Set (ℝ × ℝ)} (hs : UniqueDiffOn ℝ s)
    (hK : K ⊆ _root_.Set.univ ×ˢ s)
    (hf : ∀ᶠ j in l, ContDiffOn ℝ 2 (f j) (_root_.Set.univ ×ˢ s))
    (hg : ContDiffOn ℝ 2 g (_root_.Set.univ ×ˢ s))
    (h : ∀ m ≤ 2, TendstoUniformlyOn (fun j => iteratedFDerivWithin ℝ m (f j) (_root_.Set.univ ×ˢ s))
      (iteratedFDerivWithin ℝ m g (_root_.Set.univ ×ˢ s)) l K) :
    TendstoUniformlyOn (fun j q =>
      (f j q, deriv (fun x => f j (x, q.2)) q.1,
        deriv (deriv (fun x => f j (x, q.2))) q.1,
        derivWithin (fun t => f j (q.1, t)) s q.2))
      (fun q => (g q, deriv (fun x => g (x, q.2)) q.1,
        deriv (deriv (fun x => g (x, q.2))) q.1,
        derivWithin (fun t => g (q.1, t)) s q.2)) l K := by
  obtain ⟨hv, hx, ht, hxx⟩ :=
    tendstoUniformlyOn_spacetime_derivatives_of_iteratedFDerivWithin hs hK hf hg h
  exact tendstoUniformlyOn_prod_same_index hv
    (tendstoUniformlyOn_prod_same_index hx (tendstoUniformlyOn_prod_same_index hxx ht))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendstoUniformlyOn_spacetime_derivatives_prod_of_iteratedFDerivWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendstoUniformlyOn_spacetime_derivatives_prod_of_iteratedFDerivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendstoUniformlyOn_spacetime_derivatives_prod_of_iteratedFDerivWithin ``Submission.DifferentialGeometry.Analysis.tendstoUniformlyOn_spacetime_derivatives_prod_of_iteratedFDerivWithin

end DifferentialGeometry.Analysis
end
