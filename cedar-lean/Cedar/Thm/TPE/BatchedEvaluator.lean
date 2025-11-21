/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/


import Cedar.TPE.Input
import Cedar.TPE.BatchedEvaluator
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.Validation
import Cedar.Thm.TPE
import Cedar.Thm.Data.Map

/-!
This file defines theorems related to the batched evaluator.
-/

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm
open Cedar.Data

/-- A well behaved entity loader.

1. Loads all the requested entities, returning `none` for missing entities.
2. Refines the backing entity store via `MaybeEntityData.asPartial`.

The first condition is required for convergence of batched evaluation,
which has not been proven yet. It is currently unused in the proofs below,
but is part of the intended specification of an entity loader.
-/
abbrev EntityLoader.WellBehaved (store : Entities) (loader : EntityLoader) : Prop :=
  ∀ s, s ⊆ (loader s).keys ∧
       EntitiesRefine store ((loader s).mapOnValues MaybeEntityData.asPartial)

/-- A concrete request refines its partial counterpart that is obtained by
`Request.asPartialRequest`. -/
theorem as_partial_request_refines {req : Request} :
  RequestRefines req req.asPartialRequest := by
  simp [RequestRefines, Request.asPartialRequest, PartialEntityUID.asEntityUID]
  exact
    ⟨PartialIsValid.some _ _ rfl,
      ⟨PartialIsValid.some _ _ rfl,
        PartialIsValid.some _ _ rfl⟩⟩

/-- Any entity store refines the empty partial store. -/
theorem any_refines_empty_entities (es : Entities) :
  EntitiesRefine es (Map.empty : PartialEntities) := by
  intro uid data h_find
  have h := by
    simpa [Map.empty, Map.find?] using h_find
  cases h

/-- Helper lemma: appending partial stores preserves entity refinement. -/
theorem entities_refine_append
  (es : Entities) (m₁ m₂ : PartialEntities) :
  EntitiesRefine es m₁ →
  EntitiesRefine es m₂ →
  EntitiesRefine es (m₁ ++ m₂) := by
  classical
  intro h₁ h₂ uid data h_find
  have h_or : (m₁.find? uid).or (m₂.find? uid) = some data := by
    simpa [Data.Map.find?_append] using h_find
  cases h_case : m₁.find? uid with
  | some data₁ =>
      have h_eq : data₁ = data := by
        simpa [Option.or, h_case] using h_or
      cases h_eq
      exact h₁ uid data h_case
  | none =>
      have h_find₂ : m₂.find? uid = some data := by
        simpa [Option.or, h_case] using h_or
      exact h₂ uid data h_find₂

/-- A concrete request and entity store refine their partial counterparts. -/
theorem direct_request_and_entities_refine (req : Request) (es : Entities) :
  RequestAndEntitiesRefine req es req.asPartialRequest es.asPartial := by
  constructor
  · exact as_partial_request_refines
  · intro uid data h_find
    have h_map := Data.Map.find?_mapOnValues_some' EntityData.asPartial h_find
    rcases h_map with ⟨data₁, h_find₁, h_eq⟩
    subst h_eq
    have h_attrs : PartialIsValid (fun x => x = data₁.attrs) (some data₁.attrs) :=
      PartialIsValid.some _ _ rfl
    have h_ancestors : PartialIsValid (fun x => x = data₁.ancestors) (some data₁.ancestors) :=
      PartialIsValid.some _ _ rfl
    have h_tags : PartialIsValid (fun x => x = data₁.tags) (some data₁.tags) :=
      PartialIsValid.some _ _ rfl
    refine ⟨data₁, h_find₁, ?_, ?_, ?_⟩
    · simpa [EntityData.asPartial]
        using h_attrs
    · simpa [EntityData.asPartial]
        using h_ancestors
    · simpa [EntityData.asPartial]
        using h_tags

/--
Running `batchedEvalLoop` preserves the evaluation result of the current residual.
-/
theorem batched_eval_loop_eq_evaluate
  (loader : EntityLoader)
  (es : Entities)
  {req : Request}
  {env : TypeEnv}
  (h_loader : EntityLoader.WellBehaved es loader)
  (h_env : InstanceOfWellFormedEnvironment req es env) :
  ∀ {x : Residual} {current_store : PartialEntities},
    Residual.WellTyped env x →
    RequestAndEntitiesRefine req es req.asPartialRequest current_store →
    ∀ iters,
      (Residual.evaluate (batchedEvalLoop x req loader current_store iters) req es).toOption =
        (Residual.evaluate x req es).toOption := by
  intro x current_store h_wt h_refine iters
  induction iters generalizing x current_store with
  | zero =>
      simp [batchedEvalLoop]
  | succ iters ih =>
      classical
      rcases h_refine with ⟨h_req_refine, h_store_refine⟩
      let toLoad := x.allLiteralUIDs.filter fun uid => (current_store.find? uid).isNone
      have h_toLoad : x.allLiteralUIDs.filter (fun uid => (current_store.find? uid).isNone) = toLoad := rfl
      let newEntities := (loader toLoad).mapOnValues MaybeEntityData.asPartial
      have h_newEntities : (loader toLoad).mapOnValues MaybeEntityData.asPartial = newEntities := rfl
      let newStore := newEntities ++ current_store
      have h_newStore : newEntities ++ current_store = newStore := rfl
      obtain ⟨_, h_new_entities_refine⟩ := h_loader toLoad
      have h_store_refine' : EntitiesRefine es newStore :=
        by
          simpa [h_newStore, h_newEntities] using
            entities_refine_append es
              ((loader toLoad).mapOnValues MaybeEntityData.asPartial)
              current_store
              h_new_entities_refine
              h_store_refine
      have h_refine_new :
        RequestAndEntitiesRefine req es req.asPartialRequest newStore :=
          ⟨h_req_refine, h_store_refine'⟩
      have h_eval_eq :=
        (partial_evaluate_is_sound
          (x := x)
          (req := req)
          (es := es)
          (preq := req.asPartialRequest)
          (pes := newStore)
          (env := env)
          h_wt
          h_env
          h_refine_new).symm
      have h_wt_newRes :
        Residual.WellTyped env (Cedar.TPE.evaluate x req.asPartialRequest newStore) :=
          partial_eval_preserves_well_typed h_env h_refine_new h_wt
      generalize h_evalRes : Cedar.TPE.evaluate x req.asPartialRequest newStore = res
      have h_eval_eq' := by
        simpa [h_evalRes, h_newStore, h_newEntities] using h_eval_eq
      have h_wt_res : Residual.WellTyped env res := by
        simpa [h_evalRes, h_newStore, h_newEntities] using h_wt_newRes
      have h_rec := ih h_wt_res h_refine_new
      cases res with
      | val v ty =>
          simpa [batchedEvalLoop, h_toLoad, h_newEntities, h_newStore, h_evalRes, Residual.evaluate]
            using h_eval_eq'
      | var v ty
      | ite cond thenExpr elseExpr ty
      | and a b ty
      | or a b ty
      | unaryApp op expr ty
      | binaryApp op a b ty
      | getAttr expr attr ty
      | hasAttr expr attr ty
      | set ls ty
      | record map ty
      | call xfn args ty
      | error ty =>
          simp [batchedEvalLoop, h_toLoad, h_newEntities, h_newStore, h_evalRes] at h_rec ⊢
          exact h_rec.trans h_eval_eq'

/--
The main correctness theorem for batched evaluation: batched evaluation with an
entity loader produces the same authorization result as evaluating the original
expression with the complete entity store.
-/
theorem batched_eval_eq_evaluate
  (loader : EntityLoader)
  {iters : Nat}
  {x : TypedExpr}
  {req : Request}
  {es : Entities}
  {env : TypeEnv} :
  EntityLoader.WellBehaved es loader →
  TypedExpr.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  (Residual.evaluate (batchedEvaluate x req loader iters) req es).toOption =
    (Spec.evaluate x.toExpr req es).toOption := by
  intro h_loader h_typed h_env
  classical
  have h_refine_empty :
      RequestAndEntitiesRefine req es req.asPartialRequest (Map.empty : PartialEntities) :=
    ⟨as_partial_request_refines, any_refines_empty_entities es⟩
  have h_residual_wt :
      Residual.WellTyped env (Cedar.TPE.evaluate x.toResidual req.asPartialRequest Map.empty) :=
    partial_eval_preserves_well_typed h_env h_refine_empty (conversion_preserves_typedness h_typed)
  have h_loop :=
    batched_eval_loop_eq_evaluate
      (loader := loader)
      (es := es)
      (req := req)
      (env := env)
      h_loader
      h_env
      (x := Cedar.TPE.evaluate x.toResidual req.asPartialRequest Map.empty)
      (current_store := Map.empty)
      h_residual_wt
      h_refine_empty
      iters
  have h_sound :=
    partial_evaluate_is_sound
      (x := TypedExpr.toResidual x)
      (req := req)
      (es := es)
      (preq := req.asPartialRequest)
      (pes := Map.empty)
      (env := env)
      (conversion_preserves_typedness h_typed)
      h_env
      h_refine_empty
  have h_conv :=
    congrArg Except.toOption (conversion_preserves_evaluation x req es)
  calc
    (Residual.evaluate (batchedEvaluate x req loader iters) req es).toOption
        = (Residual.evaluate (Cedar.TPE.evaluate x.toResidual req.asPartialRequest Map.empty) req es).toOption := by
            simpa [batchedEvaluate] using h_loop
    _ = (Residual.evaluate (TypedExpr.toResidual x) req es).toOption := by
            simpa using h_sound.symm
    _ = (Spec.evaluate x.toExpr req es).toOption := by
            simpa using h_conv.symm

end Cedar.Thm
