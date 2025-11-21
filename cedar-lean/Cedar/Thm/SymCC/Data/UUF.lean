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

import Cedar.SymCC.Env

/-! Some facts about `UUF.*_id`s. -/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Spec
open Cedar.SymCC

theorem uuf_attrs_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.attrsId ety₁ ≠ UUF.ancsId ety₂ ancTy
:= by
  intro h
  have htake := congrArg (fun s => s.toList.take 2) h
  have h₁ : 2 ≤ ("attrs[" : String).toList.length := by decide
  have h₂ : 2 ≤ ("ancs[" : String).toList.length := by decide
  have hprefix := by
    simpa [UUF.attrsId, UUF.ancsId, toString, List.take_append_of_le_length, h₁, h₂]
      using htake
  have hneq : ("attrs[" : String).toList.take 2 ≠ ("ancs[" : String).toList.take 2 := by decide
  exact hneq hprefix

theorem uuf_attrs_tag_keys_no_confusion
  {ety₁ ety₂} :
  UUF.attrsId ety₁ ≠ UUF.tagKeysId ety₂
:= by
  intro h
  have htake := congrArg (fun s => s.toList.take 1) h
  have h₁ : 1 ≤ ("attrs[" : String).toList.length := by decide
  have h₂ : 1 ≤ ("tagKeys[" : String).toList.length := by decide
  have hprefix := by
    simpa [UUF.attrsId, UUF.tagKeysId, toString, List.take_append_of_le_length, h₁, h₂]
      using htake
  have hneq : ("attrs[" : String).toList.take 1 ≠ ("tagKeys[" : String).toList.take 1 := by decide
  exact hneq hprefix

theorem uuf_attrs_tag_vals_no_confusion
  {ety₁ ety₂} :
  UUF.attrsId ety₁ ≠ UUF.tagValsId ety₂
:= by
  intro h
  have htake := congrArg (fun s => s.toList.take 1) h
  have h₁ : 1 ≤ ("attrs[" : String).toList.length := by decide
  have h₂ : 1 ≤ ("tagVals[" : String).toList.length := by decide
  have hprefix := by
    simpa [UUF.attrsId, UUF.tagValsId, toString, List.take_append_of_le_length, h₁, h₂]
      using htake
  have hneq : ("attrs[" : String).toList.take 1 ≠ ("tagVals[" : String).toList.take 1 := by decide
  exact hneq hprefix

theorem uuf_tag_vals_tag_keys_no_confusion
  {ety₁ ety₂} :
  UUF.tagValsId ety₁ ≠ UUF.tagKeysId ety₂
:= by
  intro h
  have htake := congrArg (fun s => s.toList.take 4) h
  have h₁ : 4 ≤ ("tagVals[" : String).toList.length := by decide
  have h₂ : 4 ≤ ("tagKeys[" : String).toList.length := by decide
  have hprefix := by
    simpa [UUF.tagKeysId, UUF.tagValsId, toString, List.take_append_of_le_length, h₁, h₂]
      using htake
  have hneq : ("tagVals[" : String).toList.take 4 ≠ ("tagKeys[" : String).toList.take 4 := by decide
  exact hneq hprefix

theorem uuf_tag_keys_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.tagKeysId ety₁ ≠ UUF.ancsId ety₂ ancTy
:= by
  intro h
  have htake := congrArg (fun s => s.toList.take 1) h
  have h₁ : 1 ≤ ("tagKeys[" : String).toList.length := by decide
  have h₂ : 1 ≤ ("ancs[" : String).toList.length := by decide
  have hprefix := by
    simpa [UUF.tagKeysId, UUF.ancsId, toString, List.take_append_of_le_length, h₁, h₂]
      using htake
  have hneq : ("tagKeys[" : String).toList.take 1 ≠ ("ancs[" : String).toList.take 1 := by decide
  exact hneq hprefix

theorem uuf_tag_vals_ancs_no_confusion
  {ety₁ ety₂ ancTy} :
  UUF.tagValsId ety₁ ≠ UUF.ancsId ety₂ ancTy
:= by
  intro h
  have htake := congrArg (fun s => s.toList.take 1) h
  have h₁ : 1 ≤ ("tagVals[" : String).toList.length := by decide
  have h₂ : 1 ≤ ("ancs[" : String).toList.length := by decide
  have hprefix := by
    simpa [UUF.tagValsId, UUF.ancsId, toString, List.take_append_of_le_length, h₁, h₂]
      using htake
  have hneq : ("tagVals[" : String).toList.take 1 ≠ ("ancs[" : String).toList.take 1 := by decide
  exact hneq hprefix

end Cedar.Thm
