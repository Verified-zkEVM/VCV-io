/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import ToMathlib.MeasureTheory.Measure.Option
public import ToMathlib.MeasureTheory.MeasurableSpace.Except

/-!
# Function-property registrations for optional and exception-valued observations

The spaces are arbitrary measurable spaces. These tests exercise composition through registered
function heads without relying on a discrete-space instance.
-/

public section

open MeasureTheory

namespace VCVioTest.FunProp

variable {α β ε : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace ε]

example {f : α → β} (hf : Measurable f) : Measurable (Option.map (Option.map f)) := by
  fun_prop

example {f : α → β} (hf : Measurable f) (b : β) :
    Measurable (fun x : Option α => x.elim b f) := by
  fun_prop

example {f : α → β} (hf : Measurable f) :
    Measurable (fun x : Option α => (x.map f).elim (0 : Measure β) Measure.dirac) := by
  fun_prop

example {f : α → β} (hf : Measurable f) :
    Measurable (Option.map (Except.map (ε := ε) f)) := by
  fun_prop

example {f : α → β} (hf : Measurable f) : Measurable (Option.map f) := by
  fail_if_success solve | clear hf; fun_prop
  fun_prop

end VCVioTest.FunProp
