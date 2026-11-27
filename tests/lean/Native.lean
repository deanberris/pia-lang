import Statements

namespace Native

-- `native_decide` evaluates the decision with Lean's compiler, so the
-- proof depends on an axiom it adds, `product._native.native_decide.ax_1_1`
-- in Lean 4.36, which says what the compiler computed: only a `@trusted` Pia file may
-- use it (ADR 0061, section 4).
theorem product : native_trusted.product := by native_decide

end Native
