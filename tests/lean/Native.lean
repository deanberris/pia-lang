import Statements

namespace Native

-- `native_decide` evaluates the decision with Lean's compiler, so the
-- proof depends on `Lean.ofReduceBool`: only a `@trusted` Pia file may
-- use it (ADR 0061, section 4).
theorem product : native_trusted.product := by native_decide

end Native
