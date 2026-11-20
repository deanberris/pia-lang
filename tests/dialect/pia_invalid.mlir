// RUN: pia-opt %s --split-input-file --verify-diagnostics

// expected-error @+1 {{range lower bound exceeds upper bound}}
func.func @backwards(%a: !pia.int<10, 0>) { return }

// -----

// expected-error @+1 {{range must lie within [-2^63, 2^64 - 1]}}
func.func @too_wide(%a: !pia.int<0, 18446744073709551616>) { return }

// -----

func.func @constant_out_of_range() {
  // expected-error @+1 {{value is outside the range of '!pia.int<0, 255>'}}
  %c = pia.constant 256 : !pia.int<0, 255>
  return
}

// -----

func.func @load_wrong_type(%a: !pia.array<4 x f32>, %i: index) {
  // expected-error @+1 {{result type must be the buffer's element type}}
  %v = "pia.load"(%a, %i) : (!pia.array<4 x f32>, index) -> i32
  return
}

// -----

func.func @wrap_wrong_tag(%x: i32) {
  // expected-error @+1 {{'i32' is not one of the tags of '!pia.dyn<[f32]>'}}
  %d = pia.dyn.wrap %x : i32 -> !pia.dyn<[f32]>
  return
}

// -----

// expected-error @+1 {{invalid modifiers "in borrowed" on argument 0}}
func.func @modifier_order(%a: f32 {pia.modifiers = "in borrowed"}) { return }
