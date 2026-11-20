// RUN: pia-opt %s --canonicalize | FileCheck %s

// The length of a fixed array folds to a constant.
// CHECK-LABEL: func.func @len
// CHECK: %[[C:.*]] = arith.constant 16 : index
// CHECK: return %[[C]]
func.func @len(%a: !pia.array<16 x !pia.int<0, 255>>) -> index {
  %n = pia.len %a : !pia.array<16 x !pia.int<0, 255>>
  return %n : index
}
