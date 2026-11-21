// RUN: pia-opt %s --canonicalize | FileCheck %s

// The length of a fixed array folds to a constant.
// CHECK-LABEL: func.func @len
// CHECK: %[[C:.*]] = arith.constant 16 : index
// CHECK: return %[[C]]
func.func @len(%a: !pia.array<16 x !pia.int<0, 255>>) -> index {
  %n = pia.len %a : !pia.array<16 x !pia.int<0, 255>>
  return %n : index
}

// A field of a record just built is the value it was built from.
// CHECK-LABEL: func.func @field_of_record
// CHECK-NEXT: return %arg1
func.func @field_of_record(%a: !pia.int<0, 255>, %b: i1) -> i1 {
  %p = pia.record(%a, %b : !pia.int<0, 255>, i1) : !pia.record<"p", x : !pia.int<0, 255>, y : i1>
  %y = pia.field %p, "y" : !pia.record<"p", x : !pia.int<0, 255>, y : i1> -> i1
  return %y : i1
}
