// RUN: pia-opt %s | FileCheck %s
// RUN: pia-opt %s | pia-opt | FileCheck %s
// RUN: pia-opt %s --mlir-print-op-generic | pia-opt | FileCheck %s

// A recursive variant (ADR 0047): the leaf type !pia.rec<"tree">, whose
// constructors and payloads the module's pia.datatype lists in tag order.
// CHECK-DAG: !tree_Node = !pia.record<"tree_Node", left : !pia.slice<!pia.rec<"tree">>, key : !pia.int<0, 255>>
// CHECK: pia.datatype @tree ctors ["Leaf", "Node"] payloads [none, !tree_Node]
pia.datatype @tree ctors ["Leaf", "Node"] payloads [none, !pia.record<"tree_Node", left : !pia.slice<!pia.rec<"tree">>, key : !pia.int<0, 255>>]

// CHECK-LABEL: func.func @leaf
// CHECK: pia.rec_make "Leaf" : <"tree">
func.func @leaf() -> !pia.rec<"tree"> {
  %t = pia.rec_make "Leaf" : !pia.rec<"tree">
  return %t : !pia.rec<"tree">
}

// CHECK-LABEL: func.func @node
// CHECK: pia.rec_make "Node"(%{{.*}} : !tree_Node) : <"tree">
func.func @node(%p: !pia.record<"tree_Node", left : !pia.slice<!pia.rec<"tree">>, key : !pia.int<0, 255>>) -> !pia.rec<"tree"> {
  %t = pia.rec_make "Node"(%p : !pia.record<"tree_Node", left : !pia.slice<!pia.rec<"tree">>, key : !pia.int<0, 255>>) : !pia.rec<"tree">
  return %t : !pia.rec<"tree">
}

// After ScalarizeRecords a record payload is its fields.
// CHECK-LABEL: func.func @flat
// CHECK: pia.rec_make "Node"(%{{.*}}, %{{.*}} : !pia.slice<!pia.rec<"tree">>, !pia.int<0, 255>) : <"tree">
// CHECK: pia.rec_tag %{{.*}} : <"tree"> -> <0, 1>
// CHECK: pia.rec_payload %{{.*}}, "Node" : <"tree"> -> (!pia.slice<!pia.rec<"tree">>, !pia.int<0, 255>)
func.func @flat(%l: !pia.slice<!pia.rec<"tree">>, %k: !pia.int<0, 255>) -> !pia.int<0, 255> {
  %t = pia.rec_make "Node"(%l, %k : !pia.slice<!pia.rec<"tree">>, !pia.int<0, 255>) : !pia.rec<"tree">
  %tag = pia.rec_tag %t : !pia.rec<"tree"> -> !pia.int<0, 1>
  %p:2 = pia.rec_payload %t, "Node" : !pia.rec<"tree"> -> (!pia.slice<!pia.rec<"tree">>, !pia.int<0, 255>)
  return %p#1 : !pia.int<0, 255>
}

// `depth t` and `size t`, spec-only ints.
// CHECK-LABEL: func.func @measures
// CHECK: pia.rec_measure "depth" %{{.*}} : <"tree">
// CHECK: pia.rec_measure "size" %{{.*}} : <"tree">
func.func @measures(%t: !pia.rec<"tree">) -> !pia.integer {
  %d = pia.rec_measure "depth" %t : !pia.rec<"tree">
  %s = pia.rec_measure "size" %t : !pia.rec<"tree">
  return %d : !pia.integer
}
