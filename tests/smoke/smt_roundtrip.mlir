// RUN: pia-opt %s | FileCheck %s

// CHECK-LABEL: smt.solver
// CHECK: smt.declare_fun "x" : !smt.bv<8>
// CHECK: smt.bv.add
// CHECK: smt.assert
smt.solver () : () -> () {
  %x = smt.declare_fun "x" : !smt.bv<8>
  %one = smt.bv.constant #smt.bv<1> : !smt.bv<8>
  %sum = smt.bv.add %x, %one : !smt.bv<8>
  %lt = smt.bv.cmp ult %sum, %x : !smt.bv<8>
  smt.assert %lt
}
