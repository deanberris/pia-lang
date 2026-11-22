// RUN: pia-opt %s | FileCheck %s
// RUN: pia-opt %s | pia-opt | FileCheck %s
// RUN: pia-opt %s --mlir-print-op-generic | pia-opt | FileCheck %s

// Inside pia ops, MLIR prints operands and results constrained to
// !pia.int or !pia.dyn in short form, without the dialect prefix
// (`<0, 255>`). The parser accepts both spellings. The two 64-bit ranges
// print as the aliases !isize and !usize, defined at the top.
// CHECK-DAG: !isize = !pia.int<-9223372036854775808, 9223372036854775807>
// CHECK-DAG: !usize = !pia.int<0, 18446744073709551615>
// CHECK-DAG: !pixel = !pia.record<"pixel", r : !pia.int<0, 255>, g : !pia.int<0, 255>>

// The saturating pixel add from docs/design.md:
//   let add_px (a : u8) (b : u8) : u8 @overflow(saturate) = a + b
// CHECK-LABEL: func.func @add_px
// CHECK-SAME: (%{{.*}}: !pia.int<0, 255>, %{{.*}}: !pia.int<0, 255>) -> !pia.int<0, 255>
// CHECK: pia.add %{{.*}}, %{{.*}} overflow(saturate) : <0, 255>, <0, 255> -> <0, 255>
func.func @add_px(%a: !pia.int<0, 255>, %b: !pia.int<0, 255>) -> !pia.int<0, 255> {
  %r = pia.add %a, %b overflow(saturate) : !pia.int<0, 255>, !pia.int<0, 255> -> !pia.int<0, 255>
  return %r : !pia.int<0, 255>
}

// The default overflow mode is proof, and is not printed.
// CHECK-LABEL: func.func @bad
// CHECK: pia.add %{{.*}}, %{{.*}} : <0, 255>, <0, 255> -> <0, 255>
// CHECK-NOT: overflow
func.func @bad(%a: !pia.int<0, 255>, %b: !pia.int<0, 255>) -> !pia.int<0, 255> {
  %r = pia.add %a, %b : !pia.int<0, 255>, !pia.int<0, 255> -> !pia.int<0, 255>
  return %r : !pia.int<0, 255>
}

// Full-width bounds: i64 and u64.
// CHECK-LABEL: func.func @wide
// CHECK-SAME: (%{{.*}}: !isize, %{{.*}}: !usize)
func.func @wide(%a: !pia.int<-9223372036854775808, 9223372036854775807>,
                %b: !pia.int<0, 18446744073709551615>) {
  return
}

// CHECK-LABEL: func.func @constants_and_compare
// CHECK: pia.constant 200 : !pia.int<0, 255>
// CHECK: pia.constant -5 : !pia.int<-128, 127>
// CHECK: pia.convert %{{.*}} : <0, 255> -> <0, 65535>
// CHECK: pia.cmp lt
func.func @constants_and_compare() -> i1 {
  %c = pia.constant 200 : !pia.int<0, 255>
  %n = pia.constant -5 : !pia.int<-128, 127>
  %w = pia.convert %c : !pia.int<0, 255> -> !pia.int<0, 65535>
  %lt = pia.cmp lt %c, %c : !pia.int<0, 255>, !pia.int<0, 255>
  return %lt : i1
}

// Arrays, slices and parameter modifiers:
//   let scale (src : borrowed in [f32; n]) (dst : borrowed out mutable [f32; n]) ...
// CHECK-LABEL: func.func @scale
// CHECK-SAME: !pia.array<4 x f32> {pia.modifiers = "borrowed in"}
// CHECK-SAME: !pia.slice<f32> {pia.modifiers = "borrowed out mutable"}
// CHECK: pia.load %{{.*}}[%{{.*}}] : !pia.array<4 x f32>
// CHECK: pia.store %{{.*}}, %{{.*}}[%{{.*}}] : !pia.slice<f32>
// CHECK: pia.len %{{.*}} : !pia.slice<f32>
func.func @scale(%src: !pia.array<4 x f32> {pia.modifiers = "borrowed in"},
                 %dst: !pia.slice<f32> {pia.modifiers = "borrowed out mutable"},
                 %i: index) -> index {
  %v = pia.load %src[%i] : !pia.array<4 x f32>
  pia.store %v, %dst[%i] : !pia.slice<f32>
  %n = pia.len %dst : !pia.slice<f32>
  return %n : index
}

// dyn values keep their tag set.
// CHECK-LABEL: func.func @dyn
// CHECK: pia.dyn.wrap %{{.*}} : !pia.int<0, 255> -> <[!pia.int<0, 255>, f32]>
// CHECK: pia.dyn.is %{{.*}}, f32 : <[!pia.int<0, 255>, f32]>
// CHECK: pia.dyn.unwrap %{{.*}} : <[!pia.int<0, 255>, f32]> -> !pia.int<0, 255>
func.func @dyn(%x: !pia.int<0, 255>) -> i1 {
  %d = pia.dyn.wrap %x : !pia.int<0, 255> -> !pia.dyn<[!pia.int<0, 255>, f32]>
  %is = pia.dyn.is %d, f32 : !pia.dyn<[!pia.int<0, 255>, f32]>
  %u = pia.dyn.unwrap %d : !pia.dyn<[!pia.int<0, 255>, f32]> -> !pia.int<0, 255>
  return %is : i1
}

// Division, remainder and index conversion (M4).
// CHECK-LABEL: func.func @div_rem_index
// CHECK: pia.div %{{.*}}, %{{.*}} : <0, 255>, <0, 255> -> <0, 255>
// CHECK: pia.rem %{{.*}}, %{{.*}} overflow(trap) : <0, 255>, <0, 255> -> <0, 255>
// CHECK: %[[I:.*]] = pia.to_index %{{.*}} : <0, 255>
// CHECK: pia.from_index %[[I]] : !usize
func.func @div_rem_index(%a: !pia.int<0, 255>, %b: !pia.int<0, 255>) -> !pia.int<0, 18446744073709551615> {
  %q = pia.div %a, %b : !pia.int<0, 255>, !pia.int<0, 255> -> !pia.int<0, 255>
  %r = pia.rem %q, %b overflow(trap) : !pia.int<0, 255>, !pia.int<0, 255> -> !pia.int<0, 255>
  %i = pia.to_index %r : !pia.int<0, 255>
  %u = pia.from_index %i : !pia.int<0, 18446744073709551615>
  return %u : !pia.int<0, 18446744073709551615>
}

// Records (M7): a record prints as its name.
// CHECK-LABEL: func.func @records
// CHECK: %[[P:.*]] = pia.record(%{{.*}}, %{{.*}} : !pia.int<0, 255>, !pia.int<0, 255>) : !pixel
// CHECK: pia.field %[[P]], "g" : !pixel -> !pia.int<0, 255>
func.func @records(%a: !pia.int<0, 255>) -> !pia.int<0, 255> {
  %p = pia.record(%a, %a : !pia.int<0, 255>, !pia.int<0, 255>) : !pia.record<"pixel", r : !pia.int<0, 255>, g : !pia.int<0, 255>>
  %g = pia.field %p, "g" : !pia.record<"pixel", r : !pia.int<0, 255>, g : !pia.int<0, 255>> -> !pia.int<0, 255>
  return %g : !pia.int<0, 255>
}

// The spec-only int and real (ADR 0036): exact constants, arithmetic,
// comparisons and conversions from range-typed integers.
// CHECK-LABEL: func.func @exact
// CHECK: %[[H:.*]] = pia.exact.constant "1/2" : !pia.real
// CHECK: %[[N:.*]] = pia.exact.convert %{{.*}} : !pia.int<0, 255> -> !pia.integer
// CHECK: %[[X:.*]] = pia.exact.convert %[[N]] : !pia.integer -> !pia.real
// CHECK: pia.exact.mul %[[X]], %[[H]] : !pia.real
// CHECK: pia.exact.div %{{.*}}, %[[H]] : !pia.real
// CHECK: pia.exact.cmp le %{{.*}}, %{{.*}} : !pia.real
func.func @exact(%a: !pia.int<0, 255>) -> i1 attributes {pia.spec} {
  %h = pia.exact.constant "1/2" : !pia.real
  %n = pia.exact.convert %a : !pia.int<0, 255> -> !pia.integer
  %x = pia.exact.convert %n : !pia.integer -> !pia.real
  %p = pia.exact.mul %x, %h : !pia.real
  %q = pia.exact.div %p, %h : !pia.real
  %c = pia.exact.cmp le %p, %q : !pia.real
  return %c : i1
}
