//===- Par.td - The pia_par dialect -------------------------------*- tablegen -*-===//
//
// Tiled grids with halos, `spread` loops, collectives and placement (ADR 0014,
// ADR 0015). Lives from IRGen to runtime lowering. The docs' `pia.par` is
// spelled `pia_par` in IR, because dialect namespaces cannot contain '.'.
//
//===----------------------------------------------------------------------===//

#ifndef PIA_DIALECT_PAR_TD
#define PIA_DIALECT_PAR_TD

include "mlir/IR/AttrTypeBase.td"
include "mlir/IR/DialectBase.td"
include "mlir/IR/EnumAttr.td"
include "mlir/IR/OpBase.td"
include "mlir/Interfaces/SideEffectInterfaces.td"

def Par_Dialect : Dialect {
  let name = "pia_par";
  let summary = "Pia's concurrent runtime: tiles, spread loops and collectives";
  let cppNamespace = "::pia::par";
  let useDefaultTypePrinterParser = 1;
  let extraClassDeclaration = [{
    void registerTypes();
  }];
}

def Par_TiledType : TypeDef<Par_Dialect, "Tiled"> {
  let mnemonic = "tiled";
  let summary = "a 2-D grid split into tiles with a halo of neighbour cells";
  let description = [{
    `!pia_par.tiled<!cell, 256 x 256, halo = 1>` is the IR form of
    `tiled<cell, 256, 256, halo = 1>`.
  }];
  let parameters = (ins "::mlir::Type":$elementType, "uint64_t":$tileRows,
                        "uint64_t":$tileCols, "uint64_t":$halo);
  let assemblyFormat = "`<` $elementType `,` $tileRows `x` $tileCols `,` `halo` `=` $halo `>`";
}

def Par_TileType : TypeDef<Par_Dialect, "Tile"> {
  let mnemonic = "tile";
  let summary = "one tile of a tiled grid, owned by one worker inside a spread";
  let parameters = (ins "::mlir::Type":$elementType, "uint64_t":$tileRows,
                        "uint64_t":$tileCols, "uint64_t":$halo);
  let assemblyFormat = "`<` $elementType `,` $tileRows `x` $tileCols `,` `halo` `=` $halo `>`";
}

def Par_Tiled : Type<CPred<"::llvm::isa<::pia::par::TiledType>($_self)">,
                     "tiled grid", "::pia::par::TiledType">;

def Par_Placement : I32EnumAttr<"Placement", "where a spread's tiles run", [
      I32EnumAttrCase<"auto_", 0, "auto">,  // the cost model picks per tile
      I32EnumAttrCase<"cpu", 1>,
      I32EnumAttrCase<"gpu", 2>,
      I32EnumAttrCase<"ane", 3>,   // Apple Neural Engine, via Core ML (later)
    ]> {
  let cppNamespace = "::pia::par";
}

def Par_ReduceKind : I32EnumAttr<"ReduceKind", "the combining function of a reduction", [
      I32EnumAttrCase<"add", 0>, I32EnumAttrCase<"mul", 1>,
      I32EnumAttrCase<"min", 2>, I32EnumAttrCase<"max", 3>,
    ]> {
  let cppNamespace = "::pia::par";
}

class Par_Op<string mnemonic, list<Trait> traits = []>
    : Op<Par_Dialect, mnemonic, traits>;

def Par_SpreadOp : Par_Op<"spread", [SingleBlockImplicitTerminator<"YieldOp">,
                                     RecursiveMemoryEffects]> {
  let summary = "run the body once per tile, in parallel";
  let description = [{
    The body's single block argument is the tile, of `!pia_par.tile<...>`
    matching the grid. Tiles are moved to workers, so bodies cannot race
    (ADR 0014). An optional `prefer` placement refines `auto`.
  }];
  let arguments = (ins Par_Tiled:$grid,
                       DefaultValuedAttr<Par_Placement, "::pia::par::Placement::auto_">:$placement,
                       OptionalAttr<Par_Placement>:$prefer);
  let regions = (region SizedRegion<1>:$body);
  let assemblyFormat = [{
    $grid `place` `(` $placement (`,` `prefer` `=` $prefer^)? `)` $body attr-dict `:` type($grid)
  }];
  let hasVerifier = 1;
}

def Par_YieldOp : Par_Op<"yield", [Pure, Terminator, ParentOneOf<["SpreadOp"]>]> {
  let summary = "end a spread body";
  let assemblyFormat = "attr-dict";
}

def Par_HaloExchangeOp : Par_Op<"halo_exchange"> {
  let summary = "copy each tile's edge cells into its neighbours' halos";
  let description = [{
    A collective: every worker takes part. Must precede any stencil read of
    halo cells; the protocol checker enforces the ordering (M12).
  }];
  let arguments = (ins Par_Tiled:$grid);
  let assemblyFormat = "$grid attr-dict `:` type($grid)";
}

def Par_AllReduceOp : Par_Op<"all_reduce", [SameOperandsAndResultType]> {
  let summary = "combine one value from every worker; all receive the result";
  let arguments = (ins Par_ReduceKind:$kind, AnyType:$value);
  let results = (outs AnyType:$result);
  let assemblyFormat = "$kind $value attr-dict `:` type($value)";
}

def Par_ScatterOp : Par_Op<"scatter"> {
  let summary = "split a buffer into a tiled grid";
  let arguments = (ins AnyType:$source);
  let results = (outs Par_Tiled:$grid);
  let assemblyFormat = "$source attr-dict `:` type($source) `->` type($grid)";
}

def Par_GatherOp : Par_Op<"gather"> {
  let summary = "assemble a tiled grid back into one buffer";
  let arguments = (ins Par_Tiled:$grid);
  let results = (outs AnyType:$result);
  let assemblyFormat = "$grid attr-dict `:` type($grid) `->` type($result)";
}

#endif // PIA_DIALECT_PAR_TD
