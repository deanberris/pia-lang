"""Link options for Pia's own tool binaries (piac, pia, pia-lsp, pia-opt)."""

# The tools link LLVM, MLIR and Z3 statically. On macOS every symbol they
# define is exported by default, and each weak definition (C++ templates and
# inline functions, about 365,000 of them) then becomes a bind that dyld
# resolves against the executable's own export trie at every launch: 1.5 s
# before `main` (issue #120). Exporting nothing but the Mach-O header lets
# the static linker resolve them all, and dead stripping drops the code
# nothing reaches. The tools never look themselves up with dlsym: the REPL's
# JIT gets its symbols from an explicit map (src/repl/Session.cpp).
TOOL_LINKOPTS = select({
    "@platforms//os:macos": [
        "-Wl,-dead_strip",
        "-Wl,-exported_symbol,__mh_execute_header",
    ],
    "//conditions:default": [
        "-Wl,--gc-sections",
    ],
})
