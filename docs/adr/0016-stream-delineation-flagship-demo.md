# 16. Stream delineation on Apple Silicon is the flagship demo

Date: 2026-11-20

Status: Accepted

## Context

The language needs one end-to-end program that exercises every feature and is provably correct by construction.

## Decision

The flagship demo is GIS stream delineation: decode a PNG/GIF heightmap, fill depressions, compute D8 flow direction, accumulate flow, simulate sediment transport with a proved conservation law, and render a PNG/GIF coloured by sediment load. It runs concurrently on Apple Silicon. Image I/O libraries (`Image.Png`, `Image.Gif`) are part of the work. Smaller pipelines (saturating add, dot product, clamp and scale, serialise round trip, tiled matmul) come first as the test suite.

## Consequences

- Features are prioritised by what this demo needs next.
