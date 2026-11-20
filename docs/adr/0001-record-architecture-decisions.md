# 1. Record architecture decisions

Date: 2026-11-20

Status: Accepted

## Context

Pia is a solo project with many interlocking language and compiler decisions. Later work (and later Claude sessions) needs to know what was decided and why, without re-deriving it from chat history.

## Decision

Record each significant decision as a short ADR in `docs/adr/`, numbered in order, with Status, Context, Decision and Consequences. `docs/design.md` is the readable overview; ADRs are the source of truth when they disagree. A changed decision gets a new ADR that supersedes the old one, rather than an edit that erases history.

## Consequences

- Every design change touches an ADR first.
- ADRs stay short; detail and examples live in `docs/design.md`.
