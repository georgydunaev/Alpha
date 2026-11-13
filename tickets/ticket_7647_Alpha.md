# [ALPHA] Ticket 7647 — Alpha: Coq 8.20 Modernization and Lia Migration for 00.v Proof Obligations

**Repository:** `Alpha`  
**Status:** `RESOLVED`  
**Created:** `2026-11-13T21:21:18Z`  

## Task Description
In `00.v`, Coq proof obligations rely on the deprecated and removed Omega tactic (`Require Import Omega; omega.`). Modern Coq/Rocq versions (8.14 through 8.20+) require `Coq.micromega.Lia` and the `lia` tactic. Update or provide modernized proof script with `lia` while preserving backward compatibility and original comments.

## Resolution
Provided `alpha_core.v` implementing all 5 obligations with `lia`, fully proven without admits. Preserved `00.v` intact.
