# Modifications Log

Tracks modifications to the vendored DeGiorgi code (https://github.com/scottnarmstrong/DeGiorgi,
commit `4c1b307`) per Apache License 2.0 §4(b).

## Format

```
### <YYYY-MM-DD> — <short tag>

**Files**: <list of modified files, relative to this directory>
**Change**: <short description>
```

## Entries

### 2026-04-23 — initial vendoring

**Files**: (none modified)
**Change**: Repository vendored verbatim at commit 4c1b307.

### 2026-04-28 — import-path rewire

**Files**: all `.lean` files under this directory
**Change**: rewrote internal `import DeGiorgi.…` statements as `import DifferentialGeometry.External.DeGiorgi.…` to fit the project's module path layout.

<!-- Add entries below as modifications occur. -->
