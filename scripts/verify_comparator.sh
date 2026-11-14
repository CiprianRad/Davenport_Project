#!/usr/bin/env bash
# Copyright (c) 2026 Claudiu G. Pop, George C. Rad, George C. Țurcaș. All rights reserved.
# SPDX-License-Identifier: Apache-2.0
#
# Check `Solution` against `Challenge` with the `lake comparator` of the project's toolchain: the
# statements must agree, only `propext`, `Quot.sound` and `Classical.choice` may be used, and the
# exported proofs are replayed in Lean's kernel and in the NanoDa kernel bundled with the
# toolchain. (Palomar registers the bundled kernels itself and ignores `enable_nanoda`; it also
# tries con-ron, which takes about three times as long as Lean's kernel here and is left out.)
#
# Usage: scripts/verify_comparator.sh   (needs bubblewrap; run `lake exe cache get` first)
set -euo pipefail
cd "$(dirname "$0")/.."
prefix=$(lean --print-prefix)
config=$(mktemp "${TMPDIR:-/tmp}/comparator.XXXXXX.json")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json, sys
source, target, prefix = sys.argv[1:]
config = json.load(open(source, encoding="utf-8"))
config.pop("enable_nanoda", None)
config["external_kernels"] = {"nanoda": [f"{prefix}/bin/nanoda_bin"]}
json.dump(config, open(target, "w", encoding="utf-8"), indent=2)
PY
lake comparator --config "$config"
