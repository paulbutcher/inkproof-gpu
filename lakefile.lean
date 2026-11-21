/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package «inkproof-gpu» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

require «inkproof-float» from git "https://github.com/paulbutcher/inkproof-float" @ "v0.5.0"
require «inkproof-scene» from git "https://github.com/paulbutcher/inkproof-scene" @ "v0.22.0"

@[default_target]
lean_lib InkproofGpu where
  roots := #[`Inkproof.Gpu, `Inkproof.Gpu.Proofs]

lean_exe gen where
  root := `Main
  srcDir := "gen"

@[test_driver]
script tests do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["test"], cwd := __dir__ / "test" }
  child.wait
