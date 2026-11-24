/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package «inkproof-gpu-test» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩
  ]

require «inkproof-gpu» from ".."
require «inkproof-tools» from git "https://github.com/paulbutcher/inkproof-tools" @ "v0.2.1"

@[default_target]
lean_exe tests where
  root := `Main

-- Needs node, so it is not part of `tests`, which must stay buildable by Lasm.
@[default_target]
lean_exe jstests where
  root := `JsTests

@[test_driver]
script test do
  let driver ← IO.Process.spawn
    { cmd := "lake", args := #["exe", "inkproof-tools/inkproof-test-driver"], cwd := __dir__
      -- A browser's stack, not the gigabyte Lasm gives Node, so that deep recursion fails here.
      env := #[("LASM_VM_STACK_MB", some "1")] }
  let a ← driver.wait
  let js ← IO.Process.spawn { cmd := "lake", args := #["exe", "jstests"], cwd := __dir__ }
  let b ← js.wait
  return if a == 0 && b == 0 then 0 else 1
