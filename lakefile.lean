import Lake
open Lake DSL

package «chanlun» where

require "leanprover-community" / "mathlib" @ git "v4.14.0"

lean_lib «Chanlun» where
  srcDir := "lean"
  globs := #[.submodules `Chanlun]
