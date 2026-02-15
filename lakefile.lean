import Lake
open Lake DSL

package «peanolib» where
  -- Add package configuration options here
  moreServerArgs := #["-DautoImplicit=false", "-DwarningAsError=false"]
  moreLeanArgs := #["-DautoImplicit=false", "-DwarningAsError=false"]

@[default_target]
lean_lib «Peano» where
  -- Configuramos múltiples roots: Peano y todos los módulos de PeanoNatLib
  srcDir := "."
  roots := #[`Peano]
  globs := #[Glob.submodules `PeanoNatLib]

-- Opcional: si quieres importar Mathlib para tácticas u otras utilidades
-- require mathlib from git
--  "https://github.com/leanprover-community/mathlib4.git"

-- Opcional: si tuvieras un ejecutable
-- lean_exe «peanonatlib» where
--   root := `Main -- Si tuvieras un Main.lean
