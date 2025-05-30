import Lake
open Lake DSL

package «peanonatlib» where
  -- Add package configuration options here
  moreServerArgs := #["-DautoImplicit=false"] -- Ejemplo de opción, puedes quitarla o ajustarla

@[default_target]
lean_lib «PeanoNatLib» where
  -- Add library configuration options here
  -- Por defecto, buscará archivos .lean en un directorio con el mismo nombre que la biblioteca
  -- (es decir, "PeanoNatLib") o en la raíz si no existe tal directorio.
  -- Si tus archivos están en la raíz (PeanoNatAxioms.lean, PeanoNatStrictOrder.lean),
  -- Lake debería encontrarlos.
  -- Si los tienes en un subdirectorio, por ejemplo, "src", lo indicarías así:
  -- rootDir := `PeanoNatLib -- Esta línea se elimina o se corrige si se usa srcDir

-- Opcional: si quieres importar Mathlib para tácticas u otras utilidades
-- require mathlib from git
--  "https://github.com/leanprover-community/mathlib4.git"

-- Opcional: si tuvieras un ejecutable
-- lean_exe «peanonatlib» where
--   root := `Main -- Si tuvieras un Main.lean
