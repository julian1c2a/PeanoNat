import Lake
open Lake DSL

package «peanonat» where
  -- Metadatos del paquete
  precompileModules := true

@[default_target]
lean_lib «PeanoNat» where
  -- Configuración de la biblioteca
  -- Aquí puedes agregar opciones adicionales para la biblioteca
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «peanonat» where
  root := `Main
  -- Habilita el intérprete de Lean por defecto
  supportInterpreter := true
