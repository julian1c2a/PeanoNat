import Lake
open Lake DSL

package «peanonat» where
  -- Metadatos del paquete
  precompileModules := true

@[default_target]
lean_lib «PeanoNat» where
  -- Configuración de la biblioteca
  -- Aquí puedes agregar opciones adicionales para la biblioteca

@[default_target]
lean_exe «peanonat» where
  root := `Main
  -- Habilita el intérprete de Lean por defecto
  supportInterpreter := true
