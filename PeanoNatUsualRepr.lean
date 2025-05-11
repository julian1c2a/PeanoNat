import PeanoNat -- Importa las definiciones de PeanoNat.lean

namespace PeanoNat

-- Función auxiliar para convertir PeanoNat a Nat (solo para interactuar con Char y operaciones de Nat)
-- Esta función es "unsafe" en el sentido de que no está formalizada dentro de PeanoNat.txt
-- y asume terminación para PeanoNat bien formados.
private partial def peanoToNatUnsafe : PeanoNat → Nat
  | PeanoNat.zero => 0
  | PeanoNat.succ k => Nat.succ (peanoToNatUnsafe k)

-- === Representación Unaria ===

/--
Convierte un PeanoNat a una representación de String unaria usando el carácter '1'.
El cero se representa como "0".
Ej: 0 -> "0", 1 -> "1", 2 -> "11", 3 -> "111"
-/
def toUnaryString (p : PeanoNat) : String :=
  match p with
  | zero => "0" -- O podrías elegir "" para el cero en unario si prefieres
  | succ k =>
    let rec go : PeanoNat → List Char
      | zero => []
      | succ n' => '1' :: go n'
    -- Los '1's se generan en orden inverso (succ (succ zero) -> ['1', '1']),
    -- pero como todos los caracteres son iguales, el reverse no cambia el resultado visual
    -- si se piensa en la cantidad. Para ser precisos, si 0 es "0" y 1 es "1",
    -- entonces `succ zero` debería ser "1". `succ (succ zero)` debería ser "11".
    -- La lógica actual: toUnaryString (succ zero) -> go zero (para k) -> ['1'] -> "1"
    -- toUnaryString (succ (succ zero)) -> go (succ zero) -> '1' :: (go zero) -> ['1', '1'] -> "11"
    -- Esto parece correcto.
    (go p).asString -- `p` ya es `succ k`, por lo que `go p` producirá al menos un '1'.


/--
Versión alternativa para representación unaria donde el cero es una cadena vacía
y los números positivos son secuencias de '1'.
Ej: 0 -> "", 1 -> "1", 2 -> "11"
-/
def toUnaryString' (p : PeanoNat) : String :=
  let rec go : PeanoNat → List Char
    | zero => []
    | succ n' => '1' :: go n'
  (go p).asString


-- === Representación en Bases (2, 10, 16) usando Nat internamente ===

/--
Convierte un dígito (como Nat, 0-15) a su carácter correspondiente.
Para bases > 10, usa A-F.
Requiere que `digit < base` y `base > 0`.
-/
private def digitNatToChar (digit : Nat) (base : Nat) : Char :=
  if base ≤ 10 || digit < 10 then
    Char.ofNat (Char.toNat '0' + digit)
  else if digit < base && base > 10 && base <= 16 then -- Para A-F
    Char.ofNat (Char.toNat 'A' + (digit - 10))
  else
    '?' -- Carácter de error si el dígito/base no es válido para esta función simple

/--
Función auxiliar genérica para convertir un Nat a un String en una base dada.
La base debe estar entre 2 y 16.
-/
private def natToBaseString (n : Nat) (base : Nat) : String :=
  if base < 2 || base > 16 then
    "Error: Base debe estar entre 2 y 16"
  else if n == 0 then
    "0"
  else
    let rec go (num : Nat) (acc : List Char) : List Char :=
      if num == 0 then
        acc
      else
        let digit := num % base
        let char := digitNatToChar digit base
        go (num / base) (char :: acc) -- Prepend char, se invierte al final implícitamente
    (go n []).asString

/--
Convierte un PeanoNat a una representación de String en base binaria (base 2).
-/
def toBinaryString (p : PeanoNat) : String :=
  let n_nat := peanoToNatUnsafe p
  natToBaseString n_nat 2

/--
Convierte un PeanoNat a una representación de String en base decimal (base 10).
-/
def toDecimalString (p : PeanoNat) : String :=
  let n_nat := peanoToNatUnsafe p
  natToBaseString n_nat 10

/--
Convierte un PeanoNat a una representación de String en base hexadecimal (base 16).
-/
def toHexString (p : PeanoNat) : String :=
  let n_nat := peanoToNatUnsafe p
  natToBaseString n_nat 16

-- === Ejemplos de Uso (para probar en un entorno Lean) ===
-- Suponiendo que tienes `PeanoNat.zero`, `PeanoNat.one`, `PeanoNat.two`, ..., `PeanoNat.sixteen` definidos.

-- #eval PeanoNat.toUnaryString PeanoNat.zero  -- "0"
-- #eval PeanoNat.toUnaryString PeanoNat.three -- "111"
-- #eval PeanoNat.toUnaryString' PeanoNat.zero -- ""
-- #eval PeanoNat.toUnaryString' PeanoNat.three -- "111"

-- #eval PeanoNat.toBinaryString PeanoNat.zero    -- "0"
-- #eval PeanoNat.toBinaryString PeanoNat.one     -- "1"
-- #eval PeanoNat.toBinaryString PeanoNat.two     -- "10"
-- #eval PeanoNat.toBinaryString PeanoNat.six     -- "110"
-- #eval PeanoNat.toBinaryString PeanoNat.ten     -- "1010"

-- #eval PeanoNat.toDecimalString PeanoNat.zero    -- "0"
-- #eval PeanoNat.toDecimalString PeanoNat.seven   -- "7"
-- #eval PeanoNat.toDecimalString PeanoNat.thirteen -- "13"

-- #eval PeanoNat.toHexString PeanoNat.zero     -- "0"
-- #eval PeanoNat.toHexString PeanoNat.nine     -- "9"
-- #eval PeanoNat.toHexString PeanoNat.ten      -- "A"
-- #eval PeanoNat.toHexString PeanoNat.fifteen  -- "F"
-- #eval PeanoNat.toHexString PeanoNat.sixteen  -- "10"

end PeanoNat
```

**Explicación de las funciones:**

1.  **`peanoToNatUnsafe`**: La misma función que teníamos antes para convertir `PeanoNat` a `Nat`. Es crucial para las funciones de base 2, 10 y 16.
2.  **`toUnaryString` y `toUnaryString'`**:
    * `toUnaryString`: Convierte un `PeanoNat` a una cadena de '1's. El `PeanoNat.zero` se representa como "0". Un `PeanoNat` que representa `k > 0` se convierte en una cadena de `k` caracteres '1'.
    * `toUnaryString'`: Una alternativa donde `PeanoNat.zero` se representa como una cadena vacía `""`.
3.  **`digitNatToChar`**: Una función privada que toma un dígito (como `Nat`, entre 0 y 15) y la base, y devuelve el `Char` correspondiente ('0'-'9', 'A'-'F').
4.  **`natToBaseString`**:
    * Una función privada genérica que toma un `Nat` y una base (entre 2 y 16).
    * Implementa el algoritmo estándar de conversión de base dividiendo repetidamente por la base y tomando el residuo.
    * Los dígitos se recopilan y luego se convierten en una cadena.
5.  **`toBinaryString`, `toDecimalString`, `toHexString`**:
    * Estas son las funciones públicas que quieres.
    * Cada una primero convierte el `PeanoNat` de entrada a `Nat` usando `peanoToNatUnsafe`.
    * Luego, llaman a `natToBaseString` con el `Nat` resultante y la base apropiada (2, 10 o 16).

**Para usar este código:**
* Asegúrate de que el archivo `PeanoNat.lean` (que contiene la definición de `PeanoNat` y sus constantes como `PeanoNat.one`, `PeanoNat.ten`, etc.) está en el mismo proyecto y es importado correctamente (`import PeanoNat`).
* Puedes descomentar las líneas `#eval` al final para probar las funciones en un entorno Lean. Necesitarás tener las definiciones de `PeanoNat.zero`, `PeanoNat.one`, etc., disponibles.

Este enfoque te da las representaciones directas que buscabas. La principal "trampa" o simplificación es el uso de `peanoToNatUnsafe` para evitar reimplementar la división y el módulo para `PeanoNat`, lo cual sería un esfuerzo de formalización mucho mayor. Para fines de representación, esto suele ser una solución muy aceptab
