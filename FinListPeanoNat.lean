import Mathlib.Data.Fin.Basic -- Para Fin n y sus propiedades
import Mathlib.Data.List.Basic -- Para Listas

/-
El objetivo es definir un tipo, llamémoslo `FinListPeano n`, que sea isomórfico
a `Nat`. Este tipo dependerá de un parámetro `n : Nat`.
La "forma de escribir los números" o su representación fundamental será
una "cadena" (lista) de elementos de tipo `Fin n`.

Asumiremos que la lista de dígitos `Fin n` representa el número con el
dígito menos significativo primero (LSB first).
Por ejemplo, si n=10, el número 123 se representaría como la lista `[⟨3,_⟩, ⟨2,_⟩, ⟨1,_⟩]`.
El número 0 se representará, por convención, con una lista vacía `[]`.
-/

-- Primero, definimos el tipo que encapsula la lista de dígitos.
-- Usamos `@[ext]` para que Lean genere automáticamente un teorema de extensionalidad,
-- lo que significa que dos `FinListPeano` son iguales si sus campos `digits` son iguales.
@[ext]
structure FinListPeano (n : Nat) where
  -- Los dígitos, con el menos significativo primero.
  digits : List (Fin n)
  deriving Repr, BEq -- Para poder imprimirlos y compararlos (estructuralmente)

namespace FinListPeano

-- Definición de Cero para FinListPeano n
-- El cero se representa como una lista de dígitos vacía.
def zero (n : Nat) : FinListPeano n :=
  ⟨[]⟩

-- Definición del Sucesor para FinListPeano n
--
-- Para esta operación, es crucial considerar el valor de `n`:
-- - Si `n = 0`, `Fin 0` es un tipo vacío. `digits` solo puede ser `[]`.
--   `FinListPeano 0` solo tiene un valor (`zero 0`), y `succ` no puede "avanzar".
-- - Si `n > 0`, `Fin n` es habitable.
--
-- La función `list_succ_raw` es el núcleo de la operación `succ`.
-- Toma una lista de dígitos y devuelve la lista sucesora.
-- Necesita una prueba de que `n > 0` (denotada `h_n_pos`).

private def list_succ_raw (n : Nat) (ds : List (Fin n)) (h_n_pos : n > 0) : List (Fin n) :=
  match ds with
  | [] =>
    -- Caso base: la lista de dígitos está vacía (representa el número 0).
    -- El sucesor de 0 es 1.
    -- Si n = 1 (base unaria): El único dígito es 0. El sucesor de [] es [⟨0, h_one⟩].
    -- Si n > 1 (base > 1): El sucesor de [] es [⟨1, h_one_lt_n⟩].
    if h_n_eq_1 : n = 1 then
      -- n = 1. El único dígito posible es `Fin.mk 0 _`.
      [⟨0, h_n_eq_1 ▸ Nat.zero_lt_one⟩]
    else
      -- n > 1. El dígito 1 es `Fin.mk 1 _`.
      -- Probamos que `1 < n` si `n > 0` y `n ≠ 1`.
      have h_one_lt_n : 1 < n := Nat.lt_of_le_of_ne (Nat.pos_iff_one_le.mp h_n_pos) (Ne.symm h_n_eq_1)
      [⟨1, h_one_lt_n⟩]
  | d :: rest =>
    -- Caso recursivo: la lista de dígitos no está vacía. `d` es el LSB.
    -- Si n = 1 (base unaria):
    --   El dígito `d` debe ser `⟨0, _⟩`.
    --   El sucesor en base 1 (LSB first) significa añadir un 0 al principio de la lista.
    --   Ej: succ de [0,0] (dos) es [0,0,0] (tres).
    --   Aquí, `d` es el LSB. `succ ([0,0])` -> `d=0, rest=[0]`.
    --   Debería ser `0 :: (0 :: rest_original_sin_d)`.
    --   Más simple: `succ [d₀, d₁, ...]` es `[0, d₀, d₁, ...]`.
    if h_n_eq_1 : n = 1 then
      -- `d` es `⟨0, _⟩`. `rest` son los otros `⟨0, _⟩`.
      -- El sucesor es `⟨0, _⟩ :: (d :: rest)`.
      ⟨0, h_n_eq_1 ▸ Nat.zero_lt_one⟩ :: (d :: rest).map (fun x => h_n_eq_1 ▸ x) -- Re-tipar para Lean
    else
      -- Base n > 1:
      -- `h_one_lt_n` también se cumple aquí si `n > 1`.
      -- Intentamos incrementar el dígito menos significativo `d`.
      if h_lt : d.val + 1 < n then
        -- No hay acarreo desde este dígito. Simplemente incrementamos `d`.
        -- `h_lt` prueba que `d.val + 1 < n`.
        ⟨d.val + 1, h_lt⟩ :: rest
      else
        -- Hay acarreo: d.val + 1 = n. El nuevo LSB es 0.
        -- Propagamos el acarreo al resto de la lista (`rest`).
        ⟨0, h_n_pos⟩ :: list_succ_raw n rest h_n_pos

-- La función `succ` pública para `FinListPeano`.
-- Requiere la prueba `h_n_pos : n > 0`.
def succ (flp : FinListPeano n) (h_n_pos : n > 0) : FinListPeano n :=
  ⟨list_succ_raw n flp.digits h_n_pos⟩

-- Ejemplos (requerirían pruebas explícitas de h_n_pos en uso real):
-- def one (n : Nat) (h : n > 0) : FinListPeano n := succ (zero n) h
-- def two (n : Nat) (h : n > 0) : FinListPeano n := succ (one n h) h

-- Para demostrar el isomorfismo con Nat, los siguientes pasos serían:
-- 1. Probar propiedades de `zero` y `succ` (ej. `succ x ≠ zero`).
-- 2. Definir funciones de conversión:
--    `toNat : FinListPeano n → Nat`
--    `fromNat : Nat → FinListPeano n` (necesitará `h_n_pos`)
-- 3. Probar que estas funciones son inversas y que preservan las operaciones
--    (homomorfismos):
--    `toNat (zero n) = Nat.zero`
--    `toNat (succ x h) = Nat.succ (toNat x)`
--    Y similarmente para `fromNat`.

end FinListPeano

-- Ejemplo de cómo se verían los números (conceptual):
-- Base n=2 (binario), LSB first:
-- FinListPeano.zero 2  => ⟨[]⟩                  (0)
-- FinListPeano.succ (⟨[]⟩) (by decide) => ⟨[⟨1, by decide⟩]⟩ (1)
-- FinListPeano.succ (⟨[⟨1, by decide⟩]⟩) (by decide) => ⟨[⟨0, by decide⟩, ⟨1, by decide⟩]⟩ (2)
-- FinListPeano.succ (⟨[⟨0, _⟩, ⟨1, _⟩]⟩) (by decide) => ⟨[⟨1, _⟩, ⟨1, _⟩]⟩ (3)

-- Base n=1 (unario), LSB first:
-- FinListPeano.zero 1 => ⟨[]⟩                   (0)
-- FinListPeano.succ (⟨[]⟩) (by decide) => ⟨[⟨0, by decide⟩]⟩  (1)
-- FinListPeano.succ (⟨[⟨0,_⟩]⟩) (by decide) => ⟨[⟨0,_⟩,⟨0,_⟩]⟩ (2)
