-- import Mathlib.Logic.Classical

-- PeanoNatAxioms.lean



inductive ℕ₀ : Type
  where
  | zero : ℕ₀
  | succ : ℕ₀ -> ℕ₀
  deriving Repr, BEq, DecidableEq


namespace Peano
    set_option trace.Meta.Tactic.simp true



  notation "σ" n:max => ℕ₀.succ n
  def cero : ℕ₀ := ℕ₀.zero
  notation "𝟘" => ℕ₀.zero

  def is_zero : ℕ₀ -> Prop :=
    fun n =>
      match n with
      | ℕ₀.zero   => True
      | ℕ₀.succ _ => False

  def is_succ : ℕ₀ -> Prop :=
    fun n =>
      match n with
      | ℕ₀.zero => False
      | ℕ₀.succ _ => True

  def return_branch : ℕ₀ -> Prop :=
    fun n =>
      match n with
      | ℕ₀.zero   => is_zero n
      | ℕ₀.succ _ => is_succ n

  /--!
      EL SIGUIENTE AXIOMA SE DA POR QUE IS_ZERO INDICA
      QUE ES UNA RAMA DEL CONSTRUCTOR DE PEANONAT
     !-/
  theorem AXIOM_zero_is_an_PeanoNat :
      is_zero 𝟘 := by
        unfold is_zero
        trivial


  /--!
      EL SIGUIENTE AXIOMA SE DA POR QUE IS_SUCC INDICA
      QUE ES UNA RAMA DEL CONSTRUCTOR DE PEANONAT
     !-/
  theorem AXIOM_succ_is_an_PeanoNat(n : ℕ₀) :
      is_succ (σ n) := by
        unfold is_succ
        trivial


  /--!
  EL AXIOMA DE PEANO DE EXISTENCIA DEL CERO
  COMO NÚMERO NATURAL ESTÁ ASEGURADO POR LA CONSTRUCCIÓN
  DEL TIPO PEANONAT (BRAZO UNO DEL TIPO INDUCTIVO,
  EXPLÍCITO EN LA DEFINICIÓN DEL TIPO)


  --- TEOREMAS ACERCA DE LA FUNCIÓN SUCESOR Y LA CONSTANTE ZERO
  ---

  !-/

  theorem cero_neq_succ
      (n : ℕ₀)
      (h_ex_n : n = σ n):
          𝟘 ≠ σ n
              := by
                  cases n with
                  | zero =>
                      contradiction
                  | succ n' =>
                      apply ℕ₀.noConfusion

  theorem AXIOM_cero_neq_succ :
          ∀ (k : ℕ₀), 𝟘 ≠ σ k
              := by
                  intro k
                  intro h_eq_contra
                  exact ℕ₀.noConfusion h_eq_contra

  /--!
      ESTOS DOS TEOREMAS  QUE SE MUESTRAN A CONTINUACIÓN DICEN EL
      AXIOMA DE PEANO
          σ ES UNA FUNCIÓN EN EL SENTIDO MATEMÁTICO MODERNO.

      QUE UNA FUNCIÓN (PORQUE TODO SON FUNCIONES EN LEAN4) TENGA
      RETORNOS CONCRETOS PARA CADA ENTRADA (TENGA IMAGEN) ES UN
      TEOREMA EN LEAN4, HABRÍA QUE HACER EXPLÍCITAMENTE ALGUNA
      FUNCIÓN DE TIPO PARCIAL, NO TOTAL, PARA QUE NO OCURRIERA
      ASÍ
     !-/
  theorem AXIOM_succ_is_funct_forall_n_in_PeanoNat:
      ∀ (n : ℕ₀), ∃ (k : ℕ₀), k = σ n
          := by
              intro n
              exists σ n

  /--!
      LA UNICIDAD EN LA IMAGEN DE LA FUNCIÓN SUCESIÓN ES UN TEOREMA
      PORQUE EN LEAN4 TODAS SON FUNCIONES DETERMINISTAS, Y POR LO
      TANTO SIEMPRE VAN A DAR EL MISMO RESULTADO CON ENTRADAS IGUALES
      (NO SE PUEDE HACER UNA FUNCIÓN QUE NO SEA DETERMINISTA)
     !-/
  theorem AXIOM_uniqueness_on_image(n m: ℕ₀) :
      n = m → σ n = σ m
          := by
              intro h_eq
              calc
                σ n = σ n   := by rfl
                _   = σ m   := by rw [h_eq]

  /--!
      ESTE TEOREMA QUE SE MUESTRAN A CONTINUACIÓN ES EL
      AXIOMA DE PEANO
          σ ES UNA FUNCIÓN INYECTIVA.

      POR LA FORMA DE LOS TIPOS INDUCTIVO NOS LEAN4 ASEGURA QUE LOS BRAZOS DEL MATCH SON VALORES DISTINTOS DEL TIPO, Y LAS FUNCIONES EN LOS BRAZOS SON INYECTIVAS PARA SEGUIR PRODUCIENDO VALORES DIFERENTES.
     !-/
  theorem AXIOM_succ_inj(n m : ℕ₀):
      σ n = σ m → n = m
          := by
              intro h_eq
              injection h_eq with h_n_eq_m

  def succ_inj(n m : ℕ₀) := AXIOM_succ_inj n m

  theorem succ_inj_neg :
      ∀ n m : ℕ₀, σ n ≠ σ m → n ≠ m :=
          fun n m h_neq_succ h_eq =>
              have h_succ_eq : σ n = σ m
                  := congrArg ℕ₀.succ h_eq
              absurd h_succ_eq h_neq_succ

  /--!
      AXIOMA DE PEANO:
          0 NO ES SUCESOR DE NINGÚN NÚMERO NATURAL.

      EN LEAN4 ESTO VIENE DADO POR EL CONSTRUCTOR QUE TIENE LA PROPIEDAD NOCONFUSION
     !-/
  theorem succ_neq_zero (n : ℕ₀) :
      σ n ≠ 𝟘
          := by
              intro h_eq
              apply ℕ₀.noConfusion h_eq

  theorem AXIOM_zero_notin_ima_succ :
      ∀ (n : ℕ₀), 𝟘 ≠ σ n
          := by
              intro n
              symm
              apply succ_neq_zero

  /--!
      EL ÚLTIMO AXIOMA DE LA FUNCIÓN SUCESOR
      ES LA PROPIEDAD DE INDUCCIÓN SOBRE CUALQUIER
      PROPIEDAD P.
      EN LEAN4 ESTO VIENE DADO POR EL TIPO INDUCTIVO
      QUE TIENE LA PROPIEDAD NOCONFUSION
     !-/
  theorem AXIOM_induction_on_PeanoNat
      (P : ℕ₀ -> Prop)
      (h_0 : P 𝟘)
      (h_succ : ∀ n, P n → P (σ n)) :
      ∀ n, P n
          := by
              intro n
              induction n with
              | zero =>
                  exact h_0
              | succ k ih =>
                  exact h_succ k ih

  def BIs_zero : ℕ₀ -> Bool :=
    fun n =>
      match n with
      | ℕ₀.zero   => true
      | ℕ₀.succ _ => false

  def BIs_succ : ℕ₀ -> Bool :=
    fun n =>
      match n with
      | ℕ₀.zero   => false
      | ℕ₀.succ _ => true

  def category_by_constructor (n : ℕ₀) : ℕ₀ -> Prop :=
    match n with
    | ℕ₀.zero   => is_zero
    | ℕ₀.succ _ => is_succ

  theorem neq_succ (k : ℕ₀) : k ≠ σ k := by
    induction k with
    | zero =>
      intro h_eq_zero_succ_zero
      exact Peano.succ_neq_zero 𝟘 h_eq_zero_succ_zero.symm
    | succ k' ih_k' =>
      intro h_eq_succ_k_succ_succ_k
      have h_k_eq_succ_k : k' = σ k' := AXIOM_succ_inj k' (σ k') h_eq_succ_k_succ_succ_k
      exact ih_k' h_k_eq_succ_k

  theorem is_zero_or_is_succ (n : ℕ₀) :
      is_zero n ∨ is_succ n
          := by
              cases n with
              | zero =>
                  unfold is_zero
                  dsimp
                  unfold is_succ
                  dsimp
                  rw [true_or]
                  trivial
              | succ a =>
                  unfold is_zero
                  dsimp
                  unfold is_succ
                  dsimp
                  rw [or_true]
                  trivial

  theorem is_zero_xor_is_succ (n : ℕ₀) :
      (is_zero n ∧ ¬is_succ n) ∨ (¬is_zero n ∧ is_succ n)
          := by
              cases n with
              | zero =>
                  unfold is_zero is_succ
                  dsimp
                  rw [not_false_eq_true]
                  rw [and_self]
                  rw [not_true_eq_false]
                  rw [and_self]
                  rw [or_false]
                  trivial
              | succ a =>
                  unfold is_zero is_succ
                  dsimp
                  rw [not_true_eq_false]
                  rw [and_self]
                  rw [not_false_eq_true]
                  rw [and_self]
                  rw [or_true]
                  trivial

  /-- Definiciones básicas para PeanoNat -/
  def one : ℕ₀ := σ 𝟘
  def two : ℕ₀ := σ one
  def three : ℕ₀ := σ two
  def four : ℕ₀ := σ three
  def five : ℕ₀ := σ four
  def six : ℕ₀ := σ five
  def seven : ℕ₀ := σ six
  def eight : ℕ₀ := σ seven
  def nine : ℕ₀ := σ eight
  def ten : ℕ₀ := σ nine
  def eleven : ℕ₀ := σ ten
  def twelve : ℕ₀ := σ eleven
  def thirteen : ℕ₀ := σ twelve
  def fourteen : ℕ₀ := σ thirteen
  def fifteen : ℕ₀ := σ fourteen
  def sixteen : ℕ₀ := σ fifteen
  def seventeen : ℕ₀ := σ sixteen
  def eighteen : ℕ₀ := σ seventeen
  def nineteen : ℕ₀ := σ eighteen
  def twenty : ℕ₀ := σ nineteen
  def twenty_one : ℕ₀ := σ twenty
  def twenty_two : ℕ₀ := σ twenty_one
  def twenty_three : ℕ₀ := σ twenty_two
  def twenty_four : ℕ₀ := σ twenty_three
  def twenty_five : ℕ₀ := σ twenty_four
  def twenty_six : ℕ₀ := σ twenty_five
  def twenty_seven : ℕ₀ := σ twenty_six
  def twenty_eight : ℕ₀ := σ twenty_seven
  def twenty_nine : ℕ₀ := σ twenty_eight
  def thirty : ℕ₀ := σ twenty_nine
  def thirty_one : ℕ₀ := σ thirty
  def thirty_two : ℕ₀ := σ thirty_one
  def thirty_three : ℕ₀ := σ thirty_two
  def thirty_four : ℕ₀ := σ thirty_three
  def thirty_five : ℕ₀ := σ thirty_four
  def thirty_six : ℕ₀ := σ thirty_five
  def thirty_seven : ℕ₀ := σ thirty_six
  def thirty_eight : ℕ₀ := σ thirty_seven
  def thirty_nine : ℕ₀ := σ thirty_eight
  def forty : ℕ₀ := σ thirty_nine
  def forty_one : ℕ₀ := σ forty
  def forty_two : ℕ₀ := σ forty_one
  def forty_three : ℕ₀ := σ forty_two
  def forty_four : ℕ₀ := σ forty_three
  def forty_five : ℕ₀ := σ forty_four
  def forty_six : ℕ₀ := σ forty_five
  def forty_seven : ℕ₀ := σ forty_six
  def forty_eight : ℕ₀ := σ forty_seven
  def forty_nine : ℕ₀ := σ forty_eight
  def fifty : ℕ₀ := σ forty_nine
  def fifty_one : ℕ₀ := σ fifty
  def fifty_two : ℕ₀ := σ fifty_one
  def fifty_three : ℕ₀ := σ fifty_two
  def fifty_four : ℕ₀ := σ fifty_three
  def fifty_five : ℕ₀ := σ fifty_four
  def fifty_six : ℕ₀ := σ fifty_five
  def fifty_seven : ℕ₀ := σ fifty_six
  def fifty_eight : ℕ₀ := σ fifty_seven
  def fifty_nine : ℕ₀ := σ fifty_eight
  def sixty : ℕ₀ := σ fifty_nine
  def sixty_one : ℕ₀ := σ sixty
  def sixty_two : ℕ₀ := σ sixty_one
  def sixty_three : ℕ₀ := σ sixty_two
  def sixty_four : ℕ₀ := σ sixty_three

  notation "𝟙" => one
  notation "𝟚" => two
  notation "𝟛" => three
  notation "𝟜" => four
  notation "𝟝" => five
  notation "𝟞" => six
  notation "𝟟" => seven
  notation "𝟠" => eight
  notation "𝟡" => nine
  notation "𝔸" => ten
  notation "𝔹" => eleven
  notation "ℂ" => twelve
  notation "𝔻" => thirteen
  notation "𝔼" => fourteen
  notation "𝔽" => fifteen
  notation "𝔾" => sixteen
  notation "ℍ" => σ sixteen
  notation "𝕁" => σ seventeen
  notation "𝕂" => σ eighteen
  notation "𝕃" => σ nineteen
  notation "𝕄" => σ twenty
  notation "ℕ" => σ twenty_one
  notation "ℙ" => σ twenty_two
  notation "ℚ" => σ twenty_three
  notation "ℝ" => σ twenty_four
  notation "𝕊" => σ twenty_five
  notation "𝕋" => σ twenty_six
  notation "𝕌" => σ twenty_seven
  notation "𝕍" => σ twenty_eight
  notation "𝕎" => σ twenty_nine
  notation "𝕏" => σ thirty
  notation "𝕐" => σ thirty_one
  notation "ℤ" => σ thirty_two
  notation "ψ " => σ thirty_three
  notation "π" => σ thirty_four
  notation "δ" => σ thirty_five
  notation "γ" => σ thirty_six
  notation "ε" => σ thirty_seven
  notation "ζ" => σ thirty_eight
  notation "η" => σ thirty_nine
  notation "φ" => σ forty
  notation "ι" => σ forty_one
  notation "χ" => σ forty_two
  notation "λ" => σ forty_three
  notation "μ" => σ forty_four
  notation "ξ" => σ forty_five
  notation "ω" => σ forty_six
  notation "Γ" => σ forty_seven
  notation "Π" => σ forty_eight
  notation "𝕒" => σ forty_nine
  notation "𝕓" => σ fifty
  notation "𝕔" => σ fifty_one
  notation "𝕕" => σ fifty_two
  notation "𝕖" => σ fifty_three
  notation "𝕗" => σ fifty_four
  notation "𝕘" => σ fifty_five
  notation "𝕙" => σ fifty_six
  notation "𝕛" => σ fifty_seven
  notation "𝕞" => σ fifty_eight
  notation "𝕟" => σ fifty_nine
  notation "𝕡" => σ sixty
  notation "𝕢" => σ sixty_one
  notation "𝕣" => σ sixty_two
  notation "𝕤" => σ sixty_three
  notation "𝕪" => σ sixty_four

  /-- probaremos posteriormente que se trata de un isomorfismo-/
  def Λ(n : Nat) : ℕ₀ :=
    match n with
    | Nat.zero => 𝟘
    | Nat.succ k => σ (Λ k)

  theorem Λ_inj (n m : Nat) :
    Λ n = Λ m → n = m := by
      induction n generalizing m with
      | zero =>
        intro h_eq
        cases m with
        | zero =>
          rfl
        | succ m' =>
          exact ℕ₀.noConfusion h_eq
      | succ k ih =>
        intro h_eq
        cases m with
        | zero =>
          exact ℕ₀.noConfusion h_eq
        | succ m' =>
          -- h_eq : Λ (Nat.succ k) = Λ (Nat.succ m')
          -- Esto es σ (Λ k) = σ (Λ m')
          -- Por inyección, obtenemos Λ k = Λ m'
          injection h_eq with h_Λk_eq_Λm'

          -- ih : ∀ (m_local : Nat), Λ k = Λ m_local → k = m_local
          -- Aplicamos ih a m' y h_Λk_eq_Λm'
          have h_k_eq_m' : k = m' := ih m' h_Λk_eq_Λm'
          exact congrArg Nat.succ h_k_eq_m'

  /-- probaremos posteriormente que se trata de un isomorfismo-/
  def Ψ (n : ℕ₀) : Nat :=
    match n with
    | ℕ₀.zero => Nat.zero
    | ℕ₀.succ k => Nat.succ (Ψ k)

  theorem Ψ_inj (n m : ℕ₀) :
    (Ψ n) = (Ψ m) → n = m
      := by
      induction n generalizing m with
      | zero =>
        intro h_eq
        cases m with
        | zero =>
          rfl
        | succ m' =>
          exact Nat.noConfusion h_eq
      | succ k ih =>
        intro h_eq
        cases m with
        | zero =>
          exact Nat.noConfusion h_eq
        | succ m' =>
          -- h_eq : Ψ (σ k) = Ψ (σ m')
          -- Esto es Nat.succ (Ψ k) = Nat.succ (Ψ m')
          -- Por inyección, obtenemos Ψ k = Ψ m'
          injection h_eq with h_Ψk_eq_Ψm'
          -- ih : ∀ (m_local : ℕ₀), Ψ k = Ψ m_local → k = m_local
          -- Aplicamos ih a m' y h_Ψk_eq_Ψm'
          have h_k_eq_m' : k = m' := ih m' h_Ψk_eq_Ψm'
          exact congrArg ℕ₀.succ h_k_eq_m'

  theorem Λ_surj (k : ℕ₀) :
    k = Λ (Ψ k)
    := by
        induction k with
        | zero =>
          calc
            𝟘 = 𝟘 := rfl
            _ = Λ (Ψ 𝟘) := rfl
        | succ k ih =>
          calc
            σ k = σ (Λ (Ψ k))       := congrArg ℕ₀.succ ih
            _   = Λ (Nat.succ (Ψ k))  := rfl
            _   = Λ (Ψ (σ k))       := rfl

  theorem Λ_bij (n m : Nat) (k : ℕ₀) :
    (Λ n = Λ m ↔ n = m) ∧ (k = Λ (Ψ k))
    := by
        constructor
        · -- Prueba de (Λ n = Λ m ↔ n = m)
          apply Iff.intro
          · -- Prueba de (Λ n = Λ m → n = m)
            intro h_eq
            apply Λ_inj
            exact h_eq
          · -- Prueba de (n = m → Λ n = Λ m)
            intro h_eq
            rw [h_eq]
        · -- Prueba de (k = Λ (Ψ k))
          apply Λ_surj

  theorem Ψ_surj (n : Nat) :
    n = Ψ (Λ n)
    := by
        induction n with
        | zero =>
          calc
            0 = 0 := by rfl
            _ = Ψ (Λ 0) := by rfl
        | succ k ih =>
          calc
            Nat.succ k = Nat.succ (Ψ (Λ k))
                := congrArg Nat.succ ih
            _          = Ψ (σ (Λ k))
                := by rfl
            _          = Ψ (Λ (Nat.succ k))
                := by rfl

  theorem Ψ_bij (n m : ℕ₀) (k : Nat) :
    (Ψ n = Ψ m ↔ n = m) ∧ (k = Ψ (Λ k))
    := by
        constructor
        · -- Prueba de (Ψ n = Ψ m ↔ n = m)
          apply Iff.intro
          · -- Prueba de (Ψ n = Ψ m → n = m)
            intro h_eq
            apply Ψ_inj
            exact h_eq
          · -- Prueba de (n = m → Ψ n = Ψ m)
            intro h_eq
            rw [h_eq]
        · -- Prueba de (k = Ψ (Λ k))
          apply Ψ_surj

  instance : Coe Nat ℕ₀ where
    coe n := Λ n

  def id (n : ℕ₀) : ℕ₀ := n
  def idNat (n : Nat) : Nat := n
  def Eq {α β : Type} (f : α → β) (g : α → β) : Prop :=
    ∀ (x : α), f x = g x
  def Inv {α β : Type} (f : α → β) (g : β → α) : Prop :=
    ∀ (x : α), g (f x) = x
  def EqFn {α : Type}
          (f : ℕ₀ -> α)(g : ℕ₀ -> α) : Prop :=
    ∀ (x : ℕ₀), f x = g x
  def EqFnNat {α : Type}
          (f : Nat -> α)(g : Nat -> α) : Prop :=
    ∀ (x : Nat), f x = g x

  theorem Inv_Λ_eq_Ψ :
    Inv (Λ : Nat -> ℕ₀) (Ψ : ℕ₀ -> Nat)
        := by
        intro n
        induction n with
        | zero =>
          calc
            Ψ (Λ 0) = Ψ 𝟘 := by rfl
            _ = 0 := by rfl
        | succ k ih =>
          calc
            Ψ (Λ (Nat.succ k)) = Ψ (σ (Λ k)) := by rfl
            _ = Nat.succ (Ψ (Λ k)) := by rfl
            _ = Nat.succ k := by rw [ih]

  theorem Inv_Ψ_eq_Λ :
    Inv (Ψ : ℕ₀ -> Nat) (Λ : Nat -> ℕ₀)
        := by
        intro n
        induction n with
        | zero =>
          calc
            Λ (Ψ 𝟘) = Λ 0 := by rfl
            _ = 𝟘 := by rfl
        | succ k ih =>
          calc
            Λ (Ψ (σ k)) = σ (Λ (Ψ k)) := by rfl
            _ = σ k := by rw [ih]


  theorem EqFn_induction {α} (f : ℕ₀ -> α)(g : ℕ₀ -> α) :
    (
      (f 𝟘 = g 𝟘)
      ∧
      (
        ∀ (n: ℕ₀),
        (f n = g n) → (f (σ n) = g (σ n))
      )
    ) → (EqFn f g) := by
            intro h
            let h_0 := h.left
            let h_step := h.right
            intro n
            induction n with
            | zero =>
                exact h_0
            | succ k ih =>
                exact h_step k ih

  /--!
      LA SIGUIENTE ES UNA PRUEBA DE CONCEPTO (UN ENSAYO)
      DE COMO UTILIZAR EqFun Y EqFun_induction
     !-/
    theorem id_eq_id_lambda:
      EqFn id (λ (n : ℕ₀) => n)
          :=  by
              intro n
              rfl

  /--!
      LA IGUALDAD DE FUNCIONES ES UNA RELACIÓN DE EQUIVALENCIA
      (REFLEXIVA, SIMÉRICA Y TRANSITIVA)
     !-/
  theorem EqFn_refl {α} (f : ℕ₀ -> α) :
    EqFn f f := by
        intro n
        rfl

  theorem EqFn_symm {α} (f : ℕ₀ -> α)(g : ℕ₀ -> α) :
    EqFn f g → EqFn g f := by
        intro h n
        exact (h n).symm

  theorem EqFn_trans {α}
    (f : ℕ₀ -> α)
    (g : ℕ₀ -> α)
    (h : ℕ₀ -> α) :
    EqFn f g → EqFn g h → EqFn f h := by
        intro h_fg h_gh n
        exact (h_fg n).trans (h_gh n)

  /--
     LA SIGUIENTE FUNCIÓN PRED ES ISOMORFA A LA FUNCIÓN NAT.PRED
     SE SATURA CUANDO SUSTRAENDO ES MAYOR QUE MINUENDO A CERO
  -/
  def τ (n : ℕ₀) : ℕ₀ :=
    match n with
    | ℕ₀.zero => 𝟘
    | ℕ₀.succ k => k

  /--
     LA SIGUIENTE FUNCIÓN PRED ES CHEQUEADA Y PREFERIBLE
     A LA FUNCIÓN NAT.PRED
     (NO ES ISOMORFA A LA FUNCIÓN NAT.PRED)
  -/
  def ρ (n : ℕ₀) (h_n_neq_0 : n ≠ 𝟘) : ℕ₀ :=
    match n with
    | ℕ₀.zero =>
      False.elim (h_n_neq_0 rfl)
    | ℕ₀.succ k => k

  /--! Dada la prueba que n ≠ 0, pred n = pred_checked n h_n_neq_0 -/
  theorem ρ_eq_τ
          (n : ℕ₀)
          (h_n_neq_0 : n ≠ 𝟘) :
      ρ n h_n_neq_0 = τ n
          := by
              unfold ρ
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem τ_σ_eq_self (n : ℕ₀) :
      τ (σ n) = n
          := by
              unfold τ
              rfl

  theorem ρ_σ_eq_self
      (n : ℕ₀ )
      {h_succ_n_neq_0 : σ n ≠ 𝟘} :
      ρ (σ n) h_succ_n_neq_0 = n
          := by
              unfold ρ
              rfl

  theorem σ_ρ_eq_self(n: ℕ₀) (h_neq_0 : n ≠ 𝟘):
      σ (ρ n h_neq_0) = n
          := by
              unfold ρ
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem τ_σ_eq_self_forall:
      ∀ (n : ℕ₀), τ (σ n) = n
              := by
                  intros n
                  unfold τ
                  rfl

  theorem σ_ρ_eq_id_pos_elem (n: ℕ₀) (n_neq_0: n ≠ 𝟘):
      σ (ρ n n_neq_0) = n
          := by
              unfold ρ
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem σ_τ_eq_id_pos :
      ∀ (n : ℕ₀) (h : n ≠ 𝟘), σ (ρ n h) = n
          := by
              intros n h
              unfold ρ
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem ΨΛ (n: Nat) :
      Ψ (Λ n) = n
          := by
              induction n with
              | zero =>
                calc
                  Ψ (Λ Nat.zero) = Ψ 𝟘 := by rfl
                  _ = 0 := by rfl
              | succ k' ih =>
                unfold Λ Ψ
                dsimp
                rw [ih]

  theorem ΨΛ_eq_id :
      EqFnNat (Ψ ∘ Λ) idNat
          := by
              intro n
              exact ΨΛ   n

    theorem ΛΨ (n : ℕ₀) :
      Λ (Ψ n) = n
    := by
    induction n with
    | zero =>
      calc
        Λ (Ψ 𝟘) = Λ 0 := by rfl
        _ = 𝟘 := by rfl
    | succ k' ih =>
      simp only [Λ, Ψ]
      rw [ih]

    theorem Λψ_eq_id :
      EqFn (Λ ∘ Ψ) id
          := by
              intro n
              exact ΛΨ n

    theorem Ψ_σ_eq_σ_Λ (n : ℕ₀) :
      Ψ (σ n) = Nat.succ (Ψ n)
          := by
            induction n with
            | zero =>
              calc
                Ψ (σ 𝟘) = Ψ (σ 𝟘) := by rfl
                _ = Nat.succ (Ψ 𝟘) := by rfl
            | succ k' ih =>
              calc
                Ψ (σ (σ k')) = Ψ (σ (σ k')) := by rfl
                _ = Nat.succ (Ψ (σ k')) := by rfl
                _ = Nat.succ (Nat.succ (Ψ k')) := by rw [ih]

    theorem Ψ_σ_eq_σ_Λ_eqfn:
      EqFn ( Ψ ∘ ℕ₀.succ ) ( Nat.succ ∘ Ψ )
          := by
              intro n
              exact Ψ_σ_eq_σ_Λ n

    theorem Λ_σ_eq_σ_Ψ (n : Nat) :
      Λ (Nat.succ n) = σ (Λ n)
          := by
          induction n with
          | zero =>
            calc
              Λ (Nat.succ 0) = σ (Λ 0) := by rfl
          | succ k ih =>
            calc
              Λ (Nat.succ (Nat.succ k)) =
                  σ (Λ (Nat.succ k)) := by rfl
              _ = σ (σ (Λ k)) := by rw[ih]

        theorem Λ_σ_eq_σ_Ψ_eqfn:
          EqFnNat (Λ ∘ Nat.succ) (ℕ₀.succ ∘ Λ)
              := by
                  intro n
                  exact Λ_σ_eq_σ_Ψ n

        theorem Ψ_τ_eq_τ_Λ (n : ℕ₀) :
          Ψ (τ n) = Nat.pred (Ψ n)
              := by
                induction n with
                | zero =>
                  calc
                    Ψ (τ 𝟘) = Ψ (τ 𝟘) := by rfl
                    _ = Nat.pred (Ψ 𝟘) := by rfl
                | succ k' ih =>
                  calc
                    Ψ (τ (σ k')) = Ψ k'
                        := by simp only [τ_σ_eq_self]
                    _ = Nat.pred (Nat.succ (Ψ k'))
                        := by rw [Nat.pred_succ (Ψ k')]
                    _ = Nat.pred (Ψ (σ k'))
                        := by rw [Ψ_σ_eq_σ_Λ k']

        theorem Ψ_τ_eq_τ_Λ_eqfn:
          EqFn ( Ψ ∘ τ ) ( Nat.pred ∘ Ψ )
              := by
                  intro n
                  exact Ψ_τ_eq_τ_Λ n

        theorem Λ_τ_eq_τ_Ψ (n : Nat) :
          Λ (Nat.pred n) = τ (Λ n)
              := by
                induction n with
                | zero =>
                  calc
                    Λ (Nat.pred 0) = Λ (Nat.pred 0)
                        := by rfl
                    _ = τ 𝟘
                        := by rfl
                | succ k ih =>
                  calc
                    Λ (Nat.pred (Nat.succ k)) =
                        Λ k := by rfl
                    _ = τ (Λ (Nat.succ k))
                        := by
                            simp only [
                              Λ_σ_eq_σ_Ψ k,
                              τ_σ_eq_self
                            ]

end Peano

export Peano (
  Λ Ψ τ ρ cero
  Λ_inj Λ_surj Λ_bij
  Ψ_inj Ψ_surj Ψ_bij
  is_zero
  is_succ return_branch
  AXIOM_zero_is_an_PeanoNat
  AXIOM_succ_is_an_PeanoNat
  AXIOM_cero_neq_succ
  AXIOM_succ_is_funct_forall_n_in_PeanoNat
  AXIOM_uniqueness_on_image
  AXIOM_succ_inj
  succ_inj_neg
  AXIOM_zero_notin_ima_succ
  AXIOM_induction_on_PeanoNat
  BIs_zero BIs_succ
  category_by_constructor
  neq_succ
  is_zero_or_is_succ
  is_zero_xor_is_succ
  id idNat Inv
  Eq EqFn EqFnNat
  EqFn_refl EqFn_symm EqFn_trans
  EqFn_induction
  Inv_Λ_eq_Ψ Inv_Ψ_eq_Λ
  EqFn_induction
  EqFn_refl EqFn_symm EqFn_trans
  EqFn_induction id_eq_id_lambda
  EqFn_refl EqFn_symm EqFn_trans
  τ_σ_eq_self
  σ_ρ_eq_self σ_τ_eq_id_pos σ_ρ_eq_id_pos_elem
  ΨΛ ΛΨ Ψ_σ_eq_σ_Λ Λ_σ_eq_σ_Ψ Ψ_τ_eq_τ_Λ
  Λ_τ_eq_τ_Ψ id idNat EqFn EqFnNat EqFn_refl
  EqFn_symm EqFn_trans
  )
