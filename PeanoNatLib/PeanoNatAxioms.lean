-- import Mathlib.Logic.Classical

-- PeanoNatAxioms.lean


inductive ℕ₀ : Type
  where
  | zero : ℕ₀
  | succ : ℕ₀ -> ℕ₀
  deriving Repr, BEq, DecidableEq


namespace PeanoNat
    set_option trace.Meta.Tactic.simp true


  notation "σ" n:max => ℕ₀.succ n
  notation "𝟘" => ℕ₀.zero

  def is_zero : ℕ₀ -> Prop :=
    fun n =>
      match n with
      | ℕ₀.zero => True
      | ℕ₀.succ _ => False

  def is_succ : ℕ₀ -> Prop :=
    fun n =>
      match n with
      | ℕ₀.zero => False
      | ℕ₀.succ _ => True

  def return_rama : ℕ₀ -> Prop :=
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
      (h_ex_k : n = σ n):
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
      ∀ (n : ℕ₀), ∃ (k : ℕ₀), k = n.succ
          := by
              intro n
              exists n.succ

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
      {P : ℕ₀ -> Prop}
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
      | 𝟘   => true
      | σ _ => false

  def BIs_succ : ℕ₀ -> Bool :=
    fun n =>
      match n with
      | 𝟘   => false
      | σ _ => true

  def category_by_constructor (n : ℕ₀) : ℕ₀ -> Prop :=
    match n with
    | 𝟘 => is_zero
    | σ _ => is_succ

  theorem neq_succ (k : ℕ₀) : k ≠ σ k := by
    induction k with
    | zero =>
      intro h_eq_zero_succ_zero
      exact PeanoNat.succ_neq_zero 𝟘 h_eq_zero_succ_zero.symm
    | succ k' ih_k' =>
      intro h_eq_succ_k_succ_succ_k
      have h_k_eq_succ_k : k' = σ k' := PeanoNat.AXIOM_succ_inj k' (σ k') h_eq_succ_k_succ_succ_k
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
  notation "Λ" => σ forty_eight
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

  /-- probaremos posteriormente que se trat de un isomorfismo-/
  def nat2pea (n : Nat) : ℕ₀ :=
    match n with
    | Nat.zero => 𝟘
    | Nat.succ k => σ (nat2pea k)

  /-- probaremos posteriormente que se trat de un isomorfismo-/
  def pea2nat (n : ℕ₀) : Nat :=
    match n with
    | 𝟘 => Nat.zero
    | σ k => Nat.succ (pea2nat k)

  instance : Coe Nat ℕ₀ where
    coe n := nat2pea n

  def id (n : ℕ₀) : ℕ₀ := n
  def idNat (n : Nat) : Nat := n
  def Eq {α β : Type} (f : α → β) (g : α → β) : Prop :=
    ∀ (x : α), f x = g x
  def EqFn {α : Type}
          (f : ℕ₀ -> α)(g : ℕ₀ -> α) : Prop :=
    ∀ (x : ℕ₀), f x = g x
  def EqFnNat {α : Type}
          (f : Nat -> α)(g : Nat -> α) : Prop :=
    ∀ (x : Nat), f x = g x

  theorem EqFn_induction {α} (f : ℕ₀ -> α)(g : ℕ₀ -> α) :
    ((f 𝟘 = g 𝟘) ∧ (∀ n, (f n = g n) → (f (σ n) = g (σ n)))) → (EqFn f g) := by
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
      (REFLEXIVA, SIMÉTRICA Y TRANSITIVA)
     !-/
  theorem EqFn_reflexivity {α} (f : ℕ₀ -> α) :
    EqFn f f := by
        intro n
        rfl

  theorem EqFn_symmetry {α} (f : ℕ₀ -> α)(g : ℕ₀ -> α) :
    EqFn f g → EqFn g f := by
        intro h n
        exact (h n).symm

  theorem EqFn_transitivity {α}
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
    | 𝟘 => 𝟘
    | σ k => k

  /--
     LA SIGUIENTE FUNCIÓN PRED ES CHEQUEADA Y PREFERIBLE
     A LA FUNCIÓN NAT.PRED
     (NO ES ISOMORFA A LA FUNCIÓN NAT.PRED)
  -/
  def ρ (n : ℕ₀) (h_n_neq_0 : n ≠ 𝟘) : ℕ₀ :=
    match n with
    | 𝟘 =>
      False.elim (h_n_neq_0 rfl)
    | σ k => k


  /--! Dada la prueba que n ≠ 0, pred n = pred_checked n h_n_neq_0 -/
  theorem pred_checked_eq_pred
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

  theorem pred_succ_eq_self (n : ℕ₀) :
      τ (σ n) = n
          := by
              unfold τ
              rfl

  theorem pred_checked_succ_eq_self
      (n : ℕ₀ )
      {h_succ_n_neq_0 : σ n ≠ 𝟘} :
      ρ (σ n) h_succ_n_neq_0 = n
          := by
              unfold ρ
              rfl

  theorem succ_pred_checked_eq_self(n: ℕ₀) (h_neq_0 : n ≠ 𝟘):
      σ (ρ n h_neq_0) = n
          := by
              unfold ρ
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem pred_succ_eq_self_forall:
      ∀ (n : ℕ₀) (_ : σ n ≠ 𝟘),
          τ (σ n) = n
              := by
                  intros n h_succ_n_neq_0
                  unfold τ
                  rfl

  theorem succ_pred_checked_eq_id_pos_byelem (n: ℕ₀) (n_neq_0: n ≠ 𝟘):
      σ (ρ n n_neq_0) = n
          := by
              unfold ρ
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem succ_pred_eq_id_pos :
      ∀ (n : ℕ₀) (h : n ≠ 𝟘), σ (ρ n h) = n
          := by
              intros n h
              unfold ρ
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem nat2pea2nat (n: Nat) :
      pea2nat (nat2pea n) = n
          := by
              induction n with
              | zero =>
                calc
                  pea2nat (nat2pea Nat.zero) = pea2nat 𝟘 := by rfl
                  _ = Nat.zero := by rfl
              | succ k' ih =>
                unfold nat2pea pea2nat
                dsimp
                rw [ih]

  theorem nat2pea2nat_eq_id :
      EqFnNat (pea2nat ∘ nat2pea) idNat
          := by
              intro n
              exact nat2pea2nat n

    theorem pea2nat2pea (n : ℕ₀) :
      nat2pea (pea2nat n) = n
    := by
    induction n with
    | zero =>
      calc
        nat2pea (pea2nat 𝟘) = nat2pea Nat.zero := by rfl
        _ = 𝟘 := by rfl
    | succ k' ih =>
      simp only [nat2pea, pea2nat]
      rw [ih]

    theorem pea2nat2pea_eq_id :
      EqFn (nat2pea ∘ pea2nat) id
          := by
              intro n
              exact pea2nat2pea n
    theorem pea2nat_succ_eq_succ_nat2pea (n : ℕ₀) :
      pea2nat (σ n) = Nat.succ (pea2nat n)
          := by
            induction n with
            | zero =>
              calc
                pea2nat (σ 𝟘) = pea2nat (σ 𝟘)
                      :=    by rfl
                _ = Nat.succ Nat.zero
                      := by rfl
                _ = Nat.succ (pea2nat 𝟘)
                      := by rfl
            | succ k' ih =>
              calc
                pea2nat (σ (σ k')) = pea2nat (σ (σ k'))
                    := by rfl
                _ = Nat.succ (pea2nat (σ k'))
                    := by rfl
                _ = Nat.succ (Nat.succ (pea2nat k'))
                    := by rw [ih]

    theorem pea2nat_succ_eq_succ_nat2pea_eqfn:
      EqFn ( pea2nat ∘ ℕ₀.succ ) ( Nat.succ ∘ pea2nat )
          := by
              intro n
              exact pea2nat_succ_eq_succ_nat2pea n

    theorem nat2pea_succ_eq_succ_pea2nat (n : Nat) :
      nat2pea (Nat.succ n) = σ (nat2pea n)
          := by
          rfl

        theorem nat2pea_succ_eq_succ_pea2nat_eqfn:
          EqFnNat (nat2pea∘Nat.succ) (ℕ₀.succ∘nat2pea)
              := nat2pea_succ_eq_succ_pea2nat

        theorem pea2nat_pred_eq_pred_nat2pea (n : ℕ₀) :
          pea2nat (τ n) = Nat.pred (pea2nat n)
              := by
                induction n with
                | zero =>
                  calc
                    pea2nat (τ 𝟘) = pea2nat (τ 𝟘)
                        := by rfl
                    _ = Nat.pred (pea2nat 𝟘)
                        := by rfl
                | succ k' ih =>
                  calc
                    pea2nat (τ (σ k'))
                        = pea2nat k'
                            := by simp only
                               [pred_succ_eq_self]
                    _ = Nat.pred (Nat.succ (pea2nat k'))
                        := by rw
                            [Nat.pred_succ (pea2nat k')]
                    _ = Nat.pred (pea2nat (σ k'))
                        := by rw
                         [pea2nat_succ_eq_succ_nat2pea
                          k']

        theorem pea2nat_pred_eq_pred_nat2pea_eqfn:
          EqFn ( pea2nat ∘ τ ) ( Nat.pred ∘ pea2nat )
              := by
                  intro n
                  exact pea2nat_pred_eq_pred_nat2pea n

        theorem nat2pea_pred_eq_pred_pea2nat (n : Nat) :
          nat2pea (Nat.pred n) = τ (nat2pea n)
              := by
                induction n with
                | zero =>
                  calc
                    nat2pea (Nat.pred Nat.zero) = nat2pea (Nat.pred 0) := by rfl
                    _ = τ 𝟘 := by rfl
                | succ k ih =>
                  calc
                    nat2pea (Nat.pred (Nat.succ k)) =
                        nat2pea k := by rfl
                    _ = τ (nat2pea (Nat.succ k))
                        := by
                            simp only [
                              nat2pea_succ_eq_succ_pea2nat k,
                              pred_succ_eq_self
                            ]

end PeanoNat
