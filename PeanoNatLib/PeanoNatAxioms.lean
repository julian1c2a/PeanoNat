-- import Mathlib.Logic.Classical

-- PeanoNatAxioms.lean


inductive PeanoNat : Type
  where
  | zero : PeanoNat
  | succ : PeanoNat -> PeanoNat
  deriving Repr, BEq, DecidableEq


namespace PeanoNat
    set_option trace.Meta.Tactic.simp true

  def ℕ₀ : Type := PeanoNat

  notation "σ" n:max => PeanoNat.succ n
  def cero : ℕ₀ := PeanoNat.zero
  notation "𝟎" => cero

  def is_zero : ℕ₀ -> Prop :=
    fun n =>
      match n with
      | zero => True
      | succ _ => False

  def is_succ : ℕ₀ -> Prop :=
    fun n =>
      match n with
      | zero => False
      | succ _ => True

  /--!
      EL SIGUIENTE AXIOMA SE DA POR QUE IS_ZERO INDICA
      QUE ES UNA RAMA DEL CONSTRUCTOR DE PEANONAT
     !-/
  theorem AXIOM_zero_is_an_PeanoNat :
      is_zero 𝟎 := by
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
      {k : ℕ₀}
      (n : ℕ₀)
      (h_ex_k : n = k.succ):
          cero ≠ k.succ
              := by
                  cases n with
                  | zero =>
                      contradiction
                  | succ n' =>
                      apply PeanoNat.noConfusion

  theorem AXIOM_cero_neq_succ :
          ∀ (k : ℕ₀), cero ≠ succ k
              := by
                  intro k
                  apply cero_neq_succ
                  rfl

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
                  := congrArg PeanoNat.succ h_eq
              absurd h_succ_eq h_neq_succ

  /--!
      AXIOMA DE PEANO:
          0 NO ES SUCESOR DE NINGÚN NÚMERO NATURAL.

      EN LEAN4 ESTO VIENE DADO POR EL CONSTRUCTOR QUE TIENE LA PROPIEDAD NOCONFUSION
     !-/
  theorem succ_neq_zero (n : ℕ₀) :
      σ n ≠ zero
          := by
              intro h_eq
              apply PeanoNat.noConfusion h_eq

  theorem AXIOM_zero_notin_ima_succ :
      ∀ (n : ℕ₀), zero ≠ σ n
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
      (h_0 : P zero)
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
      | zero => true
      | succ _ => false

  def BIs_succ : ℕ₀ -> Bool :=
    fun n =>
      match n with
      | zero => false
      | succ _ => true

  def category_by_constructor (n : ℕ₀) : ℕ₀ -> Prop :=
    match n with
    | zero => is_zero
    | succ _ => is_succ

  axiom tertium_non_datur (p : Prop) : p ∨ ¬p

  theorem neq_succ (k : PeanoNat) : k ≠ succ k := by
    induction k with
    | zero =>
      intro h_eq_zero_succ_zero
      exact PeanoNat.succ_neq_zero zero h_eq_zero_succ_zero.symm
    | succ k' ih_k' =>
      intro h_eq_succ_k_succ_succ_k
      have h_k_eq_succ_k : k' = succ k' := PeanoNat.succ.inj h_eq_succ_k_succ_succ_k
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
  def one : ℕ₀ := σ cero
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

  notation "𝟏" => one
  notation "𝟐" => two
  notation "𝟑" => three
  notation "𝟒" => four
  notation "𝟓" => five
  notation "𝟔" => six
  notation "𝟕" => seven
  notation "𝟖" => eight
  notation "𝟗" => nine
  notation "𝐀" => ten
  notation "𝐁" => eleven
  notation "𝐂" => twelve
  notation "𝐃" => thirteen
  notation "𝐄" => fourteen
  notation "𝐅" => fifteen
  notation "𝐆" => sixteen
  notation "𝐇" => σ sixteen
  notation "𝚪" => σ seventeen
  notation "𝐉" => σ eighteen
  notation "𝐊" => σ nineteen
  notation "𝐋" => σ twenty
  notation "𝐌" => σ twenty_one
  notation "𝐍" => σ twenty_two
  notation "𝐎" => σ twenty_three
  notation "𝐏" => σ twenty_four
  notation "𝐐" => σ twenty_five
  notation "𝐑" => σ twenty_six
  notation "𝐒" => σ twenty_seven
  notation "𝐓" => σ twenty_eight
  notation "𝐔" => σ twenty_nine
  notation "𝐕" => σ thirty
  notation "𝐖" => σ thirty_one
  notation "𝐗" => σ thirty_two
  notation "𝐘" => σ thirty_three
  notation "𝐙" => σ thirty_four
  notation "𝛂" => σ thirty_five
  notation "𝛃" => σ thirty_six
  notation "𝛄" => σ thirty_seven
  notation "𝛅" => σ thirty_eight
  notation "𝛆" => σ thirty_nine
  notation "𝛇" => σ forty
  notation "𝛈" => σ forty_one
  notation "𝛉" => σ forty_two
  notation "𝛊" => σ forty_three
  notation "𝛋" => σ forty_four
  notation "𝛌" => σ forty_five
  notation "𝛍" => σ forty_six
  notation "𝛏" => σ forty_seven
  notation "𝛚" => σ forty_eight
  notation "𝐚" => σ forty_nine
  notation "𝐛" => σ fifty
  notation "𝐜" => σ fifty_one
  notation "𝐝" => σ fifty_two
  notation "𝐞" => σ fifty_three
  notation "𝐟" => σ fifty_four
  notation "𝐠" => σ fifty_five
  notation "𝐡" => σ fifty_six
  notation "𝐣" => σ fifty_seven
  notation "𝐤" => σ fifty_eight
  notation "𝐦" => σ fifty_nine
  notation "𝐧" => σ sixty
  notation "𝐩" => σ sixty_one
  notation "𝐪" => σ sixty_two
  notation "𝐫" => σ sixty_three
  notation "𝐬" => σ sixty_four

  /-- probaremos posteriormente que se trat de un isomorfismo-/
  def nat2pea (n : Nat) : ℕ₀ :=
    match n with
    | Nat.zero => 𝟎
    | Nat.succ k => PeanoNat.succ (nat2pea k)

  /-- probaremos posteriormente que se trat de un isomorfismo-/
  def pea2nat (n : ℕ₀) : Nat :=
    match n with
    | zero => Nat.zero
    | succ k => Nat.succ (pea2nat k)

  instance : Coe Nat PeanoNat where
    coe n := nat2pea n

  def id (n : ℕ₀) : ℕ₀ := n
  def idNat (n : Nat) : Nat := n
  def Eq {α β : Type}
          (f : α -> β)(g : α -> β) : Prop :=
    ∀ (x : α), f x = g x
  def EqFn {α : Type}
          (f : ℕ₀ -> α)(g : ℕ₀ -> α) : Prop :=
    ∀ (x : ℕ₀), f x = g x
  def EqFnNat {α : Type}
          (f : Nat -> α)(g : Nat -> α) : Prop :=
    ∀ (x : Nat), f x = g x

  theorem EqFn_induction {α} (f : ℕ₀ -> α)(g : ℕ₀ -> α) :
    ((f zero = g zero) ∧ (∀ n, (f n = g n) → (f (σ n) = g (σ n)))) → (EqFn f g) := by
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
  def pred (n : ℕ₀) : ℕ₀ :=
    match n with
    | zero => zero
    | succ k => k

  notation "σ⁻¹" => pred

  /--
     LA SIGUIENTE FUNCIÓN PRED ES CHEQUEADA Y PREFERIBLE
     A LA FUNCIÓN NAT.PRED
     (NO ES ISOMORFA A LA FUNCIÓN NAT.PRED)
  -/
  def pred_checked (n : PeanoNat) (h_n_neq_0 : n ≠ cero) : PeanoNat :=
    match n with
    | zero =>
      False.elim (h_n_neq_0 rfl)
    | succ k => k

  notation "σ⁻¹ₕₖ" => pred_checked

  /--! Dada la prueba que n ≠ 0, pred n = pred_checked n h_n_neq_0 -/
  theorem pred_checked_eq_pred
          (n : ℕ₀)
          (h_n_neq_0 : n ≠ 𝟎) :
      σ⁻¹ₕₖ n h_n_neq_0 = σ⁻¹ n
          := by
              unfold pred_checked
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem pred_succ_eq_self (n : ℕ₀) :
      σ⁻¹ (σ n) = n
          := by
              unfold pred
              rfl

  theorem pred_checked_succ_eq_self
      (n : ℕ₀ )
      {h_succ_n_neq_0 : σ n ≠ 𝟎} :
      σ⁻¹ₕₖ (σ n) h_succ_n_neq_0 = n
          := by
              unfold pred_checked
              rfl

  theorem succ_pred_checked_eq_self(n: ℕ₀) (h_neq_0 : n ≠ 𝟎):
      σ (σ⁻¹ₕₖ n h_neq_0) = n
          := by
              unfold pred_checked
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem pred_succ_eq_self_forall:
      ∀ (n : ℕ₀) (_ : σ n ≠ 𝟎),
          σ⁻¹ (σ n) = n
              := by
                  intros n h_succ_n_neq_0
                  unfold pred
                  rfl

  theorem succ_pred_checked_eq_id_pos_byelem (n: ℕ₀) (n_neq_0: n ≠ 𝟎):
      σ (σ⁻¹ₕₖ n n_neq_0) = n
          := by
              unfold pred_checked
              cases n
              case zero =>
                contradiction
              case succ k =>
                rfl

  theorem succ_pred_eq_id_pos :
      ∀ (n : PeanoNat) (h : n ≠ 𝟎), succ (pred_checked n h) = n
          := by
              intros n h
              unfold pred_checked
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
                  pea2nat (nat2pea Nat.zero) = pea2nat 𝟎 := by rfl
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

    theorem pea2nat2pea (n : PeanoNat) :
      nat2pea (pea2nat n) = n
    := by
    induction n with
    | zero =>
      calc
        nat2pea (pea2nat 𝟎) = nat2pea Nat.zero := by rfl
        _ = 𝟎 := by rfl
    | succ k' ih =>
      simp only [nat2pea, pea2nat]
      rw [ih]

    theorem pea2nat2pea_eq_id :
      EqFn (nat2pea ∘ pea2nat) id
          := by
              intro n
              exact pea2nat2pea n

    theorem pea2nat_succ_eq_succ_nat2pea (n : PeanoNat) :
      pea2nat (σ n) = Nat.succ (pea2nat n)
          := by
            induction n with
            | zero =>
              calc
                pea2nat (σ 𝟎) = pea2nat (σ zero) := by rfl
                _ = Nat.succ (pea2nat 𝟎) := by rfl
            | succ k' ih =>
              calc
                pea2nat (σ (σ k')) = pea2nat (σ (succ k')) := by rfl
                _ = Nat.succ (pea2nat (σ k')) := by rfl
                _ = Nat.succ (Nat.succ (pea2nat k')) := by rw [ih]

    theorem pea2nat_succ_eq_succ_nat2pea_eqfn:
      EqFn (pea2nat ∘ PeanoNat.succ) (Nat.succ ∘ pea2nat)
          := by
              intro n
              exact pea2nat_succ_eq_succ_nat2pea n

    theorem nat2pea_succ_eq_succ_pea2nat (n : Nat) :
      nat2pea (Nat.succ n) = σ (nat2pea n)
          := by
          induction n with
          | zero =>
            calc
              nat2pea (Nat.succ Nat.zero) =
                  nat2pea (Nat.succ 0) := by rfl
              _ = σ (nat2pea Nat.zero) := by rfl
              _ = σ (nat2pea 0) := by rfl
          | succ k ih =>
            calc
              nat2pea (Nat.succ (Nat.succ k)) =
                  σ (nat2pea (Nat.succ k)) := by rfl
              _ = σ (σ (nat2pea k)) := by rw[ih]

        theorem nat2pea_succ_eq_succ_pea2nat_eqfn:
          EqFnNat (nat2pea ∘ Nat.succ) (PeanoNat.succ ∘ nat2pea)
              := by
                  intro n
                  exact nat2pea_succ_eq_succ_pea2nat n

        theorem pea2nat_pred_eq_pred_nat2pea (n : PeanoNat) :
          pea2nat (σ⁻¹ n) = Nat.pred (pea2nat n)
              := by
                induction n with
                | zero =>
                  calc
                    pea2nat (σ⁻¹ 𝟎) = pea2nat (σ⁻¹ zero) := by rfl
                    _ = Nat.pred (pea2nat 𝟎) := by rfl
                | succ k' ih =>
                  calc
                    pea2nat (σ⁻¹ (σ k'))
                        = pea2nat k' := by simp only [pred_succ_eq_self]
                    _ = Nat.pred (Nat.succ (pea2nat k')) := by rw [Nat.pred_succ (pea2nat k')]
                    _ = Nat.pred (pea2nat (σ k')) := by rw [pea2nat_succ_eq_succ_nat2pea k']

        theorem pea2nat_pred_eq_pred_nat2pea_eqfn:
          EqFn ( pea2nat ∘ σ⁻¹ ) ( Nat.pred ∘ pea2nat )
              := by
                  intro n
                  exact pea2nat_pred_eq_pred_nat2pea n

        theorem nat2pea_pred_eq_pred_pea2nat (n : Nat) :
          nat2pea (Nat.pred n) = σ⁻¹ (nat2pea n)
              := by
                induction n with
                | zero =>
                  calc
                    nat2pea (Nat.pred Nat.zero) = nat2pea (Nat.pred 0) := by rfl
                    _ = σ⁻¹ 𝟎 := by rfl
                | succ k ih =>
                  calc
                    nat2pea (Nat.pred (Nat.succ k)) =
                        nat2pea k := by rfl
                    _ = σ⁻¹ (nat2pea (Nat.succ k))
                        := by
                            simp only [
                              nat2pea_succ_eq_succ_pea2nat k,
                              pred_succ_eq_self
                            ]

end PeanoNat
