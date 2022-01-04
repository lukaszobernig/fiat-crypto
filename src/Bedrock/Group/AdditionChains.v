Require Import Rupicola.Lib.Api.
Require Import Rupicola.Lib.Loops.
Require Import Rupicola.Lib.ControlFlow.DownTo.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.FLia.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Algebra.Hierarchy.
Require Import Numbers.DecimalString.

Local Open Scope Z_scope.

Section Utils.
  
    Lemma Nat_iter_plus_one :
      forall A f k (x : A), Nat.iter k f (f x) = Nat.iter (S k) f x.
    Proof.
      intros.
      induction k.
      - reflexivity.
      - simpl.
        rewrite IHk.
        f_equal.
    Qed.

End Utils.

Section FElems.

  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}. 
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Section Impl.
    Context (m : positive).
    Fixpoint exp_by_squaring (x : F m) (n : positive) : F m :=
      match n with
      | 1    => x
      | n'~0 => let/n res := exp_by_squaring x n' in
                let/n res := F.pow res 2 in
                res
      | n'~1 => let/n res := exp_by_squaring x n' in
                let/n res := F.pow res 2 in
                let/n res := F.mul x res in
                res
      end%positive.

    Fixpoint run_length_encoding (n : positive) : list (bool * nat) :=
      match n with
      | xH => [(true, 0)]
      | xO n' =>
        match (run_length_encoding n') with
        | (false, k) :: t => (false, k + 1) :: t
        | t => (false, 0) :: t
        end
      | xI n' =>
        match (run_length_encoding n') with
        | (true, k) :: t => (true, k + 1) :: t
        | t => (true, 0) :: t
        end
      end%nat.

    Definition exp_square_and_multiply (x : F m) (x' : F m) :=
      let/n res := F.pow x' 2 in
      let/n res := F.mul res x in
      res.

    Definition exp_square (x' : F m) :=
      let/n res := F.pow x' 2 in
      res.

    Fixpoint exp_from_encoding_simple (x : F m) (n : list (bool * nat)) : F m :=
      match n with
      | [] =>
        1
      (* can add more cases for small k to be faster *)
      | (true, 0%nat) :: t =>
        let/n res := exp_from_encoding_simple x t in
        let/n res := F.pow res 2 in
        let/n res := F.mul x res in
        res
      | (true, k) :: t =>
        let/n res := exp_from_encoding_simple x t in
        let/n res := Nat.iter (S k) (exp_square_and_multiply x) res in
        res
      | (false, 0%nat) :: t =>
        let/n res := exp_from_encoding_simple x t in
        let/n res := F.pow res 2 in
        res
      | (false, k) :: t =>
        let/n res := exp_from_encoding_simple x t in
        let/n res := Nat.iter (S k) (exp_square) res in
        res
      end.

    Fixpoint exp_from_encoding (x : F m) (n : list (bool * nat)) : F m :=
      match n with
      | [] =>
        1
      | [(true, 0%nat)] =>
        x
      | [(true, 1%nat)] =>
        let/n res := F.pow x 2 in
        let/n res := F.mul x res in
        res
      | [(true, (S k))] =>
        let/n res := F.pow x 2 in
        let/n res := F.mul x res in
        let/n res := Nat.iter k (exp_square_and_multiply x) res in
        res
      | [(false, 0%nat); (true, 0%nat)] =>
        let/n res := F.pow x 2 in
        res
      | [(false, k); (true, 0%nat)] =>
        let/n res := F.pow x 2 in
        let/n res := Nat.iter k (exp_square) res in
        res
      | (true, 0%nat) :: t =>
        let/n res := exp_from_encoding x t in
        let/n res := F.pow res 2 in
        let/n res := F.mul x res in
        res
      | (true, k) :: t =>
        let/n res := exp_from_encoding x t in
        let/n res := Nat.iter (S k) (exp_square_and_multiply x) res in
        res
      | (false, 0%nat) :: t =>
        let/n res := exp_from_encoding x t in
        let/n res := F.pow res 2 in
        res
      | (false, k) :: t =>
        let/n res := exp_from_encoding x t in
        let/n res := Nat.iter (S k) (exp_square) res in
        res
      end.

    Definition exp_by_squaring_encoded_simple (x : F m) (n : positive) : F m :=
      exp_from_encoding_simple x (run_length_encoding n).

    Definition exp_by_squaring_encoded (x : F m) (n : positive) : F m :=
      exp_from_encoding x (run_length_encoding n).
  End Impl.

  Section FUtils.
    Context (m : positive).
    (* FIXME go over this section with Dustin to understand why the code below
       is needed. *)
    
    Lemma solve_F_equality_via_Z lhs' rhs' (lhs rhs : F m)
      : F.to_Z lhs = lhs' mod Z.pos m ->
        F.to_Z rhs = rhs' mod Z.pos m ->
        lhs' = rhs' ->
        lhs = rhs.
    Proof.
      intros.
      rewrite <- (F.of_Z_to_Z lhs).
      rewrite <- (F.of_Z_to_Z rhs).
      intuition congruence.
    Qed.

    Lemma F_mul_to_Z a a' b b'
      : F.to_Z a = a' mod Z.pos m ->
        F.to_Z b = b' mod Z.pos m ->
        @F.to_Z m (a * b) = (a' * b') mod Z.pos m.
    Proof.
      intros H H0.
      rewrite F.to_Z_mul.
      rewrite H, H0.
      rewrite <- PullPush.Z.mul_mod_l.
      rewrite <- PullPush.Z.mul_mod_r.
      congruence.
    Qed.

    Lemma F_add_to_Z a a' b b'
      : F.to_Z a = a' mod Z.pos m ->
        F.to_Z b = b' mod Z.pos m ->
        @F.to_Z m (a + b) = (a' + b') mod Z.pos m.
    Proof.
      intros H H0.
      rewrite F.to_Z_add.
      rewrite H, H0.
      rewrite <- PullPush.Z.add_mod_l.
      rewrite <- PullPush.Z.add_mod_r.
      congruence.
    Qed.

    Lemma F_exp_to_Z a a' n
      : F.to_Z a = a' mod Z.pos m ->
        @F.to_Z m (a ^ n) = (a' ^ n) mod Z.pos m.
    Proof.
      intros H.
      rewrite F.to_Z_pow.
      rewrite H.
      rewrite <- PullPush.Z.mod_pow_full.
      congruence.
    Qed.

    Lemma F_var_to_Z (x : F m) : F.to_Z x = proj1_sig x mod Z.pos m.    Proof.
      destruct x; simpl; assumption.
    Qed.

    Lemma F_one_to_Z : @F.to_Z m 1 = 1 mod Z.pos m.
    Proof.
      reflexivity.
    Qed.


    Lemma F_const_to_Z c : F.to_Z (F.of_Z m c) = c mod Z.pos m.
    Proof.
      reflexivity.
    Qed.


    Definition Pos2N_pos_xI n : N.pos n~1 = (2 * N.pos n + 1)%N := eq_refl.
    Definition Pos2N_pos_xO n : N.pos n~0 = (2 * N.pos n)%N := eq_refl.
    
  End FUtils.

  Section Proofs.
    Context (m : positive).
   

    Lemma F_mul_1_r : forall x : F m,
        (x * 1)%F = x.
    Proof.
      intros.
      F_lia.
    Qed.

    Lemma F_mul_1_l : forall x : F m,
        (1 * x)%F = x.
    Proof.
      intros.
      F_lia.
    Qed.

    Create HintDb F_pow.
    Hint Rewrite @F.pow_2_r : F_pow.
    Hint Rewrite @F.pow_add_r : F_pow.
    Hint Rewrite @F.pow_mul_l : F_pow.
    Hint Rewrite <- @F.pow_pow_l : F_pow.
    Hint Rewrite @F.pow_1_r : F_pow.
    Hint Rewrite @F.pow_3_r : F_pow.

    Ltac simplify_F :=
      unfold nlet;
      autorewrite with F_pow;
      repeat rewrite F_mul_1_r;
      repeat rewrite F_mul_1_l; 
      try reflexivity;
      try F_lia.

     Lemma exp_by_squaring_correct :
      forall n x, exp_by_squaring m x n = (x ^ N.pos n)%F.
    Proof.
      induction n; intros; cbn [exp_by_squaring]; unfold nlet;
        rewrite (Pos2N_pos_xI n) || rewrite (Pos2N_pos_xO n) || idtac.
      all: try rewrite IHn.
      all: try destruct n eqn : H'; autorewrite with F_pow; try reflexivity.
      all: F_lia.
    Qed.

     Lemma run_length_encoding_nonempty:
      forall n, run_length_encoding n <> [].
    Proof.
      destruct n eqn : H'; simpl.
      + destruct (run_length_encoding p).
        { inversion 1. }
        destruct p0; destruct b; inversion 1.
      + destruct (run_length_encoding p).
        { inversion 1. }
        destruct p0; destruct b; inversion 1.
      + inversion 1.
    Qed.

    Lemma exp_by_squaring_encoded_simple_correct :
      forall n x, exp_by_squaring_encoded_simple m x n = (x ^ N.pos n)%F.
    Proof.
      intros. rewrite <- exp_by_squaring_correct; eauto.
      unfold exp_by_squaring_encoded_simple; induction n; simpl.
      - destruct (run_length_encoding n) eqn : Heq.
        + apply run_length_encoding_nonempty in Heq.
          inversion Heq.
        + destruct p. destruct b.
          * rewrite <- IHn.
            cbn. replace (n0 + 1)%nat with (S n0) by lia.
            unfold nlet; destruct n0; cbn; destruct n eqn : H'; unfold exp_square_and_multiply; unfold nlet; set (exp_from_encoding_simple _ x l) as expxl; F_lia.
          * rewrite <- IHn.
            cbn.
            unfold nlet.
            destruct n0; destruct n eqn : H'; try reflexivity.
      - rewrite <- IHn.
        destruct n eqn : H'.
        * destruct (run_length_encoding p~1) as [|[[|] n0] t]; try reflexivity.
          simpl.
          replace (n0 + 1)%nat with (S n0) by lia.
          unfold nlet.
          cbn.
          unfold exp_square.
          destruct n0; cbv [nlet Nat.iter]; simpl; F_lia.
        * destruct (run_length_encoding p~0) as [|[[|] n0] t]; try reflexivity.
          simpl.
          replace (n0 + 1)% nat with (S n0) by lia.
          unfold nlet.
          simpl.
          unfold exp_square.
          destruct n0; cbv [nlet Nat.iter]; simpl; F_lia.
        * unfold run_length_encoding.
          unfold exp_from_encoding_simple.
          simplify_F.
      - simplify_F.
    Qed.

    Lemma exp_by_squaring_encoded_correct :
      forall n x, exp_by_squaring_encoded m x n = (x ^ N.pos n)%F.

    Proof.
      intros. rewrite <- exp_by_squaring_encoded_simple_correct; eauto.
      unfold exp_by_squaring_encoded. unfold exp_by_squaring_encoded_simple.
      induction (run_length_encoding n).
      - cbn.
        reflexivity.
      - destruct a.
        destruct b; simpl exp_from_encoding; unfold exp_from_encoding_simple; fold exp_from_encoding_simple; destruct n0; try destruct n0; destruct l; try rewrite IHl; simpl exp_from_encoding_simple; try simplify_F.
        + unfold exp_square_and_multiply.
          simpl Nat.iter.
          simplify_F.
        + pose Nat_iter_plus_one.
          specialize e with (f := exp_square_and_multiply m x) (k := S (S n0)) (x := 1%F).
          rewrite <- e.
          replace (exp_square_and_multiply m x 1) with x.
          2: { unfold exp_square_and_multiply; simplify_F. }
          pose Nat_iter_plus_one.
          specialize e0 with (f := exp_square_and_multiply m x) (k := (S n0)) (x := x).
          rewrite <- e0.
          f_equal.
          unfold exp_square_and_multiply.
          simplify_F.
        + destruct p; destruct b; destruct n0; eauto.
          destruct l; eauto.
          unfold exp_from_encoding_simple.
          simplify_F.
        + destruct p; destruct b; destruct n0; eauto.
          destruct l; eauto.
          unfold exp_from_encoding_simple, exp_square.
          simpl Nat.iter.
          simplify_F.
        + destruct p; destruct b; destruct n1; eauto.
          destruct l; eauto.
          unfold exp_from_encoding_simple.
          simplify_F.
          pose Nat_iter_plus_one.
          specialize e with (f := exp_square m) (k := (S (S n0))) (x := x).
          rewrite <- e.
          unfold exp_square.
          simplify_F.
    Qed.

    Lemma clean_width :
      forall x, x < 2 ^ 32 -> x < 2 ^ width.
    Proof.
      intros; destruct width_cases as [ -> | -> ]; lia.
    Qed.
    
  End Proofs.

  Section Bedrock2.
    Section Lowering.
      Lemma letn_equal :
        forall A B (val : A) (body_l body_r : A -> B) (var : string),
          (let x := val in body_l x = body_r x)
          -> (let/n x as var := val in body_l x) = (let/n y as var := val in body_r y).
      Proof.
        intros. assumption.
      Qed.

      Lemma letn_nested :
        forall A B C (a : C) (val1 : A) (body1 : A -> B) (body2 : B -> C) (var var' : string),
          a = (let/n x as var' := val1 in let/n y as var := body1 x in body2 y)
          -> a = (let/n y as var := let/n x as var' := val1 in body1 x in body2 y).
      Proof.
        intros. assumption.
      Qed.

      Lemma letn_paren_equal :
        forall A B (a : A) (val : A) (body_r : A -> B) (var : string) left,
          left = (let/n y as var := val in (a, body_r y))
          -> left = (a, let/n y as var := val in body_r y).
      Proof.
        intros.
        rewrite H. reflexivity.
      Qed.
    End Lowering.

    Section Compilation.
      Hint Resolve @relax_bounds : compiler.

      Create HintDb lowering.
      Hint Unfold exp_by_squaring : lowering.
      Hint Unfold exp_by_squaring_encoded : lowering.
      Hint Unfold exp_from_encoding : lowering.
      Hint Unfold exp_by_squaring_encoded_simple : lowering.
      Hint Unfold exp_from_encoding_simple : lowering.
      Hint Unfold run_length_encoding : lowering.
      Hint Unfold exp_square : lowering.
      Hint Unfold exp_square_and_multiply : lowering.

      Ltac lower_step :=
        match goal with
        | [ |- forall _, _ ] =>
          intros
        | [ |- let _ := _ in _ = _ ] =>
          intros
        | [ |- _ = let/n _ as _ := ?x in _] =>
          is_var x; change (nlet _ ?x ?k) with (k x) at 1; cbv beta
        | [ |- _ = let/n _ as _ := (let/n _ as _ := _ in _) in _] =>
          eapply letn_nested
        | [ |- _ = let/n _ as _ := _ in _] =>
          eapply letn_equal with (body_l := fun _ => _)
        | [ |- _ = (_, let/n _ as _ := _ in _)] =>
          eapply letn_paren_equal
        end.

      Ltac lower_setup :=
        autounfold with lowering;
        lazymatch goal with
        | [ H := _ |- _ ] =>
          subst H
        end;
        repeat simpl Nat.add;
        cbn -[Nat.iter].

      Ltac lower :=
        lower_setup;
        repeat lower_step;
        reflexivity.

      (* TODO: Move to Rupicola's standard library and check if it breaks anything*)
      Ltac compile_try_copy_pointer :=
        lazymatch goal with
        | [ |- WeakestPrecondition.cmd _ _ _ ?mem _ (_ (nlet_eq [ _ ] ?x _)) ] =>
          lazymatch goal with
          | [ H : ?pred mem |- _ ] =>
            lazymatch pred with
            | context [ ?data ?ptr x ] =>
              simple eapply @compile_copy_pointer with (x_ptr := ptr) (Data := data)
            end
          end
        end.

      Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

      Context {field_parameters : FieldParameters}.
      Context {field_representaton : FieldRepresentation}.
      Context {field_representation_ok : FieldRepresentation_ok}.

      Definition exp (e : positive) (x : F M_pos) := F.pow x (N.pos e).

      Instance spec_of_exp_6
      : spec_of "exp_6" :=
        fnspec! "exp_6" (x_ptr sq_ptr : word) / (x sq : F M_pos) R,
        { requires tr mem :=
            (FElem (Some tight_bounds) x_ptr x
             * FElem (Some tight_bounds) sq_ptr sq * R)%sep mem;
          ensures tr' mem' :=
            tr = tr'
            /\ (FElem (Some tight_bounds) x_ptr x
                * FElem (Some tight_bounds) sq_ptr (exp 6 x) * R)%sep mem'}.

      Ltac rewrite_exponentiation lemma :=
        lazymatch goal with
        | |- WeakestPrecondition.cmd _ _ _ ?mem _ (_ (?x ^ N.pos ?n)%F) =>
          eassert (?[rewritten] = (x ^ N.pos n)%F) as <-
              by (rewrite <- lemma by assumption;
                  lower; reflexivity)
        end.

      Section Exp_by_squaring.
        Hint Extern 1 => rewrite_exponentiation exp_by_squaring_correct; shelve : compiler_cleanup.

        Derive exp_6_body SuchThat
          (defn! "exp_6" ("x", "res") { exp_6_body },
          implements (exp 6) using [square; mul])
          As exp_6_body_correct.
        Proof.
          compile.
        Qed.
      End Exp_by_squaring.

      Instance spec_of_exp97 : spec_of "exp_97" :=
        fnspec! "exp_97" (x_ptr sq_ptr : word) / (x sq : F M_pos) R,
        { requires tr mem :=
            (FElem (Some tight_bounds) x_ptr x
             * FElem (Some tight_bounds) sq_ptr sq * R)%sep mem;
          ensures tr' mem' :=
            tr = tr'
            /\ (FElem (Some tight_bounds) x_ptr x
                * FElem (Some tight_bounds) sq_ptr (exp 97 x)  * R)%sep mem'}.

      Local Instance spec_of_exp_large : spec_of "fe25519_inv" :=
        fnspec! "fe25519_inv" (x_ptr sq_ptr : word) / (x sq : F M_pos) R,
        { requires tr mem :=
            (FElem (Some tight_bounds) x_ptr x
             * FElem (Some tight_bounds) sq_ptr sq * R)%sep mem;
          ensures tr' mem' :=
            tr = tr'
            /\ (FElem (Some tight_bounds) x_ptr x
            * FElem (Some tight_bounds) sq_ptr (exp (2^255-21) x)  * R)%sep mem'}.

      Import LoopCompiler.
      Hint Resolve clean_width : compiler_side_conditions.
      Hint Extern 10 => lia : compiler_side_conditions.
      Hint Extern 1 => simple apply compile_square; shelve : compiler.
      Hint Extern 1 => simple apply compile_mul; shelve : compiler.
      Hint Extern 1 => compile_downto; shelve : compiler.
      Hint Extern 1 => compile_try_copy_pointer; shelve : compiler.

      Hint Extern 1 => rewrite_exponentiation exp_by_squaring_encoded_correct; shelve : compiler_cleanup.

      Derive exp_97_body SuchThat
             (defn! "exp_97" ("x", "res") { exp_97_body },
              implements (exp 97) using [square; mul])
             As exp_97_body_correct.
      Proof.
        compile.
      Qed.

      Print Assumptions exp_6_body. (* does not depend on [width] or [word] *)
      Print Assumptions exp_97_body. (* depends on [width] and  [word] :/ *)

      Derive fe25519_inv SuchThat
             (defn! "fe25519_inv" ("x", "res") { fe25519_inv },
             implements (exp (2^255-21)) using [square; mul])
             As fe25519_inv_correct_exp.
      Proof.
        compile.
      Qed.

    Global Instance spec_of_fe25519_inv : spec_of "fe25519_inv" :=
      fnspec! "fe25519_inv" (x_ptr sq_ptr : word) / (x sq : F M_pos) R,
      { requires tr mem :=
          (FElem (Some tight_bounds) x_ptr x
           * FElem (Some tight_bounds) sq_ptr sq * R)%sep mem;
        ensures tr' mem' :=
          tr = tr'
          /\ (FElem (Some tight_bounds) x_ptr x
          * FElem (Some tight_bounds) sq_ptr (F.inv x)  * R)%sep mem'}.

    Require Import Crypto.Spec.Curve25519.
    Lemma fe_inv_correct : 
      Z.pos M_pos = 2^255-19 ->
      program_logic_goal_for_function! fe25519_inv.
    Proof.
      intros Hm HmPrime ? ** ? **.
      eapply Proper_call; [|eapply fe25519_inv_correct_exp; eauto 1; exact I].
      intros ? ** ? ** ? ** ?; intuition idtac.
      unshelve erewrite F.Fq_inv_fermat; rewrite Hm; try vm_decide.
      { exact Curve25519.prime_p. }
      { assumption. }
    Qed.

    End Compilation.
  End Bedrock2.
End FElems.

(* LATER: Make a separate compilation lemma for (loop) *)

Require Import bedrock2.BasicC64Semantics.

Section Extraction.
  Definition _M_pos := (2 ^ 255 - 19)%positive.
  Context (_a24: F _M_pos).

  Instance fp : FieldParameters :=
    {| M_pos := _M_pos;
       a24 := _a24;
       mul := "mul";
       add := "add";
       sub := "sub";
       opp := "opp";
       square := "square";
       scmula24 := "scmula24";
       inv := "inv";
       from_bytes := "from_bytes";
       to_bytes := "to_bytes";
       felem_copy := "felem_copy";
       felem_small_literal := "felem_small_literal" |}.
End Extraction.