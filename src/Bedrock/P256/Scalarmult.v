Require Import String coqutil.Datatypes.List.
Require Import Bedrock.P256.Specs.
Import Specs.NotationsCustomEntry Specs.coord Specs.point.
Import bedrock2.Syntax bedrock2.NotationsCustomEntry
bedrock2.ZnWords
LittleEndianList
Crypto.Util.ZUtil.Modulo Zdiv ZArith BinInt
BinInt BinNat Init.Byte
PrimeFieldTheorems ModInv
micromega.Lia
coqutil.Byte
Lists.List
Jacobian
ProgramLogic WeakestPrecondition
Word.Interface OfListWord Separation SeparationLogic
BasicC64Semantics
ListNotations
SepAutoArray
Tactics
UniquePose
Word.Properties
memcpy.
Require Import Coq.Lists.List.

Require Import Coq.Classes.Morphisms.

Import ProgramLogic.Coercions.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
Local Open Scope list_scope.

Require Import Crypto.Arithmetic.Signed.

Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.AffineProofs.

Require Import Crypto.Curves.Weierstrass.P256.

Module W.
  (* HACK: Rewrite W.eq * W.zero hangs with Proper (Logic.eq ==> W.eq ==> W.eq),
     'Definition Proper_mul := ScalarMult.Proper_scalarmult_ref' is not enough. *)
  Instance Proper_mul c :
    Proper (W.eq ==> W.eq) (W.mul c).
  Proof.
    apply @ScalarMult.Proper_scalarmult_ref.
    {
      apply Hierarchy.commutative_group_group.
      exact _.
    }
    reflexivity.
  Qed.
End W.

Existing Instance W.commutative_group.
Existing Instance W.Proper_mul.

Local Notation "xs $@ a" := (map.of_list_word_at a xs)
  (at level 10, format "xs $@ a").

Local Notation bytearray := (Array.array ptsto (word.of_Z 1)).

Notation sizeof_point := 96%nat.

From Crypto.Bedrock.P256 Require Import Jacobian Recode.

Definition p256_mul_by_pow2 :=
  func! (p_P, n) {
    while n {
      stackalloc sizeof_point as p_dP; (* Temporary point dP. *)
      p256_point_double(p_dP, p_P); (* dP = [2]P *)
      br_memcpy(p_P, p_dP, $sizeof_point); (* P = dP *)
      n = n - $1;
      $(cmd.unset "p_dP")
    }
  }.

(*Definition p256_get_signed_mult :=
  func! (p_out, p_P, k) { ... }.*)

(*Definition p256_set_zero :=
  func! (p_P) { (* set to [0,1,0] *) }.*)

Notation w := Recode.w.
Notation num_bits := 256%nat.
(* TODO: Infer this from p256 group order and w. *)
(* Compute (Z.log2 p256_group_order) / w. *)
Notation num_limbs := 52%nat.

(* Align helpers. *)
Definition align_mask x mask := Z.land (x + mask) (Z.lnot mask).
Definition align x a := align_mask x (a - 1).

(* TODO: use ($wsize.wsize - $8) instead of $56. *)
Definition load1_sext :=
  func! (p_b) ~> r {
    r = (load1(p_b) << $56) .>> $56
  }.

(*
1) what if [*;0;0;0;0;0;0;0], then the head is shifted through as 0,
then addition adds two zero inputs, which is not constant time
   -> need an addition which handles two zero inputs in constant time
   but we can also assume that it never has to do any other kind of doubling
2) [k]P could also be zero, but the first addend will be nonzero
*)
Definition p256_point_mul_signed :=
  func! (p_out, p_sscalar, p_P) {
    p256_set_zero(p_out); (* Set result point to identity. *)

    i = $num_limbs;
    while i {
      i = i - $1;

      stackalloc sizeof_point as p_kP; (* Temporary point kP = [k]P. *)
      stackalloc sizeof_point as p_tmp; (* Temporary point for addition. *)

      p256_mul_by_pow2(p_out, $w); (* OUT = [2^w]OUT *)
      unpack! k = load1_sext(p_sscalar + i); (* k is a recoded signed scalar limb. *)
      p256_get_signed_mult(p_kP, p_P, k); (* kP = [k]P *)
      p256_point_add_vartime_if_doubling(p_tmp, p_out, p_kP); (* TMP = OUT + kP *)
      br_memcpy(p_out, p_tmp, $sizeof_point); (* OUT = TMP *)

      $(cmd.unset "k");
      $(cmd.unset "p_kP");
      $(cmd.unset "p_tmp")
    }
  }.

Definition p256_point_mul :=
  func! (p_out, p_scalar, p_P) {
    stackalloc (align num_limbs 8) as p_sscalar; (* Space for limbs of unpacked and recoded scalar. *)
    words_unpack(p_sscalar, p_scalar, $num_bits); (* Unpack scalar into unsigned w-bit limbs. *)
    recode_wrap(p_sscalar, $num_limbs); (* Recode scalar into signed w-bit limbs. *)
    p256_point_mul_signed(p_out, p_sscalar, p_P) (* Multiply using signed multiplication. *)
  }.

Local Instance spec_of_load1_sext : spec_of "load1_sext" :=
  fnspec! "load1_sext" p_b / b R ~> r,
  { requires t m :=
    m =* ptsto p_b b * R;
    ensures T M :=
    M =* ptsto p_b b * R /\ T = t /\
    word.signed r = byte.signed b
  }.

(* Alternative spec for p256_point_add_vartime_if_doubling that disallows equal inputs if either is nonzero. *)
Local Instance spec_of_p256_point_add_vartime_if_doubling_alt : spec_of "p256_point_add_vartime_if_doubling" :=
  fnspec! "p256_point_add_vartime_if_doubling" p_out p_P p_Q / out (P Q : point) R,
  { requires t m :=
      m =* out$@p_out * P$@p_P * Q$@p_Q * R /\
      length out = length P /\
      (* In our algorithm, at the start, either we keep adding zero to zero OR
         we add two distinct points. *)
      (~ (W.eq (Jacobian.to_affine P) W.zero /\ W.eq (Jacobian.to_affine Q) W.zero) ->
        ~ W.eq (Jacobian.to_affine P) (Jacobian.to_affine Q));
    ensures T M := T = t /\ exists (out : point),
      M =* out$@p_out * P$@p_P * Q$@p_Q * R /\
      Jacobian.eq out (Jacobian.add P Q)
  }.

Local Instance spec_of_p256_set_zero : spec_of "p256_set_zero" :=
  fnspec! "p256_set_zero" p_P / P R,
  { requires t m :=
    m =* P$@p_P * R;
    ensures T M := exists (Q : point),
    M =* Q$@p_P * R /\
    W.eq (Jacobian.to_affine Q) (W.zero) /\
    T = t
  }.

Local Instance spec_of_p256_mul_by_pow2 : spec_of "p256_mul_by_pow2" :=
  fnspec! "p256_mul_by_pow2" p_P n / (P : point) R,
  { requires t m :=
    m =* P$@p_P * R;
    ensures T M := exists (Q : point),
    M =* Q$@p_P * R /\
    W.eq (Jacobian.to_affine Q) (W.mul (2^n) (Jacobian.to_affine P)) /\
    T = t
  }.

Local Instance spec_of_p256_get_signed_mult : spec_of "p256_get_signed_mult" :=
  fnspec! "p256_get_signed_mult" (p_out p_P k : word) / out (P : point) R,
  { requires t m :=
    m =* out$@p_out * P$@p_P * R /\ length out = length P;
    (* TODO: range of k small *)
    ensures T M := exists (Q : point),
    M =* Q$@p_out * P$@p_P * R /\
    W.eq (Jacobian.to_affine Q) (W.mul (word.signed k) (Jacobian.to_affine P)) /\
    T = t
  }.

(* N = group order == |{g \in G generated by P} = {k*P for k = 0,...,N}|
if N/2 < k < N:
    Q = [-1]P
    [k]P = [k][-1][-1]P = [-1][k]Q = [N - k]Q *)
Local Instance spec_of_p256_point_mul_signed : spec_of "p256_point_mul_signed" :=
  fnspec! "p256_point_mul_signed" (p_out p_sscalar p_P : word) / out sscalar (P : point) R,
  { requires t m :=
    m =* out$@p_out * bytearray p_sscalar sscalar * P$@p_P * R /\
    length out = length P /\ length sscalar = num_limbs /\
    0 < positional_signed_bytes (2^w) sscalar < p256_group_order /\
    Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) sscalar;
    ensures T M := exists (Q : point) (* Q = [sscalar]P *),
      M =* Q$@p_out * bytearray p_sscalar sscalar * P$@p_P * R /\ (* ... *)
      W.eq (Jacobian.to_affine Q) (W.mul (positional_signed_bytes (2^w) sscalar) (Jacobian.to_affine P)) /\
      T = t
  }.

Local Instance spec_of_p256_point_mul : spec_of "p256_point_mul" :=
  fnspec! "p256_point_mul" (p_out p_scalar p_P : word) / out scalar (P : point) R,
  { requires t m :=
    m =* out$@p_out * bytearray p_scalar scalar * P$@p_P * R /\
    length out = length P /\
    8 * (length scalar - 1) < num_bits <= 8 * length scalar /\
    0 < Z.of_bytes scalar < p256_group_order;
    ensures T M := exists (Q : point) (* Q = [scalar]P *),
      M =* Q$@p_out * bytearray p_scalar scalar * P$@p_P * R /\ (* ... *)
      W.eq (Jacobian.to_affine Q) (W.mul (Z.of_bytes scalar) (Jacobian.to_affine P)) /\
      T = t
  }.

From coqutil Require Import Tactics.Tactics Macros.symmetry.


Import memcpy.
Lemma p256_point_add_vartime_if_doubling : program_logic_goal_for_function! p256_point_add_vartime_if_doubling.
Proof.
  cbv [spec_of_p256_point_add_vartime_if_doubling_alt].
  repeat straightline.
  straightline_call; repeat straightline. (*iszero*)
  { eexists. ecancel_assumption. }
  straightline_call; repeat straightline. (*iszero*)
  { eexists. ecancel_assumption. }
  (* stackalloc *)
  seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) H9 ltac:(lia).
  straightline_call; ssplit. (*add*)
  { ecancel_assumption. }
  { rewrite length_point; lia. }
  repeat straightline.
  straightline_call; repeat straightline (* br_declassify *).
  (* stackalloc *)
  seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) H18 ltac:(lia).
  straightline_call; ssplit. (* memset *)
  { ecancel_assumption. }
  { ZnWords.ZnWords. }
  repeat straightline.
  straightline_call; repeat straightline; ssplit (* memcxor *).
  { ecancel_assumption. }
  { rewrite ?repeat_length; trivial. }
  { rewrite H19, length_point; trivial. }
  straightline_call; repeat straightline; ssplit (* memcxor *).
  { ecancel_assumption. }
  { rewrite ?repeat_length; trivial. }
  { rewrite length_point; trivial. }
  straightline_call; repeat straightline; ssplit (* memcxor *).
  { ecancel_assumption. }
  { rewrite ?repeat_length; trivial. }
  { rewrite length_point; trivial. }

  rewrite ?word.and_xorm1_l, ?word.and_xorm1_r in *.

  subst x x0 x3.
  eexists; ssplit; repeat straightline. (* if ok *)
  { straightline_call; repeat straightline; ssplit (* memcpy *).
    { ecancel_assumption. }
    { rewrite H10, length_point; trivial. }
    { trivial. }
    { clear; ZnWords.ZnWords. }
    repeat straightline.
    (* stackdealloc *)
    progress repeat seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at) H43 ltac:(rewrite ?length_point in *; lia || ZnWords.ZnWords).
    progress repeat match type of H43 with context [Array.array ptsto _ _ (point.to_bytes ?x)] =>
    unique pose proof (length_point x) end.
    assert (Datatypes.length x6 = 96%nat) by ZnWords.ZnWords.
    repeat straightline.
    progress repeat seprewrite_in_by (@Array.array1_iff_eq_of_list_word_at) H43 ltac:(rewrite ?length_point in *; lia || ZnWords.ZnWords).

    rewrite <-word.unsigned_of_Z_0, !word.unsigned_inj_iff in H28 by exact _.
    rewrite !word.lor_0_iff, !word.broadcast_0_iff in H28.
    destruct (iszero P) eqn:HP, (iszero Q) eqn:HQ in *; try intuition discriminate;
      repeat match goal with
             | H : _ = _ -> _ |- _ => specialize (H eq_refl)
             | H : ?x = ?y -> _ |- _ => assert (x = y -> False) as _ by inversion 1; clear H
             end;
      subst x4; subst x5; subst x6;
      rewrite ?Byte.map_xor_0_l in * by (rewrite ?length_point; ZnWords.ZnWords).
    { (* 0 + 0 *)
      eexists (exist _ (0,0,0)%F I); split.
      { use_sep_assumption; cancel. reflexivity. }
      apply Decidable.dec_bool, Jacobian.iszero_iff in HP.
      apply Decidable.dec_bool, Jacobian.iszero_iff in HQ.
      rewrite Jacobian.eq_iff, Jacobian.to_affine_add, HP, HQ.
      exact I. }
    { (* 0 + Q *)
      eexists; split. { ecancel_assumption. }
      apply Decidable.dec_bool, Jacobian.iszero_iff in HP.
      rewrite Jacobian.eq_iff, Jacobian.to_affine_add, HP.
      symmetry.
      eapply Hierarchy.left_identity. }
    { (* P + 0 *)
      eexists; split. { ecancel_assumption. }
      apply Decidable.dec_bool, Jacobian.iszero_iff in HQ.
      rewrite Jacobian.eq_iff, Jacobian.to_affine_add, HQ.
      symmetry.
      unshelve eapply Hierarchy.right_identity. }
    { (* nz + nz' *)
      rewrite <-Bool.not_true_iff_false in HP, HQ.
      (* Decidable.dec_iff? *)
      cbv [iszero] in HP, HQ; case Decidable.dec in HP; case Decidable.dec in HQ; try congruence.
      destruct (H20 ltac:(trivial) ltac:(trivial)) as [HE|]; [|intuition fail].
      case HE as [_ (?&HE)].
      repeat straightline_cleanup.
      eexists; split; [ecancel_assumption|].
      rewrite Jacobian.eq_iff, Jacobian.to_affine_add, Jacobian.to_affine_add_inequal_nz_nz; trivial; reflexivity. } }
  {
    (* TODO: show that !ok cannot happen. *)
    destruct H11.
    { admit. }
    { admit. }
  }
Admitted.

Lemma load1_sext_ok : program_logic_goal_for_function! load1_sext.
Proof.
  repeat (straightline || apply WeakestPreconditionProperties.dexpr_expr).
  ssplit; try ecancel_assumption; trivial.
  subst r.
  rewrite word.signed_srs_nowrap by ZnWords.
  rewrite word.signed_eq_swrap_unsigned.
  rewrite word.unsigned_slu_shamtZ by lia.
  rewrite ?word.unsigned_of_Z_nowrap; try (pose proof byte.unsigned_range b; lia).
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  cbv [byte.signed word.wrap byte.swrap word.swrap].
  PreOmega.Z.div_mod_to_equations.
  lia.
Qed.

Lemma p256_mul_by_pow2_ok : program_logic_goal_for_function! p256_mul_by_pow2.
Proof.
  repeat straightline.
  refine ((Loops.tailrec
    (* types of ghost variables*) (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                  HList.polymorphic_list.nil))
    (* program variables *) (["p_P";"n"] : list String.string))
    (fun v (P : point) R t m p_P n => PrimitivePair.pair.mk (* precondition *)
      (v = word.unsigned n /\
      m =* P$@p_P * R)
    (fun                 T M P_P N => (* postcondition *)
      exists (Q : point),
      M =* Q$@p_P * R /\
      p_P = P_P /\
      W.eq (Jacobian.to_affine Q) (W.mul (2^n) (Jacobian.to_affine P)) /\
      T = t))
    (fun n m => 0 <= n < m) (* well_founded relation *)
    _ _ _ _ _ _ _);
  Loops.loop_simpl.

  { repeat straightline. }
  { apply Z.lt_wf. }
  {
    repeat straightline.
    ecancel_assumption.
  }

  {
    repeat straightline.

    (* Induction case. *)
    {
      straightline_call. (* call p256_point_double *)
      {
        split.
        {
          seprewrite_in Array.array1_iff_eq_of_list_word_at H3; try lia.
          ecancel_assumption.
        }
        { rewrite length_point; trivial. }
      }
      repeat straightline.
      straightline_call. (* call br_memcpy *)
      {
        ssplit; try ecancel_assumption.
        { rewrite length_point; trivial. }
        { rewrite length_point; trivial. }
        ZnWords.
      }
      repeat straightline.

      (* Deallocate stack. *)
      seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at _ _ _ _ _ _ a) H11 ltac:(rewrite length_point; lia).
      assert (length (to_bytes (Jacobian.double_minus_3 eq_refl x)) = 96%nat) by (rewrite length_point; trivial).

      repeat straightline.

      eexists _, _, (word.unsigned n).
      repeat straightline.
      { ecancel_assumption. }

      split.
      { ZnWords. }

      repeat straightline.
      eexists _.
      ssplit; try ecancel_assumption; trivial.
      rewrite H14.
      subst n.
      rewrite word.unsigned_sub, word.unsigned_of_Z_nowrap by lia.
      cbv [word.wrap].
      rewrite Z.mod_small by ZnWords.

      rewrite <-Jacobian.double_minus_3_eq_double.
      rewrite Jacobian.to_affine_double.
      rewrite <-ScalarMult.scalarmult_2_l.
      rewrite ScalarMult.scalarmult_assoc.

      assert (2 * 2 ^ (word.unsigned x2 - 1) = 2 ^ word.unsigned x2) as ->.
      {
        rewrite <-Z.pow_succ_r by ZnWords.
        f_equal.
        lia.
      }
      reflexivity.
    }

    (* Base case. *)
    eexists _.
    ssplit; try ecancel_assumption; trivial.
    rewrite H2.
    rewrite Z.pow_0_r.
    rewrite ScalarMult.scalarmult_1_l.
    reflexivity.
  }

  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; trivial.
Qed.

Lemma positional_signed_bytes_cons B (h : byte) (t : list byte) :
  positional_signed_bytes B (h :: t) = byte.signed h + B*(positional_signed_bytes B t).
Proof. constructor. Qed.

Lemma positional_signed_bytes_app B (l l' : list byte) :
  positional_signed_bytes B (l ++ l') = positional_signed_bytes B l + B^(length l) * positional_signed_bytes B l'.
Proof.
  induction l as [| ? ? H].
  {
    rewrite app_nil_l, length_nil.
    cbn [positional_signed_bytes positional map fold_right].
    lia.
  }
  rewrite <-app_comm_cons, length_cons.
  rewrite ?positional_signed_bytes_cons.
  rewrite H.
  rewrite Znat.Nat2Z.inj_succ, Z.pow_succ_r by lia.
  lia.
Qed.

Lemma bytearray_firstn_nth_skipn l (i : word) start d :
  ((Z.to_nat (word.unsigned i)) < length l)%nat ->
    (Lift1Prop.iff1 ((ptsto (word.add start i) (nth (Z.to_nat (word.unsigned i)) l d)) *
                    (bytearray start (List.firstn (Z.to_nat (word.unsigned i)) l)) *
                    (bytearray (word.add (word.add start (word.of_Z (Z.of_nat (length (ListDef.firstn (Z.to_nat (word.unsigned i)) l))))) (word.of_Z 1)) (List.skipn (S (Z.to_nat (word.unsigned i))) l)))
         (bytearray start l))%sep.
Proof.
  intro Hlen.
  remember (bytearray start l) eqn:H.
  rewrite <-(firstn_nth_skipn _ (Z.to_nat (word.unsigned i)) l d Hlen) in H.
  subst P.
  rewrite ?Array.bytearray_append.
  cancel.
  rewrite length_firstn.
  assert ((Nat.min (Z.to_nat (word.unsigned i)) (length l)) = (Z.to_nat (word.unsigned i))) as -> by lia.
  cbv [bytearray seps length].
  assert ((word.of_Z (Z.of_nat (Z.to_nat (word.unsigned i)))) = i) as -> by ZnWords.
  assert ((word.of_Z (Z.of_nat 1)) = (word.of_Z 1)) as -> by ZnWords.
  cancel.
Qed.

Lemma positional_skipn_nth (i : nat) B l d :
  (i > 0) -> (i - 1 < length l)%nat ->
    positional B (skipn (i - 1) l) = positional B (skipn i l) * B + (nth (i - 1) l d).
Proof.
  intros.
  remember (positional B (skipn i l) * B + nth (i - 1) l d).
  rewrite <-(firstn_nth_skipn _ (i - 1) l d H0).
  rewrite skipn_app.
  rewrite skipn_all2; try (rewrite length_firstn; lia).
  rewrite app_nil_l, length_firstn.
  replace (i - 1 - Nat.min (i - 1) (length l))%nat with 0%nat by lia.
  rewrite skipn_0.
  replace (S (i - 1))%nat with i%nat by lia.
  change ([nth (i - 1) l d] ++ skipn i l) with ((nth (i - 1) l d) :: skipn i l).
  rewrite positional_cons.
  lia.
Qed.

Lemma positional_app B a b :
  positional B (a ++ b) = positional B a + B ^ length a * positional B b.
Proof.
  induction a.
  {
    rewrite app_nil_l.
    rewrite length_nil.
    cbn [positional fold_right].
    lia.
  }
  {
    rewrite <-app_comm_cons.
    rewrite !positional_cons.
    rewrite IHa.
    rewrite length_cons.
    rewrite Z.mul_add_distr_l.
    rewrite Z.mul_assoc.
    rewrite Pow.Z.pow_mul_base by lia.
    lia.
  }
Qed.

Lemma positional_firstn_skipn (i : nat) B l :
  (i <= length l)%nat ->
  positional B l = positional B (skipn i l) * B ^ i + positional B (firstn i l).
Proof.
  intros.
  remember (positional B (skipn i l) * B ^ i + positional B (firstn i l)).
  rewrite <-(firstn_skipn i l).
  rewrite positional_app.
  rewrite length_firstn.
  replace (Nat.min i (length l)) with i by lia.
  lia.
Qed.

Lemma positional_firstn_nth_skipn_prev (i : nat) B l d :
  (0 < i) -> (i - 1 < length l)%nat ->
  positional B l =
  positional B (skipn i l) * B ^ i + (nth (i - 1) l d) * B ^ (i - 1) + positional B (firstn (i - 1) l).
Proof.
  intros.
  remember (positional B (skipn i l) * B ^ i + (nth (i - 1) l d) * B ^ (i - 1) + positional B (firstn (i - 1) l)).
  rewrite <-(firstn_nth_skipn _ (i - 1) l d H0).
  rewrite ?positional_app.
  rewrite length_firstn, length_cons, length_nil.
  replace (Nat.min (i - 1) (length l)) with (i - 1)%nat by lia.
  cbn [positional fold_right].
  rewrite Z.pow_1_r, Z.mul_0_r, Z.add_0_r.
  rewrite Z.mul_add_distr_l, Z.mul_assoc, Z.add_assoc.
  rewrite <-(Z.mul_comm B).
  rewrite <-Z.pow_succ_r by lia.
  assert (S (i - 1) = i) as -> by lia.
  assert (Z.succ (Z.of_nat (i - 1)) = Z.of_nat i) as -> by lia.
  assert (Z.of_nat (i - 1) = Z.of_nat i - 1) as -> by lia.
  lia.
Qed.

(* TODO: remove once available in coqutil. *)
Lemma Forall_skipn {A} (P: A -> Prop): forall (n: nat) (l: list A),
    Forall P l -> Forall P (skipn n l).
Proof.
  induction n; intros.
  - simpl. assumption.
  - destruct l. 1: assumption. inversion H. subst. simpl. apply IHn; eauto.
Qed.

Ltac hyp_containing a := match goal with H : context[a] |- _ => H end.

Ltac subst_to_affine :=
repeat match goal with |- context [Jacobian.to_affine ?P] =>
           match goal with H : context [Jacobian.to_affine P] |- _ =>
             rewrite H
           end
        end.

Lemma p256_point_mul_signed_ok :
  (* Use the alternative spec for p256_point_add_vartime_if_doubling. *)
  let _ := spec_of_p256_point_add_vartime_if_doubling_alt in
  program_logic_goal_for_function! p256_point_mul_signed.
Proof.
  repeat straightline.

  repeat straightline.
  straightline_call. (* call p256_set_zero *)
  { ecancel_assumption. }

  repeat straightline.

  refine ((Loops.tailrec
    (* types of ghost variables*) (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                  HList.polymorphic_list.nil))
    (* program variables *) (["p_out";"p_sscalar";"p_P";"i"] : list String.string))
    (fun v (curr_out : point) R t m p_out p_sscalar p_P i => PrimitivePair.pair.mk (* precondition *)
      (
        let processed_limbs := skipn (Z.to_nat v) sscalar in
        let processed_scalar := positional_signed_bytes (2^w) processed_limbs in
        W.eq (Jacobian.to_affine curr_out) (W.mul processed_scalar (Jacobian.to_affine P)) /\
        v = word.unsigned i /\
        0 <= v <= num_limbs /\
      m =* curr_out$@p_out * bytearray p_sscalar sscalar * P$@p_P * R /\
      Z.of_nat (length sscalar) = num_limbs)
    (fun                                       T M P_OUT P_SSCALAR P_P I => (* postcondition *)
      exists (Q : point),
      M =* Q$@p_out * bytearray p_sscalar sscalar * P$@p_P * R /\
      p_out = P_OUT /\ p_P = P_P /\
      W.eq (Jacobian.to_affine Q)
           (W.add
            (W.mul (2^(w*i)) (Jacobian.to_affine curr_out))
            (W.mul (positional_signed_bytes (2^w) (firstn (Z.to_nat v) sscalar)) (Jacobian.to_affine P)))
      /\
      T = t))
    (fun n m => 0 <= n < m) (* well_founded relation *)
    _ _ _ _ _ _ _);
  Loops.loop_simpl.

  { repeat straightline. }
  { eapply Z.lt_wf. }
  {
    repeat straightline.
    ssplit; try ecancel_assumption; trivial.
    {
      subst i.
      assert (Z.to_nat (word.unsigned (word.of_Z 52)) = 52%nat) as -> by ZnWords.
      rewrite List.skipn_all by ZnWords.
      cbn [positional_signed_bytes positional fold_right map].
      rewrite ScalarMult.scalarmult_0_l.
      assumption.
    }
    { ZnWords. }
    { ZnWords. }
    { lia. }
  }

  {
    intros ?v ?curr_out ?R ?t ?m ?p_out ?p_sscalar ?p_P ?i.

    repeat straightline.

    {
      rename a into p_kP.

      straightline_call. (* call p256_mul_by_pow2 *)
      { ecancel_assumption. }

      repeat straightline.

      assert (Z.to_nat (word.unsigned i) < length sscalar)%nat as i_bounded by ZnWords.
      pose proof (symmetry! firstn_nth_skipn _ (Z.to_nat (word.unsigned i)) sscalar x00 i_bounded) as sscalar_parts.
      rewrite sscalar_parts in H28.
      rewrite app_assoc, <-assoc_app_cons in H28.

      seprewrite_in Array.bytearray_append H28.
      cbn [bytearray] in H28.

      rename x0 into shifted_out.

      straightline_call. (* call load1_sext *)
      {
        assert (i = word.of_Z (Z.of_nat (length (ListDef.firstn (Z.to_nat (word.unsigned i)) sscalar)))) as -> by listZnWords.
        ecancel_assumption.
      }

      repeat straightline.

      rename x0 into k.

      straightline_call. (* call p256_get_signed_mult *)
      {
        ssplit.
        {
          seprewrite_in_by (Array.array1_iff_eq_of_list_word_at p_kP) H30 ltac:(lia).
          ecancel_assumption.
        }
        { rewrite length_point; trivial. }
      }

      repeat straightline.

      rename x0 into kP.

      straightline_call. (* call p256_point_add_neq *)

      {
        seprewrite_in_by (Array.array1_iff_eq_of_list_word_at a1) H31 ltac:(lia).
        ssplit; try ecancel_assumption; trivial.

        intros.
        subst_to_affine.
        rewrite ScalarMult.scalarmult_assoc.
        rewrite Z.mul_comm, word.unsigned_of_Z_nowrap by lia.
        rewrite p256_mul_mod_n.

        unfold positional_signed_bytes in *.
        rewrite <- skipn_map in *.
        rewrite H32.
        rewrite <- map_nth in *.
        (* TODO these could probably be cleaned up earlier in the proof. *)
        replace ((Z.to_nat (word.unsigned (word.sub i0 (word.of_Z 1))))) with ((Z.to_nat v - 1))%nat in * by ZnWords.
        replace (byte.signed "000") with 0 in* by (cbn; ZnWords).
        apply (fixed_window_no_doubling') with (xs := (firstn (Z.to_nat v - 1) (map byte.signed sscalar))); unfold p256_group_order in *.
        all: try ZnWords.
        { apply Forall_firstn. rewrite Forall_map. assumption. }
        { apply Forall_skipn. rewrite Forall_map. assumption. }
        { apply Forall_nth. { rewrite Forall_map. assumption. } rewrite map_length. lia. }
        {
          intros [?N1 ?N2].
          apply H27; split.
          {
            subst_to_affine. unfold positional.
            rewrite N2.
            rewrite ScalarMult.scalarmult_0_l, ScalarMult.scalarmult_zero_r.
            reflexivity. }
          { subst_to_affine.
            rewrite H32, N1.
            rewrite ScalarMult.scalarmult_0_l.
            reflexivity.
          }
        }
        { rewrite ListUtil.app_cons_app_app. rewrite <- app_assoc.
          replace ( skipn (Z.to_nat v) (map byte.signed sscalar)) with (skipn (S (Z.to_nat v - 1)) (map byte.signed sscalar)).
          2: { f_equal. lia. }
          rewrite firstn_nth_skipn.
          { unfold positional in *. lia. }
          { rewrite map_length. lia. }
        }
      }

      repeat straightline.

      rename x0 into curr_out_new.

      straightline_call. (* call br_memcpy *)

      {
        ssplit; try ecancel_assumption; trivial.
        ZnWords.
      }

      repeat straightline.

      (* Deallocate stack. *)
      seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at _ _ _ _ _ _ p_kP) H37 ltac:(rewrite length_point; lia).
      assert (length (to_bytes kP) = 96%nat) by (rewrite length_point; trivial).

      (* Deallocate stack. *)
      seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at _ _ _ _ _ _ a1) H37 ltac:(rewrite length_point; lia).
      assert (length (to_bytes curr_out_new) = 96%nat) by (rewrite length_point; trivial).

      (* TODO: repeat straighline hangs here so we do it in steps. *)
      straightline.
      straightline.

      eexists _, _, _, _.
      split.
      { repeat straightline. }

      repeat straightline.

      eexists _, _, _.
      repeat straightline.

      {
        cbv [i] in H37.
        seprewrite_in_by bytearray_firstn_nth_skipn H37 ltac:(ZnWords).
        ssplit; try ecancel_assumption; trivial.

        {
          rewrite H36.
          rewrite Jacobian.to_affine_add.
          subst_to_affine.
          rewrite H32.
          subst i v.

          rewrite ScalarMult.scalarmult_assoc.
          rewrite <-ScalarMult.scalarmult_add_l.

          rewrite word.unsigned_of_Z_nowrap by lia.

          cbv [positional_signed_bytes].
          rewrite <-?skipn_map.

          assert (
            Z.to_nat (word.unsigned (word.sub i0 (word.of_Z 1))) =
            (Z.to_nat (word.unsigned i0) - 1)%nat
          ) as -> by ZnWords.

          rewrite (positional_skipn_nth _ _ _ (byte.signed x00)).
          {
            rewrite map_nth.
            reflexivity.
          }
          { ZnWords. }
          {
            rewrite length_map.
            ZnWords.
          }
        }
        { ZnWords. }
        { ZnWords. }
      }

      split.
      {
        (* loop test. *)
        ZnWords.
      }

      repeat straightline.

      eexists _.
      ssplit; try ecancel_assumption; trivial.

      rewrite H43.
      rewrite H36.

      rewrite Jacobian.to_affine_add.

      subst_to_affine.

      rewrite word.unsigned_of_Z_nowrap by lia.
      rewrite H32.
      subst v i.

      cbv [positional_signed_bytes].
      rewrite <-?skipn_map, <-?firstn_map.

      assert (
        Z.to_nat (word.unsigned (word.sub i0 (word.of_Z 1))) =
        (Z.to_nat (word.unsigned i0) - 1)%nat
      ) as -> by ZnWords.

      repeat rewrite ?ScalarMult.scalarmult_assoc, <-?ScalarMult.scalarmult_add_l.

      Morphisms.f_equiv.

      rewrite (Z.pow_mul_r 2 5 (word.unsigned i0)) by lia.
      assert ((2 ^ 5) ^ word.unsigned i0 = (2 ^ 5) ^ Z.of_nat (Z.to_nat i0)) as -> by (f_equal; ZnWords).
      rewrite <-positional_firstn_skipn by listZnWords.

      rewrite <-map_nth.
      rewrite (Z.pow_mul_r 2 5 (word.unsigned (word.sub i0 (word.of_Z 1)))) by ZnWords.
      assert ((2 ^ 5) ^ word.unsigned (word.sub i0 (word.of_Z 1)) = (2 ^ 5) ^ Z.of_nat (Z.to_nat i0 - 1)) as -> by (f_equal; ZnWords).

      rewrite Z.mul_add_distr_r.

      rewrite <-Z.mul_assoc.
      assert (
        2 ^ 5 * (2 ^ 5) ^ Z.of_nat (Z.to_nat (word.unsigned i0) - 1) =
        (2 ^ 5) ^ Z.of_nat (Z.to_nat (word.unsigned i0))
      ) as ->.
      {
        rewrite Pow.Z.pow_mul_base by ZnWords.
        f_equal.
        ZnWords.
      }
      assert (Z.of_nat (Z.to_nat (word.unsigned i0) - 1) = Z.of_nat (Z.to_nat (word.unsigned i0)) - 1) as -> by lia.
      rewrite <-positional_firstn_nth_skipn_prev; (rewrite ?length_map; lia).
    }

    (* Base case. *)
    eexists _.
    ssplit; try ecancel_assumption; trivial.

    subst_to_affine.

    cbv [v].
    rewrite H14.
    rewrite Znat.Z2Nat.inj_0, firstn_0.
    cbn [positional_signed_bytes positional List.map fold_right].

    rewrite ScalarMult.scalarmult_0_l.
    rewrite Hierarchy.right_identity.

    rewrite Z.mul_0_r, Z.pow_0_r.
    rewrite ScalarMult.scalarmult_1_l.
    reflexivity.
  }

  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; trivial.

  rewrite H16.
  rewrite H13.

  rewrite ScalarMult.scalarmult_zero_r.
  rewrite Hierarchy.left_identity.

  cbv [i].
  rewrite word.unsigned_of_Z_nowrap by lia.

  assert (Z.to_nat 52 = length sscalar) as -> by lia.
  rewrite firstn_all.

  reflexivity.
Admitted.

Lemma p256_point_mul_ok : program_logic_goal_for_function! p256_point_mul.
Proof.
  repeat straightline.

  (* Split stack into space for sscalar and padding. *)
  rewrite <-(firstn_skipn 52 stack) in H2.
  set (sscalar := ListDef.firstn 52 stack) in H2.
  set (padding := ListDef.skipn 52 stack) in H2.
  seprewrite_in Array.bytearray_append H2.
  assert (length sscalar = 52%nat).
  {
    unfold sscalar.
    rewrite length_firstn.
    lia.
  }
  rewrite H12 in H2.
  set (word.add a (word.of_Z (Z.of_nat 52))) in H2.

  straightline_call. (* call words_unpack *)
  {
    (* Solve words_unpack assumptions. *)
    ssplit; try ecancel_assumption; try ZnWords.
    rewrite word.unsigned_of_Z_nowrap by lia.
    cbv [p256_group_order] in *.
    lia.
  }

  repeat straightline.
  straightline_call. (* call recode_wrap *)
  {
    (* Solve recode_wrap assumptions. *)
    ssplit; try ecancel_assumption; trivial.
    { ZnWords. }
    {
      rewrite <-H18.
      change (5 * word.unsigned (word.of_Z 52)) with (260).
      cbv [p256_group_order] in *.
      lia.
    }
    { Decidable.vm_decide. }
  }

  repeat straightline.
  straightline_call. (* call p256_point_mul_signed *)
  { ssplit; try ecancel_assumption; trivial; try ZnWords. }

  repeat straightline.

  (* Restore stack by combining scalar and padding. *)
  seprewrite_in_by (Array.bytearray_index_merge x0 padding) H22 ZnWords.
  assert (length (x0 ++ padding) = 56%nat).
  {
    rewrite length_app.
    cbv [padding].
    rewrite length_skipn.
    ZnWords.
  }

  repeat straightline.

  eexists _.
  ssplit; try ecancel_assumption; trivial.

  rewrite H25, H23, <-H18.
  reflexivity.
Qed.
