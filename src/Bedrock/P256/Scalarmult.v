Require Import String coqutil.Datatypes.List Coq.Lists.List.
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
memcpy
.

Require Import Coq.Classes.Morphisms.

Import ProgramLogic.Coercions.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.
Local Open Scope list_scope.

Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.AffineProofs.

Module W.
  Import Crypto.Bedrock.P256.Specs(a, b).

  Definition a := a.
  Definition b := b.

  Local Notation "4" := (1+1+1+1)%F.
  Local Notation "27" := (4*4 + 4+4 +1+1+1)%F.
  Lemma discriminant_nonzero : (4*a*a*a + 27*b*b <> 0)%F.
  Proof.
    Decidable.vm_decide.
  Qed.

  Definition mul := ScalarMult.scalarmult_ref
    (G := W.point
      (a := a)
      (b := b)
    )
    (add := W.add)
    (zero := W.zero)
    (opp := W.opp).

  Definition commutative_group := W.commutative_group _
    (a := a)
    (b := b)
    (discriminant_nonzero := discriminant_nonzero).

  (* HACK: Rewrite W.eq * W.zero hangs with Proper (Logic.eq ==> W.eq ==> W.eq),
     'Definition Proper_mul := ScalarMult.Proper_scalarmult_ref' is not enough. *)
  Instance Proper_mul c :
    Proper (W.eq ==> W.eq) (mul c).
  Proof.
    apply @ScalarMult.Proper_scalarmult_ref.
    {
      apply Hierarchy.commutative_group_group.
      exact commutative_group.
    }
    reflexivity.
  Qed.
End W.

Existing Instance W.commutative_group.
Existing Instance W.Proper_mul.

Local Notation "xs $@ a" := (map.of_list_word_at a xs)
  (at level 10, format "xs $@ a").

Local Notation bytearray := (Array.array ptsto (word.of_Z 1)).

Definition sizeof_point := 96%nat.

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

Definition w := Recode.w.
Definition num_bits := 256%nat.
Definition p256_group_order := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551.
(* TODO: Infer this from p256 group order and w. *)
(* Compute (Z.log2 p256_group_order) / w. *)
Definition num_limbs := 52%nat.

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

      stackalloc sizeof_point as p_kP; (* Temporary point kP. *)

      p256_mul_by_pow2(p_out, $w); (* OUT = [2^w]OUT *)
      unpack! k = load1_sext(p_sscalar + i); (* k is a recoded signed scalar limb. *)
      p256_get_signed_mult(p_kP, p_P, k); (* kP = [k]P *)
      p256_point_add_vartime_if_doubling(p_out, p_out, p_kP); (* OUT = OUT + kP *)

      $(cmd.unset "k");
      $(cmd.unset "p_kP")
    }
  }.

Definition p256_point_mul :=
  func! (p_out, p_scalar, p_P) {
    stackalloc (align num_limbs 8) as p_sscalar; (* Space for limbs of unpacked and recoded scalar. *)
    words_unpack(p_sscalar, p_scalar, $(256)); (* Unpack scalar into unsigned w-bit limbs. *)
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

(* TODO: prove in-place spec/lemma of p256_point_add_vartime_if_doubling *)
Definition spec_of_p256_point_add_vartime_if_doubling_inplace : spec_of "p256_point_add_vartime_if_doubling" :=
  fnspec! "p256_point_add_vartime_if_doubling" p_out p_P p_Q / (P Q : point) R,
  { requires t m := m =* P$@p_P * Q$@p_Q * R /\ p_out = p_P /\
    (* In our algorithm, at the start, either we keep adding zero to zero OR
       we add two distinct points. *)
     (~ (W.eq (Jacobian.to_affine P) W.zero /\ W.eq (Jacobian.to_affine Q) W.zero) ->
     ~ W.eq (Jacobian.to_affine P) (Jacobian.to_affine Q));
    ensures t' m := t' = t /\ exists (out : point),
      m =* out$@p_out * Q$@p_Q * R /\ length out = length P /\
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
    2 * positional_signed_bytes (2^w) sscalar < p256_group_order /\
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
    2 * Z.of_bytes scalar < p256_group_order;
    ensures T M := exists (Q : point) (* Q = [scalar]P *),
      M =* Q$@p_out * bytearray p_scalar scalar * P$@p_P * R /\ (* ... *)
      W.eq (Jacobian.to_affine Q) (W.mul (Z.of_bytes scalar) (Jacobian.to_affine P)) /\
      T = t
  }.

From coqutil Require Import Tactics.Tactics Macros.symmetry.

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

Lemma group_isom (a b : Z) (P : point) :
  W.eq (W.mul a (Jacobian.to_affine P)) (W.mul b (Jacobian.to_affine P)) <->
  a mod p256_group_order = b mod p256_group_order.
Proof.
Admitted.

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

Lemma positional_dist_p256 (B := 2^w) h t
  (l := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551) :
  let words := cons h t in
    Forall (fun b => (-2^w + 2 <= 2*b <= 2^w)) words ->
    0 < Z.abs (2 * B * positional B words) < 2^(w*num_limbs) ->
    h mod l <> B*(positional B t) mod l.
    (* or both sides zero if scalar = 0 *)
Proof.
  intros.
  rewrite Z.cong_iff_0.
  rewrite Z.mod_divide by lia.
  intros [x].
  inversion H; subst.
  cbv [words] in H0.
  rewrite positional_cons in H0.
  cbv [w Recode.w num_limbs] in *.
  lia.
Qed.

Lemma p256_point_mul_signed_ok :
  let _ := spec_of_p256_point_add_vartime_if_doubling_inplace in
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
        0 < v <= num_limbs /\
      m =* curr_out$@p_out * bytearray p_sscalar sscalar * P$@p_P * R /\
      Z.of_nat (length sscalar) = num_limbs
      (* 2 * positional_signed_bytes (2^w) sscalar < p256_group_order *)
      (* let j := num_limbs - i in *)
      (*2^w * Z.abs (processed_scalar) < (*2*2^(w*j)*) p256_group_order /\*)
      (*Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) sscalar*) )
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
      cbv [num_limbs] in *.
      subst i.
      assert (Z.to_nat (word.unsigned (word.of_Z 52)) = 52%nat) as -> by ZnWords.
      rewrite <-H6.
      rewrite skipn_all.
      cbn [positional_signed_bytes positional fold_right map].
      rewrite H11.
      rewrite ScalarMult.scalarmult_0_l.
      reflexivity.
    }
    { cbv [num_limbs]. ZnWords. }
    { cbv [num_limbs]. ZnWords. }
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
      rewrite sscalar_parts in H22.
      rewrite app_assoc, <-assoc_app_cons in H22.

      seprewrite_in Array.bytearray_append H22.
      cbn [bytearray] in H22.

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
          seprewrite_in_by (Array.array1_iff_eq_of_list_word_at p_kP) H24 ltac:(lia).
          ecancel_assumption.
        }
        { rewrite length_point; trivial. }
      }

      repeat straightline.

      rename x0 into kP.

      straightline_call. (* call p256_point_add_vartime_if_doubling *)

      {
        ssplit; try ecancel_assumption; trivial.
        intros.
        rewrite H23, H27, H9.
        rewrite ScalarMult.scalarmult_assoc.
        rewrite Z.mul_comm, word.unsigned_of_Z_nowrap by lia.
        rewrite group_isom.

        apply signed_limb_ineq_shifted_postivie_num.

        {
          rewrite H26, sscalar_parts.
          subst i.
          rewrite firstn_nth_skipn.
          {
            eapply Forall_nth_default' in H8.
            admit.
          }
          ZnWords.
        }
        {
          admit. (* forall and skipn, sscalar is bound*)
        }
        {
          admit. (*should follow from h7 and h13, if the whole thing is bounded, then any suffix will be bounded*)

        }
        {
          intros [HNP HNk].
          apply H21.
          split.
          {
            rewrite H23.
            rewrite H9.
            unfold positional_signed_bytes.
            rewrite HNP.
            admit. (* zero times something is zero*)
          }
          {
            rewrite H27.
            rewrite HNk.
            admit. (* zero times something is zero*)
          }
        }
      }

      repeat straightline.

      rename x0 into curr_out_new.

      (* Deallocate stack. *)
      seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at _ _ _ _ _ _ p_kP) H29 ltac:(rewrite length_point; lia).
      assert (length (to_bytes kP) = 96%nat) by (rewrite length_point; trivial).

      (* TODO: repeat straighline hangs here so we do it in steps. *)
      straightline.

      eexists _, _, _, _.
      split.
      { repeat straightline. }

      repeat straightline.

      eexists _, _, _.
      repeat straightline.

      {
        cbv [i] in H28.
        seprewrite_in_by bytearray_firstn_nth_skipn H28 ltac:(ZnWords).
        ssplit; try ecancel_assumption; trivial.

        {
          rewrite
          rewrite positional_signed_bytes_cons.

          rewrite ScalarMult.scalarmult_add_l.
          rewrite Z.mul_comm.
          rewrite <-ScalarMult.scalarmult_assoc.

          rewrite <-H10.

          rewrite H33.

          rewrite Jacobian.to_affine_add.

          rewrite H25, H29.

          rewrite H28.

          rewrite word.unsigned_of_Z_nowrap by lia.
          cbv [w Recode.w].

          rewrite Hierarchy.commutative.
          reflexivity.
        }
        { ZnWords. }

        (*
        H17 : 2 ^ w * Z.abs (positional_signed_bytes (2 ^ w) x8) < p256_group_order
        H18 : Forall (fun b => - 2 ^ w + 2 <= 2 * byte.signed b <= 2 ^ w) x1
        *)

        rewrite positional_signed_bytes_cons.

        admit.
      }

      split.
      {
        (* loop test. *)
        ZnWords.
      }

      repeat straightline.

      eexists _.
      ssplit; try ecancel_assumption; trivial.

      rewrite H37.
      rewrite H33.

      rewrite Jacobian.to_affine_add.

      rewrite H25, H29.

      rewrite H28.

      rewrite word.unsigned_of_Z_nowrap by lia.
      cbv [w Recode.w v i].

      (* Should be OK. *)
      admit.
    }

    (* Base case. *)
    eexists _.
    ssplit; try ecancel_assumption; trivial.

    rewrite H10.

    cbv [v].
    rewrite H13.
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

  rewrite H15.
  rewrite H12.

  rewrite ScalarMult.scalarmult_zero_r.
  rewrite Hierarchy.left_identity.

  cbv [i].
  rewrite word.unsigned_of_Z_nowrap by lia.

  assert (Z.to_nat 52 = length sscalar) as ->.
  {
    cbv [num_limbs] in *.
    lia.
  }
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
  rewrite H11 in H2.
  set (word.add a (word.of_Z (Z.of_nat 52))) in H2.

  straightline_call. (* call words_unpack *)
  {
    (* Solve words_unpack assumptions. *)
    ssplit; try ecancel_assumption; try (cbv [num_bits Recode.w] in *; ZnWords).
    rewrite word.unsigned_of_Z_nowrap by lia.
    cbv [p256_group_order] in *; lia.
  }

  repeat straightline.
  straightline_call. (* call recode_wrap *)
  {
    (* Solve recode_wrap assumptions. *)
    ssplit; try ecancel_assumption; trivial.
    { ZnWords. }
    {
      rewrite <-H17.
      cbv [Recode.w].
      (*rewrite word.unsigned_of_Z_nowrap in H8 by lia.*)
      change (5 * word.unsigned (word.of_Z 52)) with (260).
      cbv [p256_group_order] in *.
      lia.
    }
    { Decidable.vm_decide. }
  }

  repeat straightline.
  straightline_call. (* call p256_point_mul_signed *)
  { ssplit; try ecancel_assumption; trivial; try (cbv [num_limbs w]; ZnWords). }

  repeat straightline.

  (* Restore stack by combining scalar and padding. *)
  seprewrite_in_by (Array.bytearray_index_merge x0 padding) H21 ZnWords.
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

  cbv [Recode.w w] in *.
  rewrite H24.
  rewrite H22.
  rewrite <-H17.
  apply W.Equivalence_eq.
Qed.





















(* OLD PROOF STUFF *)

      (* Point addition requires the inputs to be non-zero.
         It returns ok = 0 if the points are the same, we have to prove that this case never happens.
       *)
      assert (~ Jacobian.iszero x9) as H_nz_x9 by admit.
      assert (~ Jacobian.iszero x11) as H_nz_x11 by admit.
      specialize (H32 H_nz_x9 H_nz_x11).
      destruct H32 as [[H_ok [H_point_diff H_point_add]] | [H_not_ok H_point_eq]]; cycle 1.

      (* Points are equal case. *)
      {
        exfalso.
        revert H_point_eq.
        rewrite Jacobian.eq_iff.
        rewrite H24.
        rewrite H28.

        rewrite H9.
        rewrite ScalarMult.scalarmult_assoc.
        rewrite Z.mul_comm, word.unsigned_of_Z_nowrap by lia.

        rewrite group_isom.

        intro Hmul.

        eapply positional_dist_p256.

        3 : {
          cbv [Recode.w].
          cbv [positional_signed_bytes] in Hmul.
          fold p256_group_order.
          rewrite <-Hmul.
          reflexivity.
        }
        { admit. }





        admit.
      }

      (* Points are distinct case. *)
      {
        eexists _, _, _, _, _.
        repeat straightline.
        {
          exists ((nth (Z.to_nat (word.unsigned (word.sub x7 (word.of_Z 1)))) x1 x00) :: x8).
          cbv [i] in H30.
          seprewrite_in_by bytearray_firstn_nth_skipn H30 ltac:(ZnWords).
          ssplit; try ecancel_assumption; trivial.
          {
            rewrite positional_signed_bytes_cons.

            rewrite ScalarMult.scalarmult_add_l.
            rewrite Z.mul_comm.
            rewrite <-ScalarMult.scalarmult_assoc.

            rewrite <-H9.

            rewrite (Jacobian.to_affine_add_inequal_nz_nz _ _ _ H_nz_x9 H_nz_x11).
            rewrite H24, H28.

            rewrite H27.

            rewrite word.unsigned_of_Z_nowrap by lia.
            cbv [w Recode.w].

            rewrite Hierarchy.commutative.
            reflexivity.
          }
          { ZnWords. }
          { rewrite <-H15. listZnWords. } (* TODO: Fix destroying x1 stuff. *)

          { admit. }

          (* Fix destroying x1 stuff. *)
          admit.
        }

        split.
        {
          (* loop test. *)
          ZnWords.
        }

        repeat straightline.

        eexists _.
        (* TODO: Fix destroying x1 stuff. *)
        rewrite <-(firstn_nth_skipn _ (Z.to_nat (word.unsigned i)) x1 x00 i_bounded) in H32.
        rewrite app_assoc, <-assoc_app_cons in H32.
        ssplit; try ecancel_assumption; trivial.

        rewrite H35.
        rewrite (Jacobian.to_affine_add_inequal_nz_nz _ _ _ H_nz_x9 H_nz_x11).
        rewrite H24, H28.

        rewrite H27.

        admit.
      }
    }

    (* Base case. *)
    eexists _.
    ssplit; try ecancel_assumption; trivial.

    rewrite H9.

    cbv [v].
    rewrite H12.
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

  rewrite H14.
  rewrite H11.

  rewrite ScalarMult.scalarmult_zero_r.
  rewrite Hierarchy.left_identity.

  cbv [i].
  rewrite word.unsigned_of_Z_nowrap by lia.

  assert (Z.to_nat 52 = length sscalar) as ->.
  {
    cbv [num_limbs] in *.
    lia.
  }
  rewrite firstn_all.

  reflexivity.
Admitted.


      destruct (ListUtil.break_list_last x1) as [|[sscalar_rest [sscalar_limb]]].
      {
        (* list cannot be empty *)
        rewrite <-length_zero_iff_nil in H21.
        lia.
      }
      rewrite H21 in *; clear dependent H21.
      (* split length *)
      rewrite length_app in H14.
      cbn [length] in H14.

      seprewrite_in Array.bytearray_append H22.
      cbn [bytearray] in H22.

      straightline_call. (* call load1_sext *)
      {
        assert (i = word.of_Z (Z.of_nat (length sscalar_rest))) as -> by ZnWords.
        ecancel_assumption.
      }

      repeat straightline.

      straightline_call. (* call p256_get_signed_mult *)
      {
        ssplit.
        {
          seprewrite_in_by (Array.array1_iff_eq_of_list_word_at a) H24 ltac:(lia).
          ecancel_assumption.
        }
        { rewrite length_point; trivial. }
      }

      repeat straightline.

      straightline_call. (* call p256_point_add_nz_nz_neq *)
      { ssplit; try ecancel_assumption; trivial. }

      repeat straightline.

      (* Deallocate stack. *)
      seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at _ _ _ _ _ _ a) H29 ltac:(rewrite length_point; lia).
      assert (length (to_bytes x10) = 96%nat) by (rewrite length_point; trivial).

      (* TODO: repeat straighline hangs here so we do it in steps. *)
      straightline.

      eexists _, _, _, _.
      split.
      { repeat straightline. }

      repeat straightline.

      (* Point addition requires the inputs to be non-zero.
         It returns ok = 0 if the points are the same, we have to prove that this case never happens.
       *)
      assert (~ Jacobian.iszero x9) as H_nz_x9 by admit.
      assert (~ Jacobian.iszero x10) as H_nz_x10 by admit.
      specialize (H31 H_nz_x9 H_nz_x10).
      destruct H31 as [[H_ok [H_point_diff H_point_add]] | [H_not_ok H_point_eq]]; cycle 1.

      (* Points are equal case. *)
      {
        exfalso.
        revert H_point_eq.
        rewrite Jacobian.eq_iff.
        rewrite H23.
        rewrite H27.

        rewrite H9.

        admit.
      }

      (* Points are distinct case. *)
      {
        eexists _, _, _, _, _.
        repeat straightline.
        {
          eexists _. (* TODO: needs correct bytes *)
          ssplit; try ecancel_assumption; trivial.
          { admit. }
          {
            ZnWords.
          }
          { admit. }
          rewrite Forall_app in H16.
          destruct H16.
          trivial.
        }

        split.
        {
          (* loop test. *)
          ZnWords.
        }

        repeat straightline.

        eexists _.
        ssplit; trivial.
        {
          seprewrite Array.bytearray_append.
          cbn [bytearray].
          assert (i = word.of_Z (Z.of_nat (length sscalar_rest))) as -> by ZnWords.
          ecancel_assumption.
        }

        rewrite H34.
        subst i.
        rewrite (Jacobian.to_affine_add_inequal_nz_nz _ _ _ H_nz_x9 H_nz_x10).

        rewrite H23.
        rewrite H27.
        rewrite H26.

        rewrite positional_signed_bytes_app.
        cbn [positional_signed_bytes positional List.map fold_right].
        rewrite Z.mul_0_r, Z.add_0_r.

        rewrite word.unsigned_sub_nowrap by ZnWords.
        rewrite <-H14.

        rewrite ?word.unsigned_of_Z_nowrap by lia.

        admit.
      }
    }

    (* Base case. *)
    eexists _.
    ssplit; try ecancel_assumption; trivial.

    assert (x1 = []) as ->.
    {
      rewrite <-length_zero_iff_nil.
      ZnWords.
    }
    cbn [positional_signed_bytes positional List.map fold_right].

    rewrite ScalarMult.scalarmult_0_l.
    rewrite Hierarchy.right_identity.

    rewrite H12, Z.mul_0_r, Z.pow_0_r.
    rewrite ScalarMult.scalarmult_1_l.
    reflexivity.
  }

  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; trivial.

  rewrite H14.
  rewrite H11.

  rewrite ScalarMult.scalarmult_zero_r.
  rewrite Hierarchy.left_identity.

  reflexivity.
Admitted.
