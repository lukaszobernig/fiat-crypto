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
memcpy.

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
End W.

Local Notation Wzero := (W.zero
  (F := F p256)
  (Feq := eq)
  (Fadd := F.add)
  (Fmul := F.mul)
  (a := W.a)
  (b := W.b)
  ).

Existing Instance W.commutative_group.

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
(* TODO: Infer this from P256 modulus size and w. *)
Definition num_limbs := 52%nat.

(* Align helpers. *)
Definition align_mask x mask := Z.land (x + mask) (Z.lnot mask).
Definition align x a := align_mask x (a - 1).

(*Definition sext_byte_word x :=
  let sign_bit := Z.land (Z.shiftr x 7) 1 in
  let mask := Z.shiftl (0 - sign_bit) 8 in
  Z.lor x mask.

Local Instance spec_of_sext_byte_word : spec_of "sext_byte_word" :=
  fnspec! "sext_byte_word" x / y,
  { requires t m := True;
    ensures T M :=
    M = m /\ T = t /\
    y = sext_byte_word x
  }.*)

(* TODO: sscalar is passed in little endian, this atm processes it as big endian *)
Definition p256_point_mul_signed :=
  func! (p_out, p_sscalar, p_P) {
    p256_set_zero(p_out); (* Set result point to identity. *)

    i = $0;
    while i < $num_limbs {
      stackalloc sizeof_point as p_kP; (* Temporary point kP. *)

      p256_mul_by_pow2(p_out, $w); (* OUT = [2^w]OUT *)
      k = load1(p_sscalar); (* k is a recoded signed scalar limb. *)
      (* TODO: sign extended load into k *)
      p256_get_signed_mult(p_kP, p_P, k); (* kP = [k]P *)
      unpack! ok = p256_point_add_nz_nz_neq(p_out, p_out, p_kP); (* OUT = OUT + kP *)

      p_sscalar = p_sscalar + $1;
      i = i + $1;

      $(cmd.unset "ok");
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

(*
  TODO: prove in-place spec/lemma of p256_point_add_nz_nz_neq
*)
Definition spec_of_p256_point_add_nz_nz_neq_inplace : spec_of "p256_point_add_nz_nz_neq" :=
  fnspec! "p256_point_add_nz_nz_neq" p_out p_P p_Q / (P Q : point) R ~> ok,
  { requires t m := m =* P$@p_P * Q$@p_Q * R /\ p_out = p_P;
    ensures t' m := t' = t /\ exists out,
    m =* out$@p_out * Q$@p_Q * R /\ length out = length P /\ (
        ~ Jacobian.iszero P -> ~ Jacobian.iszero Q ->
        (ok <> word.of_Z 0 /\ exists pfPneqQ, out = (Jacobian.add_inequal_nz_nz P Q pfPneqQ : point)) \/
        (ok = word.of_Z 0) /\ Jacobian.eq P Q)
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
    ensures T M := exists (Q : point),
    M =* Q$@p_out * P$@p_P * R /\
    W.eq (Jacobian.to_affine Q) (W.mul (word.signed k) (Jacobian.to_affine P)) /\
    T = t
  }.

Local Instance spec_of_p256_point_mul_signed : spec_of "p256_point_mul_signed" :=
  fnspec! "p256_point_mul_signed" (p_out p_sscalar p_P : word) / out sscalar (P : point) R,
  { requires t m :=
    m =* out$@p_out * bytearray p_sscalar sscalar * P$@p_P * R /\
    length out = length P /\ length sscalar = num_limbs /\
    positional_signed_bytes (2^w) sscalar < Specs.p256 /\
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
    Z.of_bytes scalar < Specs.p256;
    ensures T M := exists (Q : point) (* Q = [scalar]P *),
      M =* Q$@p_out * bytearray p_scalar scalar * P$@p_P * R /\ (* ... *)
      W.eq (Jacobian.to_affine Q) (W.mul (Z.of_bytes scalar) (Jacobian.to_affine P)) /\
      T = t
  }.

From coqutil Require Import Tactics.Tactics Macros.symmetry.

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
      apply W.Equivalence_eq.
    }

    (* Base case. *)
    eexists _.
    ssplit; try ecancel_assumption; trivial.
    rewrite H2.
    rewrite Z.pow_0_r.
    rewrite ScalarMult.scalarmult_1_l.
    apply W.Equivalence_eq.
  }

  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; trivial.
Qed.

Lemma positional_signed_bytes_cons B (h : byte) (t : list byte) :
  positional_signed_bytes B (h :: t) = byte.signed h + B*(positional_signed_bytes B t).
Proof. constructor. Qed.

Lemma p256_point_mul_signed_ok :
  let _ := spec_of_p256_point_add_nz_nz_neq_inplace in
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
                                  (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                  HList.polymorphic_list.nil))))
    (* program variables *) (["p_out";"p_sscalar";"p_P";"i"] : list String.string))
    (fun v (out : point) sscalar (P : point) R t m p_out p_sscalar p_P i => PrimitivePair.pair.mk (* precondition *)
      (v = word.unsigned i /\
      m =* out$@p_out * bytearray p_sscalar sscalar * P$@p_P * R /\
      length sscalar = (num_limbs - Z.to_nat i)%nat /\
      positional_signed_bytes (2^w) sscalar < Specs.p256 /\
      Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) sscalar)
    (fun                                       T M P_OUT P_SSCALAR P_P I => (* postcondition *)
      exists (Q : point),
      M =* Q$@p_out * bytearray p_sscalar sscalar * P$@p_P * R /\
      p_out = P_OUT /\ p_P = P_P /\
      W.eq (Jacobian.to_affine Q)
           (W.add
            (W.mul (2^(w*(num_limbs - i))) (Jacobian.to_affine out))
            (W.mul (positional_signed_bytes (2^w) sscalar) (Jacobian.to_affine P)))
      /\
      T = t))
    (fun n m => m < n <= num_limbs) (* well_founded relation *)
    _ _ _ _ _ _ _ _ _);
  Loops.loop_simpl.

  { repeat straightline. }
  { eapply Z.gt_wf. }
  {
    repeat straightline.
    ssplit; try ecancel_assumption; trivial.
  }

  {
    repeat straightline.
    {
      straightline_call. (* call p256_mul_by_pow2 *)
      { ecancel_assumption. }

      repeat straightline.
      destruct x1 as [| x1_0 x1_rest].
      {
        (* Empty list case. *)
        rewrite List.length_nil in *.
        admit.
      }

      cbn [bytearray] in * |-.
      repeat straightline.

      straightline_call. (* call p256_get_signed_mult *)
      {
        ssplit.
        {
          seprewrite_in_by (Array.array1_iff_eq_of_list_word_at a) H20 ltac:(lia).
          ecancel_assumption.
        }
        { rewrite length_point; trivial. }
      }

      repeat straightline.

      straightline_call. (* call p256_point_add_nz_nz_neq *)
      { ssplit; try ecancel_assumption; trivial. }

      repeat straightline.

      (* Deallocate stack. *)
      seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at _ _ _ _ _ _ a) H25 ltac:(rewrite length_point; lia).
      assert (length (to_bytes x1) = 96%nat) by (rewrite length_point; trivial).

      (* TODO: repeat straighline hangs here so we do it in steps. *)
      straightline.

      eexists _, _, _, _.
      split.
      { repeat straightline. }

      (* Point addition requires the inputs to be non-zero.
         It returns ok = 0 if the points are the same, we have to prove that this case never happens.
       *)
      assert (~ Jacobian.iszero x8) as H_nz_x8 by admit.
      assert (~ Jacobian.iszero x1) as H_nz_x1 by admit.
      specialize (H27 H_nz_x8 H_nz_x1).
      destruct H27 as [[H_ok [H_point_diff H_point_add]] | [H_not_ok H_point_eq]].

      (* Points are distinct case. *)
      {
        eexists (Jacobian.add_inequal_nz_nz x8 x1 H_point_diff), x1_rest, x2, _, _.

        split.
        {
          replace (p_sscalar) with (word.add x5 (word.of_Z 1)) by ZnWords.
          replace (i) with (word.add x7 (word.of_Z 1)) by ZnWords.
          rewrite H_point_add in H25.
          ssplit; try ecancel_assumption; trivial.
          {
            rewrite length_cons in H12.
            cbv [num_limbs] in *.
            ZnWords.
          }
          {
            rewrite positional_signed_bytes_cons in H13.
            cbv [w Recode.w] in *.
            admit. (* TODO: this should go by ZnWords?! *)
          }
          inversion H14.
          trivial.
        }

        split.
        {
          (* loop test. *)
          cbv [num_limbs].
          revert H8.
          unfold br.
          case word.ltu_spec; intros; try ZnWords.
        }

        repeat straightline.

        eexists _.
        cbn [bytearray].
        ssplit; try ecancel_assumption; trivial.
        admit.
      }

      (* Points are equal case. *)
      admit.
    }

    (* base case. *)
    eexists _.
    ssplit; try ecancel_assumption; trivial.

    revert H8.
    unfold br.
    case word.ltu_spec; intros; try (rewrite word.unsigned_of_Z_nowrap in H15 by lia; lia).

    (* need something to show x7 = 52*)

    assert (x7 = word.of_Z 52) as -> by admit.
    unfold num_limbs.
    rewrite word.unsigned_of_Z_nowrap by lia.
    assert (Z.of_nat 52 = 52) as -> by lia.
    cbv [w Recode.w].
    assert (2 ^ (5 * (52 - 52)) = 1) as -> by lia.

    rewrite ScalarMult.scalarmult_1_l.

    cbv [num_limbs] in H12.
    assert (length x1 = 0%nat) by ZnWords.
    rewrite length_zero_iff_nil in H16.
    rewrite H16.
    cbn [positional_signed_bytes positional_bytes positional List.map fold_right].
    rewrite ScalarMult.scalarmult_0_l.

    admit.
  }

  repeat straightline.

  eexists x4.
  ssplit; try ecancel_assumption; trivial.

  rewrite H13.

  (* rewriting W.zero hangs *)
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
    cbv [p256] in *; lia.
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
      cbv [p256] in *.
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
