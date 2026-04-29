Require Import String coqutil.Datatypes.List.
Require Import Bedrock.P256.Specs.
Import Specs.NotationsCustomEntry Specs.coord Specs.point.
Import bedrock2.Syntax
bedrock2.NotationsCustomEntry
bedrock2.ZnWords
bedrock2.wsize
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
From coqutil Require Import Tactics.Tactics Macros.symmetry.

#[local] Open Scope string_scope.
#[local] Open Scope Z_scope.
#[local] Open Scope bool_scope.
#[local] Open Scope list_scope.

Require Import Crypto.Arithmetic.Signed.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.AffineProofs.
Require Import Crypto.Curves.Weierstrass.P256.
From Crypto.Bedrock.P256 Require Import Jacobian RecodeSpecs RecodeProofs PrecomputedMultiples.

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

#[local] Notation "xs $@ a" := (map.of_list_word_at a xs)
  (at level 10, format "xs $@ a").

#[local] Notation bytearray := (Array.array ptsto (word.of_Z 1)).

(* TODO: should this be global somewhere? *)
#[local] Notation sizeof_point := 96%nat.

#[local] Notation pointarray := (Array.array (fun (p : word.rep) (Q : point) =>
  sepclause_of_map ((to_bytes Q)$@p)) (word.of_Z (Z.of_nat sizeof_point))).

(* Limb size (nonzero). *)
#[local] Notation w := 5.
#[local] Notation num_bits := 256%nat.
(* TODO: Infer this from p256 group order and w. *)
(* Compute (Z.log2 p256_group_order) / w + 1. *)
#[local] Notation num_limbs := 52%nat.

(* Align helpers. *)
Definition align_mask x mask := Z.land (x + mask) (Z.lnot mask).
Definition align x a := align_mask x (a - 1).

Definition load1_sext :=
  func! (p_b) ~> r {
    r = (load1(p_b) << ($wsize - $8)) .>> ($wsize - $8)
  }.

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

Definition p256_point_mul_signed :=
  func! (p_out, p_sscalar, p_P) {
    stackalloc (sizeof_point * 17) as p_table;
    p256_precompute_multiples(p_table, p_P); (* Precompute multiples [k]P for k \in [0, 16].*)
    p256_point_set_zero(p_out); (* Set result point to identity. *)
    i = $num_limbs;
    while i {
      i = i - $1;
      stackalloc sizeof_point as p_kP; (* Temporary point kP = [k]P. *)
      stackalloc sizeof_point as p_tmp; (* Temporary point for addition. *)
      p256_mul_by_pow2(p_out, $w); (* OUT = [2^w]OUT *)
      unpack! k = load1_sext(p_sscalar + i); (* k is the next recoded signed scalar limb. *)
      p256_get_multiple(p_kP, p_table, k); (* kP = [k]P *)
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
    decompose_to_limbs(p_sscalar, p_scalar, $num_bits); (* Unpack scalar into unsigned w-bit limbs. *)
    signed_recode(p_sscalar, $num_limbs); (* Recode scalar into signed w-bit limbs. *)
    p256_point_mul_signed(p_out, p_sscalar, p_P) (* Multiply using signed multiplication. *)
  }.

#[export] Instance spec_of_load1_sext : spec_of "load1_sext" :=
  fnspec! "load1_sext" p_b / b R ~> r,
  { requires t m :=
    m =* ptsto p_b b * R;
    ensures T M :=
    M =* ptsto p_b b * R /\ T = t /\
    word.signed r = byte.signed b
  }.

(* Alternative spec for p256_point_add_vartime_if_doubling that disallows equal inputs if either is nonzero. *)
#[export] Instance spec_of_p256_point_add_vartime_if_doubling_alt : spec_of "p256_point_add_vartime_if_doubling" :=
  fnspec! "p256_point_add_vartime_if_doubling" p_out p_P p_Q / out (P Q : point) R,
  { requires t m :=
      m =* out$@p_out * P$@p_P * Q$@p_Q * R /\
      length out = length P /\
      (~ (W.eq (Jacobian.to_affine P) W.zero /\ W.eq (Jacobian.to_affine Q) W.zero) ->
        ~ W.eq (Jacobian.to_affine P) (Jacobian.to_affine Q));
    ensures T M := T = t /\ exists (out : point),
      M =* out$@p_out * P$@p_P * Q$@p_Q * R /\
      Jacobian.eq out (Jacobian.add P Q)
  }.

#[export] Instance spec_of_p256_mul_by_pow2 : spec_of "p256_mul_by_pow2" :=
  fnspec! "p256_mul_by_pow2" p_P n / (P : point) R,
  { requires t m :=
    m =* P$@p_P * R;
    ensures T M := exists (Q : point),
    M =* Q$@p_P * R /\
    W.eq (Jacobian.to_affine Q) (W.mul (2^n) (Jacobian.to_affine P)) /\
    T = t
  }.

#[export] Instance spec_of_p256_point_mul_signed : spec_of "p256_point_mul_signed" :=
  fnspec! "p256_point_mul_signed" (p_out p_sscalar p_P : word) / out sscalar (P : point) R,
  { requires t m :=
    m =* out$@p_out * bytearray p_sscalar sscalar * P$@p_P * R /\
    ~ Jacobian.iszero P /\
    length out = length P /\ length sscalar = num_limbs /\
    0 < positional_signed_bytes (2^w) sscalar < p256_group_order /\
    Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) sscalar;
    ensures T M := exists (Q : point) (* Q = [sscalar]P *),
      M =* Q$@p_out * bytearray p_sscalar sscalar * P$@p_P * R /\ (* ... *)
      W.eq (Jacobian.to_affine Q) (W.mul (positional_signed_bytes (2^w) sscalar) (Jacobian.to_affine P)) /\
      T = t
  }.

#[export] Instance spec_of_p256_point_mul : spec_of "p256_point_mul" :=
  fnspec! "p256_point_mul" (p_out p_scalar p_P : word) / out scalar (P : point) R,
  { requires t m :=
    m =* out$@p_out * bytearray p_scalar scalar * P$@p_P * R /\
    ~ Jacobian.iszero P /\
    length out = length P /\
    8 * (length scalar - 1) < num_bits <= 8 * length scalar /\
    0 < Z.of_bytes scalar < p256_group_order;
    ensures T M := exists (Q : point) (* Q = [scalar]P *),
      M =* Q$@p_out * bytearray p_scalar scalar * P$@p_P * R /\ (* ... *)
      W.eq (Jacobian.to_affine Q) (W.mul (Z.of_bytes scalar) (Jacobian.to_affine P)) /\
      T = t
  }.

Definition pointarray_to_bytes (pa : list point) := flat_map to_bytes pa.

Lemma pointarray_iff_eq_bytearray (a : word) (bs : list point)
  : Lift1Prop.iff1 (pointarray a bs) (bytearray a (pointarray_to_bytes bs)).
Proof.
  revert a; cbv [pointarray_to_bytes]; induction bs; intros.
  { apply iff1_refl. }
  {
    rewrite Array.array_cons.
    rewrite ListUtil.List.flat_map_cons.
    rewrite Array.array_append.
    rewrite word.unsigned_of_Z_1, Z.mul_1_l.
    rewrite length_point.
    rewrite IHbs.
    rewrite <-Array.array1_iff_eq_of_list_word_at.
    { cancel. }
    { exact _. }
    { rewrite length_point. lia. }
  }
Qed.

Lemma load1_sext_ok : program_logic_goal_for_function! load1_sext.
Proof.
  repeat straightline.
  ssplit; try ecancel_assumption; trivial.
  cbv [r Semantics.interp_op1].
  rewrite eval_wsize'.
  rewrite <-word.ring_morph_sub.
  rewrite word.signed_srs_nowrap by ZnWords.
  rewrite word.signed_eq_swrap_unsigned.
  rewrite word.unsigned_slu_shamtZ by lia.
  rewrite ?word.unsigned_of_Z_nowrap; try (pose proof byte.unsigned_range b; lia).
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  cbv [byte.signed word.wrap byte.swrap word.swrap].
  PreOmega.Z.div_mod_to_equations.
  lia.
Qed.

Lemma iszero_false_decidable P : iszero P = false -> ~ Jacobian.iszero P.
Proof.
  unfold iszero.
  destruct (Crypto.Util.Decidable.dec (Jacobian.iszero _)); [discriminate|trivial].
Qed.

Import memcpy.
Lemma p256_point_add_vartime_if_doubling_alt_ok :
  (* Use the alternative spec for p256_point_add_vartime_if_doubling. *)
  let _ := spec_of_p256_point_add_vartime_if_doubling_alt in
  program_logic_goal_for_function! p256_point_add_vartime_if_doubling.
Proof.
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
  { rewrite <-word.unsigned_of_Z_0, !word.unsigned_inj_iff in H28 by exact _.
    rewrite !word.lor_0_iff, !word.broadcast_0_iff in H28.
    destruct H28 as [[HP HQ] Hx1zero]; apply iszero_false_decidable in HP, HQ.
    destruct H11.
    { rewrite <-?Jacobian.iszero_iff.
      enough (~ Jacobian.iszero P \/ ~ Jacobian.iszero Q) by intuition; now left. }
    { rewrite <-Jacobian.eq_iff.
      pose proof (H20 HP HQ) as Hadd; rewrite Hx1zero in Hadd.
      destruct Hadd as [[]|[]]; congruence. } }
Qed.

Local Ltac subst_to_affine :=
  repeat match goal with |- context [Jacobian.to_affine ?P] =>
    match goal with H : context [Jacobian.to_affine P] |- _ =>
      rewrite H
    end
  end.

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
  { (* Base case. *)
    repeat straightline.
    ecancel_assumption. }
  { intros ? ?kP ? ? ? ? ?power.
     repeat straightline.
    (* Induction case. *)
    { straightline_call. (* call p256_point_double *)
      { split.
        { seprewrite_in_by Array.array1_iff_eq_of_list_word_at H3 ltac:(lia).
          ecancel_assumption. }
        { rewrite length_point; trivial. } }
      repeat straightline.
      straightline_call. (* call br_memcpy *)
      { ssplit; try ecancel_assumption.
        { rewrite length_point; trivial. }
        { rewrite length_point; trivial. }
        ZnWords. }
      repeat straightline.
      (* Deallocate stack. *)
      seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at _ _ _ _ _ _ a) H11 ltac:(rewrite length_point; lia).
      assert (length (to_bytes (Jacobian.double_minus_3 eq_refl kP)) = sizeof_point) by (rewrite length_point; trivial).
      repeat straightline.
      eexists _, _, (word.unsigned n).
      repeat straightline.
      { ecancel_assumption. }
      split.
      { ZnWords. }
      repeat straightline.
      eexists _.
      ssplit; try ecancel_assumption; trivial.
      subst_to_affine.
      subst n.
      rewrite word.unsigned_sub, word.unsigned_of_Z_nowrap by lia.
      cbv [word.wrap].
      rewrite Z.mod_small by ZnWords.
      rewrite <-Jacobian.double_minus_3_eq_double.
      rewrite Jacobian.to_affine_double.
      rewrite <-ScalarMult.scalarmult_2_l.
      rewrite ScalarMult.scalarmult_assoc.
      assert (2 * 2 ^ (word.unsigned power - 1) = 2 ^ word.unsigned power) as ->.
      { rewrite <-Z.pow_succ_r by ZnWords.
        f_equal.
        lia. }
      reflexivity. }
    (* Post condition. *)
    eexists _.
    ssplit; try ecancel_assumption; trivial.
    rewrite H2.
    rewrite Z.pow_0_r.
    rewrite ScalarMult.scalarmult_1_l.
    reflexivity. }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; trivial.
Qed.

Lemma bytearray_firstn_nth_skipn l (i : word) start d :
  ((Z.to_nat (word.unsigned i)) < length l)%nat ->
    (Lift1Prop.iff1
      ((ptsto (word.add start i) (nth (Z.to_nat (word.unsigned i)) l d)) *
       (bytearray start (List.firstn (Z.to_nat (word.unsigned i)) l)) *
       (bytearray (word.add (word.add start (word.of_Z (Z.of_nat (length (ListDef.firstn (Z.to_nat (word.unsigned i)) l))))) (word.of_Z 1))
         (List.skipn (S (Z.to_nat (word.unsigned i))) l)))
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
  intros ? iBound.
  remember (positional B (skipn i l) * B + nth (i - 1) l d).
  rewrite <-(firstn_nth_skipn _ (i - 1) l d iBound).
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
  induction a as [|? ? Hyp].
  { rewrite app_nil_l.
    rewrite length_nil.
    cbn [positional fold_right].
    lia. }
  { rewrite <-app_comm_cons.
    rewrite !positional_cons.
    rewrite Hyp.
    rewrite length_cons.
    rewrite Z.mul_add_distr_l.
    rewrite Z.mul_assoc.
    rewrite Pow.Z.pow_mul_base by lia.
    lia. }
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
  intros ? iBound.
  remember (positional B (skipn i l) * B ^ i + (nth (i - 1) l d) * B ^ (i - 1) + positional B (firstn (i - 1) l)).
  rewrite <-(firstn_nth_skipn _ (i - 1) l d iBound).
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

Lemma p256_point_mul_signed_ok :
  (* Use the alternative spec for p256_point_add_vartime_if_doubling. *)
  let _ := spec_of_p256_point_add_vartime_if_doubling_alt in
  program_logic_goal_for_function! p256_point_mul_signed.
Proof.
  repeat straightline.
  straightline_call. (* call p256_precompute_multiples *)
  { seprewrite_in_by (Array.array1_iff_eq_of_list_word_at a) H6 ltac:(lia).
    ssplit; try ecancel_assumption; trivial. }
  repeat straightline.
  straightline_call. (* call p256_point_set_zero *)
  { ssplit; try ecancel_assumption; trivial. }
  repeat straightline.
  refine ((Loops.tailrec
    (* types of ghost variables*) (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                  (HList.polymorphic_list.cons _
                                  HList.polymorphic_list.nil)))
    (* program variables *) (["p_out";"p_sscalar";"p_P";"p_table";"i"] : list String.string))
    (fun v table (curr_out : point) R t m p_out p_sscalar p_P p_table i => PrimitivePair.pair.mk (* precondition *)
      (let processed_limbs := skipn (Z.to_nat v) sscalar in
       let processed_scalar := positional_signed_bytes (2^w) processed_limbs in
       W.eq (Jacobian.to_affine curr_out) (W.mul processed_scalar (Jacobian.to_affine P)) /\
       v = word.unsigned i /\
       0 <= v <= num_limbs /\
       Forall2 W.eq (map Jacobian.to_affine table) (W.multiples 17 (Jacobian.to_affine P)) /\
       m =* curr_out$@p_out * bytearray p_sscalar sscalar * P$@p_P * pointarray p_table table * R /\
       Z.of_nat (length sscalar) = num_limbs)
    (fun                              T M P_OUT P_SSCALAR P_P P_TABLE I => (* postcondition *)
      exists (Q : point),
      M =* Q$@p_out * bytearray p_sscalar sscalar * P$@p_P * pointarray p_table table * R /\
      p_out = P_OUT /\ p_P = P_P /\ p_table = P_TABLE /\
      W.eq (Jacobian.to_affine Q)
           (W.add
            (W.mul (2^(w*i)) (Jacobian.to_affine curr_out))
            (W.mul (positional_signed_bytes (2^w) (firstn (Z.to_nat v) sscalar)) (Jacobian.to_affine P))) /\
      T = t))
    (fun n m => 0 <= n < m) (* well_founded relation *)
    _ _ _ _ _ _ _ _);
  Loops.loop_simpl.
  { repeat straightline. }
  { eapply Z.lt_wf. }
  { (* Base case. *)
    repeat straightline.
    ssplit; try ecancel_assumption; trivial.
    { subst i.
      assert (Z.to_nat (word.unsigned (word.of_Z _)) = num_limbs) as -> by ZnWords.
      rewrite List.skipn_all by ZnWords.
      cbn [positional_signed_bytes positional fold_right map].
      rewrite Jacobian.to_affine_of_affine.
      rewrite ScalarMult.scalarmult_0_l.
      Morphisms.f_equiv. }
    { ZnWords. }
    { ZnWords. }
    { lia. } }
  { (* Induction case. *)
    intros ?v ?table ?curr_out ?R ?t ?m ?p_out ?p_sscalar ?p_P ?p_table? ?i.
    repeat straightline.
    { rename a0 into p_kP.
      straightline_call. (* call p256_mul_by_pow2 *)
      { ecancel_assumption. }
      repeat straightline.
      assert (Z.to_nat (word.unsigned i) < length sscalar)%nat as i_bounded by ZnWords.
      pose proof (symmetry! firstn_nth_skipn _ (Z.to_nat (word.unsigned i)) sscalar x00 i_bounded) as sscalar_parts.
      rewrite sscalar_parts in H36.
      rewrite app_assoc, <-assoc_app_cons in H36.
      seprewrite_in Array.bytearray_append H36.
      cbn [bytearray] in H36.
      rename x1 into shifted_out.
      straightline_call. (* call load1_sext *)
      { assert (i = word.of_Z (Z.of_nat (length (ListDef.firstn (Z.to_nat (word.unsigned i)) sscalar)))) as -> by listZnWords.
        ecancel_assumption. }
      repeat straightline.
      rename x1 into k.
      straightline_call. (* call p256_get_multiple *)
      { split; [|split; [|split; [|split]]].
        4 : { eapply H23. }
        { seprewrite_in_by (Array.array1_iff_eq_of_list_word_at p_kP) H38 ltac:(lia).
          ecancel_assumption. }
        { rewrite length_point.
          ZnWords. }
        { rewrite <-(length_map Jacobian.to_affine).
          erewrite Forall2_length by exact H23.
          trivial. }
        { rewrite H40.
          apply Forall_nth.
          { eapply Forall_impl; [| exact H11].
            intros ? Hbounds.
            cbv [id] in Hbounds.
            lia. }
          ZnWords. } }
      repeat straightline.
      rename x1 into kP.
      straightline_call. (* call p256_point_add_vartime_if_doubling *)
      { seprewrite_in_by (Array.array1_iff_eq_of_list_word_at a3) H41 ltac:(lia).
        ssplit; try ecancel_assumption; trivial.
        intros.
        subst_to_affine.
        rewrite ScalarMult.scalarmult_assoc.
        rewrite Z.mul_comm, word.unsigned_of_Z_nowrap by lia.
        rewrite p256_mul_mod_n.
        unfold positional_signed_bytes in *.
        rewrite <- skipn_map in *.
        rewrite H40.
        rewrite <- map_nth in *.
        (* TODO these could probably be cleaned up earlier in the proof. *)
        replace ((Z.to_nat (word.unsigned (word.sub x0 (word.of_Z 1))))) with ((Z.to_nat v - 1))%nat in * by ZnWords.
        replace (byte.signed "000") with 0 in * by (cbn; ZnWords).
        apply (fixed_window_no_doubling') with (xs := (firstn (Z.to_nat v - 1) (map byte.signed sscalar))); unfold p256_group_order in *.
        all: try ZnWords.
        { apply Forall_firstn. rewrite Forall_map. assumption. }
        { apply Forall_skipn. rewrite Forall_map. assumption. }
        { apply Forall_nth. { rewrite Forall_map. assumption. } rewrite map_length. lia. }
        { intros [?N1 ?N2].
          apply H35; split.
          { subst_to_affine. unfold positional.
            rewrite N2.
            rewrite ScalarMult.scalarmult_0_l, ScalarMult.scalarmult_zero_r.
            reflexivity. }
          { subst_to_affine.
            rewrite H40, N1.
            rewrite ScalarMult.scalarmult_0_l.
            reflexivity. } }
        { rewrite ListUtil.app_cons_app_app. rewrite <- app_assoc.
          replace ( skipn (Z.to_nat v) (map byte.signed sscalar)) with (skipn (S (Z.to_nat v - 1)) (map byte.signed sscalar)).
          2: { f_equal. lia. }
          rewrite firstn_nth_skipn.
          { unfold positional in *. lia. }
          { rewrite map_length. lia. } } }
      repeat straightline.
      rename x1 into curr_out_new.
      straightline_call. (* call br_memcpy *)
      { ssplit; try ecancel_assumption; trivial.
        ZnWords. }
      repeat straightline.
      (* Deallocate stack. *)
      seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at _ _ _ _ _ _ p_kP) H45 ltac:(rewrite length_point; lia).
      assert (length (to_bytes kP) = 96%nat) by (rewrite length_point; trivial).
      (* Deallocate stack. *)
      seprewrite_in_by (symmetry! @Array.array1_iff_eq_of_list_word_at _ _ _ _ _ _ a3) H45 ltac:(rewrite length_point; lia).
      assert (length (to_bytes curr_out_new) = 96%nat) by (rewrite length_point; trivial).
      (* TODO: repeat straighline hangs here so we do it in steps. *)
      do 2 straightline.
      eexists _, _, _, _, _.
      split.
      { repeat straightline. }
      repeat straightline.
      eexists _, _, _, _.
      repeat straightline.
      { cbv [i] in H45.
        seprewrite_in_by bytearray_firstn_nth_skipn H45 ltac:(ZnWords).
        ssplit; try ecancel_assumption; trivial.
        { rewrite H44.
          rewrite Jacobian.to_affine_add.
          subst_to_affine.
          rewrite H40.
          subst i v.
          rewrite ScalarMult.scalarmult_assoc.
          rewrite <-ScalarMult.scalarmult_add_l.
          rewrite word.unsigned_of_Z_nowrap by lia.
          cbv [positional_signed_bytes].
          rewrite <-?skipn_map.
          assert (
            Z.to_nat (word.unsigned (word.sub x0 (word.of_Z 1))) =
            (Z.to_nat (word.unsigned x0) - 1)%nat
          ) as -> by ZnWords.
          rewrite (positional_skipn_nth _ _ _ (byte.signed x00)).
          { rewrite map_nth.
            reflexivity. }
          { ZnWords. }
          { rewrite length_map.
            ZnWords. } }
        { ZnWords. }
        { ZnWords. } }
      split.
      { ZnWords. } (* loop test *)
      repeat straightline.
      eexists _.
      ssplit; try ecancel_assumption; trivial.
      subst_to_affine.
      rewrite H44.
      rewrite Jacobian.to_affine_add.
      subst_to_affine.
      rewrite word.unsigned_of_Z_nowrap by lia.
      rewrite H40.
      subst v i.
      cbv [positional_signed_bytes].
      rewrite <-?skipn_map, <-?firstn_map.
      assert (
        Z.to_nat (word.unsigned (word.sub x0 (word.of_Z 1))) =
        (Z.to_nat (word.unsigned x0) - 1)%nat
      ) as -> by ZnWords.
      repeat rewrite ?ScalarMult.scalarmult_assoc, <-?ScalarMult.scalarmult_add_l.
      Morphisms.f_equiv.
      rewrite (Z.pow_mul_r 2 w (word.unsigned x0)) by lia.
      assert ((2 ^ w) ^ word.unsigned x0 = (2 ^ w) ^ Z.of_nat (Z.to_nat x0)) as -> by (f_equal; ZnWords).
      rewrite <-positional_firstn_skipn by listZnWords.
      rewrite <-map_nth.
      rewrite (Z.pow_mul_r 2 w (word.unsigned (word.sub x0 (word.of_Z 1)))) by ZnWords.
      assert ((2 ^ w) ^ word.unsigned (word.sub x0 (word.of_Z 1)) = (2 ^ w) ^ Z.of_nat (Z.to_nat x0 - 1)) as -> by (f_equal; ZnWords).
      rewrite Z.mul_add_distr_r.
      rewrite <-Z.mul_assoc.
      assert (
        2 ^ w * (2 ^ w) ^ Z.of_nat (Z.to_nat (word.unsigned x0) - 1) =
        (2 ^ w) ^ Z.of_nat (Z.to_nat (word.unsigned x0))
      ) as ->.
      { rewrite Pow.Z.pow_mul_base by ZnWords.
        f_equal.
        ZnWords. }
      assert (Z.of_nat (Z.to_nat (word.unsigned x0) - 1) = Z.of_nat (Z.to_nat (word.unsigned x0)) - 1) as -> by lia.
      rewrite <-positional_firstn_nth_skipn_prev; (rewrite ?length_map; lia). }
    (* Post condition. *)
    eexists _.
    ssplit; try ecancel_assumption; trivial.
    subst_to_affine.
    cbv [v].
    rewrite H18.
    rewrite Znat.Z2Nat.inj_0, firstn_0.
    cbn [positional_signed_bytes positional List.map fold_right].
    rewrite ScalarMult.scalarmult_0_l.
    rewrite Hierarchy.right_identity.
    rewrite Z.mul_0_r, Z.pow_0_r.
    rewrite ScalarMult.scalarmult_1_l.
    reflexivity. }
  repeat straightline.
  (* Deallocate stack. *)
  seprewrite_in pointarray_iff_eq_bytearray H17.
  assert (length (pointarray_to_bytes x) = 1632%nat).
  { cbv [pointarray_to_bytes].
    rewrite (flat_map_constant_length (c := 96)) by trivial.
    rewrite <-(length_map Jacobian.to_affine).
    erewrite Forall2_length by exact H20.
    trivial. }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; try exact eq_refl.
  subst_to_affine.
  rewrite Jacobian.to_affine_of_affine.
  rewrite ScalarMult.scalarmult_zero_r.
  rewrite Hierarchy.left_identity.
  cbv [i].
  rewrite word.unsigned_of_Z_nowrap by lia.
  assert (Z.to_nat _ = length sscalar) as -> by lia.
  rewrite firstn_all.
  reflexivity.
Qed.

Lemma p256_point_mul_ok : program_logic_goal_for_function! p256_point_mul.
Proof.
  repeat straightline.
  (* Split stack into space for sscalar and padding. *)
  rewrite <-(firstn_skipn num_limbs stack) in H2.
  set (sscalar := ListDef.firstn num_limbs stack) in H2.
  set (padding := ListDef.skipn num_limbs stack) in H2.
  seprewrite_in Array.bytearray_append H2.
  assert (length sscalar = num_limbs).
  { unfold sscalar.
    rewrite length_firstn.
    lia. }
  rewrite H13 in H2.
  set (word.add a (word.of_Z (Z.of_nat _))) in H2.
  straightline_call. (* call limbs_unpack *)
  { (* Solve limbs_unpack assumptions. *)
    ssplit; try ecancel_assumption; try ZnWords.
    rewrite word.unsigned_of_Z_nowrap by lia.
    cbv [p256_group_order] in *.
    lia. }
  repeat straightline.
  straightline_call. (* call recode_wrap *)
  { (* Solve recode_wrap assumptions. *)
    ssplit; try ecancel_assumption; trivial.
    { ZnWords. }
    { rewrite H19.
      rewrite word.unsigned_of_Z_nowrap by lia.
      cbv [p256_group_order] in *.
      lia. }
    { Decidable.vm_decide. } }
  repeat straightline.
  straightline_call. (* call p256_point_mul_signed *)
  { ssplit; try ecancel_assumption; trivial; try ZnWords. }
  repeat straightline.
  (* Restore stack by combining scalar and padding. *)
  seprewrite_in_by (Array.bytearray_index_merge x0 padding) H23 ZnWords.
  assert (length (x0 ++ padding) = 56%nat).
  { rewrite length_app.
    cbv [padding].
    rewrite length_skipn.
    ZnWords. }
  repeat straightline.
  eexists _.
  ssplit; try ecancel_assumption; trivial.
  subst_to_affine.
  rewrite H24, <-H19.
  reflexivity.
Qed.
