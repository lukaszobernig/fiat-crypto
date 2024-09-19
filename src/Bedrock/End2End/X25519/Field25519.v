Require Import Crypto.Spec.Curve25519.
From Coq Require Import String. Local Open Scope string_scope.
From Coq Require Import List.
From Coq Require Import ZArith.
Require Import coqutil.Word.Bitwidth32.
Require Import coqutil.Macros.WithBaseName.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Field.Interface.Representation.
Require Import Crypto.Bedrock.Field.Synthesis.New.ComputedOp.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Translation.Parameters.FE310.
Require Import Crypto.Bedrock.Specs.Field.
Import ListNotations.

#[export]
Existing Instances Naive.word Naive.word32_ok BW32.
#[export]
Existing Instances SortedListWord.map SortedListWord.ok.

(* Parameters for Curve25519 field (32-bit machine). *)
Section Field.
  Context {ext_spec: Semantics.ExtSpec} {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Definition n : nat := 10.
  Definition s : Z := 2^255.
  Definition c : list (Z * Z) := [(1, 19)]%Z.

  Definition prefix : string := "fe25519_"%string.

  (* Note: Cannot use Defaults32.default_parameters here as the parameters for
     the bedrock2 backend because it uses BasicC32Semantics.ext_spec, while we
     will eventually want to plug in FE310CSemantics.ext_spec. TODO: is there a
     way to prove the ext_spec doesn't matter here, since we're not using any MMIO? *)
  (* Parameters for the fiat-crypto bedrock2 backend *)
  Instance translation_parameters : Types.parameters
    (varname_gen := default_varname_gen)
    (error := Syntax.expr.var Defaults.ERROR)
    := tt.
  Instance translation_parameters_ok : Types.ok.
  Proof using ext_spec_ok. constructor; try exact _; apply prefix_name_gen_unique. Qed.

  Instance field_parameters : FieldParameters :=
    field_parameters_prefixed Curve25519.p Curve25519.M.a24 "fe25519_"%string.

  (* Call fiat-crypto pipeline on all field operations *)
  Instance fe25519_ops : unsaturated_solinas_ops (ext_spec:=ext_spec) n s c.
  Proof using Type. Time constructor; make_computed_op. Defined.

  (**** Translate each field operation into bedrock2 and apply bedrock2 backend
        field pipeline proofs to prove the bedrock2 functions are correct. ****)

  Derive fe25519_from_bytes
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_from_bytes" = Some fe25519_from_bytes ->
      spec_of_from_bytes
        (ext_spec:=ext_spec)
        (field_representation:=field_representation n s c)
        functions)
    As fe25519_from_bytes_correct.
  Proof. Time derive_bedrock2_func from_bytes_op. Qed.

  Derive fe25519_to_bytes
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_to_bytes" = Some fe25519_to_bytes ->
      spec_of_to_bytes
        (field_representation:=field_representation n s c)
        functions)
    As fe25519_to_bytes_correct.
  Proof. Time derive_bedrock2_func to_bytes_op. Qed.

  Derive fe25519_copy
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_copy" = Some fe25519_copy ->
      spec_of_felem_copy
        (field_representation:=field_representation n s c)
        functions)
    As fe25519_copy_correct.
  Proof. Time derive_bedrock2_func felem_copy_op. Qed.

  Derive fe25519_from_word
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_from_word" = Some fe25519_from_word ->
      spec_of_from_word
        (field_representation:=field_representation n s c)
        functions)
    As fe25519_from_word_correct.
  Proof. Time derive_bedrock2_func from_word_op. Qed.

  Derive fe25519_mul
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_mul" = Some fe25519_mul ->
      spec_of_BinOp bin_mul
        (field_representation:=field_representation n s c)
        functions)
    As fe25519_mul_correct.
  Proof. Time derive_bedrock2_func mul_op. Qed.

  Derive fe25519_square
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_square" = Some fe25519_square ->
      spec_of_UnOp un_square
        (field_representation:=field_representation n s c)
        functions)
    As fe25519_square_correct.
  Proof. Time derive_bedrock2_func square_op. Qed.

  Derive fe25519_add
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_add" = Some fe25519_add ->
      spec_of_BinOp bin_add
        (field_representation:=field_representation n s c)
        functions)
    As fe25519_add_correct.
  Proof. Time derive_bedrock2_func add_op. Qed.

  Derive fe25519_carry_add
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_carry_add" = Some fe25519_carry_add ->
      spec_of_BinOp bin_carry_add
        (field_representation:=field_representation n s c)
        functions)
    As fe25519_carry_add_correct.
  Proof. Time derive_bedrock2_func carry_add_op. Qed.

  Derive fe25519_sub
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_sub" = Some fe25519_sub ->
      spec_of_BinOp bin_sub
        (field_representation:=field_representation n s c)
        functions)
    As fe25519_sub_correct.
  Proof. Time derive_bedrock2_func sub_op. Qed.

  Derive fe25519_carry_sub
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_carry_sub" = Some fe25519_carry_sub ->
      spec_of_BinOp bin_carry_sub
        (field_representation:=field_representation n s c)
        functions)
    As fe25519_carry_sub_correct.
  Proof. Time derive_bedrock2_func carry_sub_op. Qed.

  Derive fe25519_scmula24
    SuchThat (forall functions,
      Interface.map.get functions "fe25519_scmula24" = Some fe25519_scmula24 ->
      spec_of_UnOp un_scmula24
        (field_representation:=field_representation n s c)
        functions)
    As fe25519_scmula24_correct.
  Proof. Time derive_bedrock2_func scmula24_op. Qed.

  #[export] Instance frep25519_ok : FieldRepresentation_ok(field_representation:=field_representation n s c).
  Proof.
    apply Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation_ok.
    apply UnsaturatedSolinas.relax_valid.
  Qed.
End Field.
