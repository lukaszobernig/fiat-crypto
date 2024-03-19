From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section NTT.

Variable F : fieldType.
Variable w : F.

(* https://github.com/thery/mathcomp-extra/blob/master/fft.v#L41 *)
Lemma prim_exp2nS n : (2 ^ n.+1).-primitive_root w -> w ^+ (2 ^ n) = -1.
Proof.
  move=> H; have /prim_expr_order/eqP := H.
  rewrite expnS mulnC exprM sqrf_eq1 => /orP[]/eqP // /eqP.
  by rewrite -(prim_order_dvd H) dvdn_Pexp2l // ltnn.
Qed.

(* Helper lemma. *)
Lemma nat_add_lt : forall a b, (a + b < b)%N = false.
Proof.
  move=> a b.
  elim: b => [|b IHb] //.
  by rewrite addnS /IHb.
Qed.

(* The modulus we use. *)
Definition modulus (k l : nat) :=
  'X^(2^k) - (w ^+ (2^k) ^+ l)%:P.

(* The modulus is a monic polynomial. *)
Lemma modulus_monic (k l : nat) :
  modulus k l \is monic.
Proof.
  unfold modulus.
  rewrite monicE lead_coefDl.
  by rewrite lead_coefXn.
  rewrite size_polyXn size_opp size_polyC.
  case: ((w ^+ (2 ^ k) ^ l)%R != 0) => /=.
  by rewrite -(addn1 (2^k)) -{1}(add0n 1%N) ltn_add2r expn_gt0.
  by rewrite ltn0Sn.
Qed.

(* Monic implies that the modulus is nonzero. *)
Lemma modulus_nonzero (k l : nat) :
  modulus k l != 0.
Proof.
  have: modulus k l \is monic by
    rewrite modulus_monic.
  apply monic_neq0.
Qed.

(* The degree equals 2^k. *)
Lemma modulus_size (k l : nat) : size (modulus k l) = (2^k).+1.
Proof.
  unfold modulus.
  rewrite size_addl.
  by rewrite size_polyXn.
  rewrite size_polyXn size_opp size_polyC.
  case: ((w ^+ (2 ^ k) ^ l)%R != 0) => /=.
  by rewrite -(addn1 (2^k)) -{1}(add0n 1%N) ltn_add2r expn_gt0.
  by rewrite ltn0Sn.
Qed.

Section WithMAndWPrimRoot.

Context
  (m : nat)
  (m_positive : (0 < m)%N).
Context (w_2m_primroot : (2^m).-primitive_root w).

  Section InductiveCase.

  Context
    (rec_ntt : nat->nat->{poly F}->seq F)
    (rec_idx : nat->nat->nat)
    (k' l i : nat)
    (k := k'.+1)
    (p : {poly F}).
  Let m1 := modulus k' l.
  Let m2 := modulus k' (l + 2^(m - k)).
  Let p1 := p %% m1.
  Let p2 := p %% m2.
  Let lhs := rec_ntt k' l p1.
  Let rhs := rec_ntt k' (l + (2^(m - k)))%N p2.
  Definition ntt_body' := lhs ++ rhs.
  Let idx' := rec_idx k' i./2.
  Definition idx_body' :=
    if odd i then (idx' + 2^k')%N else idx'.

  Context (k_bounded_m : (k <= m)%N).
  Context (k_positive : (0 < k)%N).
  Context (h_idx_bounded : forall i, (rec_idx k' i < 2^k')%N).
  Context (h_size_rec_ntt : forall l p, (size (rec_ntt k' l p) = 2^k')%N).
  Context (h_rec_ntt :
    forall i l (p : {poly F}) (e := (i*2^(m - k') + l)%N),
      (k' <= m)%N -> (size p < (2^k').+1)%N -> p.[w ^+ e] = nth w (rec_ntt k' l p) (rec_idx k' i)
  ).

  (* This also implies m1 and m2 coprime. *)
  Let a := w ^+ (2 ^ k') ^ l.
  Let b := w ^+ (2 ^ k') ^ (l + 2 ^ (m - k))%N.
  Let u := (b - a)^-1.
  Let v := (a - b)^-1. (* v = -u. *)
  Lemma linear_relation_m1_m2 : u%:P * m1 + v%:P * m2 = 1.
  Proof.
    unfold m1, m2, modulus.
    fold a.
    fold b.
  Admitted.

  Lemma coprime_m1_m2 : coprimep m1 m2.
  Proof.
    apply/(Bezout_eq1_coprimepP m1 m2).
    exists (u%:P, v%:P).
    apply linear_relation_m1_m2.
  Qed.

  Definition egcdpf (p q : {poly F}) := let e := egcdp p q in let c := lead_coef (e.1 * p + e.2 * q) in (c^-1 *: e.1, c^-1 *: e.2).
  Definition pchinese r1 r2 (e := egcdpf m1 m2) := r1 * e.2 * m2 + r2 * e.1 * m1.
  Lemma pchinese_mod (r : {poly F}) : r %% (m1 * m2) == pchinese (r %% m1) (r %% m2) %% (m1 * m2). Admitted.

  Lemma modulus_split : (modulus k l) = (modulus k' l) * (modulus k' (l + 2^(m - k))). Admitted.

  Lemma hCRT : exists (u v : {poly F}), p = p1 * v * m2 + p2 * u * m1. Admitted.
  Lemma hCRT1 : exists (u : {poly F}), p = p1 + (p2 - p1) * u * m1. Admitted.
  Lemma hCRT2 : exists (v : {poly F}), p = p2 + (p1 - p2) * v * m2. Admitted.

  Lemma def_k : (k' = k - 1)%N.
  Proof.
    unfold k.
    by rewrite -addn1 addnK.
  Qed.

  Lemma w_neg1 : w ^+ (2 ^ (m - 1)) = -1.
  Proof.
    apply prim_exp2nS.
    rewrite subn1 prednK //.
  Qed.

  Lemma w_even_odd : if odd i then
    w ^+ (i * 2 ^ (m - 1)) = -1 else
    w ^+ (i * 2 ^ (m - 1)) = 1.
  Proof.
    case odd eqn:h; rewrite mulnC exprM w_neg1 -signr_odd h //.
  Qed.

  Let e := (i*2^(m - k) + l)%N.
  Lemma zero_even_odd : if odd i then m2.[w ^+ e] = 0 else m1.[w ^+ e] = 0.
  Proof.
    pose proof w_even_odd.
    unfold m1, m2, modulus, e.
    case odd eqn:h; rewrite !hornerE def_k -!exprM mulnDl -mulnA.
    {
      rewrite mulnDr (mulnC (2 ^ (k - 1))%N l) (mulnC (2 ^ (k - 1))%N (2 ^ (m - k))%N).
      rewrite -!expnD !addnBA.
      rewrite !subnK.
      by rewrite !exprD mulrC w_neg1 H addrN.
      apply k_bounded_m.
      apply k_positive.
    }
    {
      rewrite -expnD addnBA.
      rewrite subnK.
      by rewrite (mulnC (2 ^ (k - 1))%N l) exprD H mul1r addrN.
      apply k_bounded_m.
      apply k_positive.
    }
  Qed.

  Lemma p_eval_w_p1_p2 :
    p.[w ^+ e] = if odd i then p2.[w ^+ e] else p1.[w ^+ e].
  Proof.
    pose proof zero_even_odd as mi_eval_0.
    case odd eqn:h;
      [specialize hCRT2; move=> [q hCRT2]; rewrite hCRT2 |
       specialize hCRT1; move=> [q hCRT1]; rewrite hCRT1];
      by rewrite hornerD !hornerM mi_eval_0 mulr0 addr0.
  Qed.

  Lemma size_p_mod_modulus : forall k l, (size (modp p (modulus k l)) < (2^k).+1)%N.
  Proof.
    move=> r s.
    have: (size (modp p (modulus r s)) < (size (modulus r s)))%N by
      rewrite ltn_modp modulus_nonzero.
    by rewrite modulus_size.
  Qed.

  Lemma kp_bounded_m : (k' <= m)%N.
  Proof.
    rewrite def_k subn1.
    move: k_bounded_m.
    have: (k.-1 <= k)%N by apply leq_pred.
    apply leq_trans.
  Qed.

  Lemma id_even : odd i = false -> (i * 2 ^ (m - k))%N =
    (i./2 * 2 ^ (m - k'))%N.
  Proof.
    intros.
    rewrite def_k (subnCBA _ k_positive) -(addnBA _ k_bounded_m).
    by rewrite add1n expnS mulnA muln2 even_halfK // H.
  Qed.

  Lemma id_odd : odd i = true -> (i * 2 ^ (m - k) + l)%N =
    (i./2 * 2 ^ (m - k') + (l + 2 ^ (m - k)))%N.
  Proof.
    intros.
    rewrite def_k (subnCBA _ k_positive) -(addnBA _ k_bounded_m).
    rewrite add1n expnS mulnA muln2 odd_halfK //.
    rewrite -subn1 mulnBl mul1n (addnC l _) addnA.
    nat_congr.
    rewrite addnBAC.
    rewrite -addnBA.
    by rewrite subnn addn0.
    trivial.
    case i eqn:h.
    by []. (* Contradiction with i being odd. *)
    by rewrite -(addn1 n) mulnDl mul1n leq_addl.
  Qed.

  Lemma p_eval_w_ntt :
    p.[w ^+ e] = nth w ntt_body' idx_body'.
  Proof.
    rewrite p_eval_w_p1_p2.
    unfold ntt_body', idx_body', idx'.
    rewrite nth_cat.
    case odd eqn:h; rewrite h_size_rec_ntt.
    {
      rewrite addnK.
      case (_ < 2 ^ k')%N eqn:hh.
      by rewrite nat_add_lt in hh.
      unfold rhs, e.
      rewrite -(h_rec_ntt _ _ kp_bounded_m).
      do 2 f_equal.
      rewrite id_odd //.
      apply size_p_mod_modulus.
    }
    {
      rewrite h_idx_bounded.
      unfold lhs, e.
      rewrite -(h_rec_ntt _ _ kp_bounded_m).
      do 2 f_equal.
      rewrite id_even //.
      apply size_p_mod_modulus.
    }
  Qed.

  End InductiveCase.

Definition ntt_body rec_ntt (k l : nat) (p : {poly F}) : seq F :=
  if k is k'.+1 then
    ntt_body' rec_ntt k' l p
  else
    [:: p`_0].

Definition idx_body rec_idx (k i :nat) : nat :=
  if k is k'.+1 then
    idx_body' rec_idx k' i
  else
    0.

Fixpoint ntt k l p := ntt_body ntt k l p.

Fixpoint idx k i := idx_body idx k i.

Lemma size_ntt :
  forall k l (p : {poly F}), (size (ntt k l p) = 2^k)%N.
Proof.
  induction k; cbn [ntt ntt_body]; intros.
  trivial.
  unfold ntt_body'.
  by rewrite size_cat !IHk addnn -(addn1 k) expnD expn1 muln2.
Qed.

Lemma idx_bounded :
  forall k i, (idx k i < 2^k)%N.
Proof.
  induction k; cbn [idx idx_body]; intros; trivial.
  unfold idx_body'.
  case odd eqn:h; rewrite -(addn1 k) expnD expn1 muln2; rewrite -addnn.
  by rewrite ltn_add2r.
  by rewrite ltn_addr.
Qed.

Lemma ntt_correct :
  forall k i l (p : {poly F}), (k <= m)%N -> (size p < (2^k).+1)%N ->
  p.[w ^+ (i*2^(m - k) + l)] = nth w (ntt k l p) (idx k i).
Proof.
  induction k; cbn [ntt idx ntt_body idx_body]; intros.
  rewrite nth0 /head subn0 horner_coef.
  case size_p : size H0 => [|[]] // _.
  by rewrite big_ord0 -[p]coefK size_p poly_def big_ord0 coefC.
  by rewrite big_ord1 expr0 mulr1.
  rewrite -p_eval_w_ntt //.
  apply idx_bounded.
  apply size_ntt.
Qed.

End WithMAndWPrimRoot.

(*Compute mkseq Nat.div2 8.
Compute mkseq (idx 3) 8.*)

End NTT.
