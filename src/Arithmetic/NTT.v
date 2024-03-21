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
  Context (size_p_bounded : (size p < (2^k).+1)%N).
  Context (h_idx_bounded : forall i, (rec_idx k' i < 2^k')%N).
  Context (h_size_rec_ntt : forall l p, (size (rec_ntt k' l p) = 2^k')%N).
  Context (h_rec_ntt :
    forall i l (p : {poly F}) (e := (i*2^(m - k') + l)%N),
      (k' <= m)%N -> (size p < (2^k').+1)%N -> p.[w ^+ e] = nth w (rec_ntt k' l p) (rec_idx k' i)
  ).

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

  Lemma kp_msubk : (2 ^ (k - 1) * 2 ^ (m - k) = 2 ^ (m - 1))%N.
  Proof.
    rewrite (mulnC (2 ^ (k - 1))%N (2 ^ (m - k))%N).
    by rewrite -!expnD !addnBA // subnK.
  Qed.

  Ltac r := repeat rewrite ?polyCN ?mulrDl ?mulrDr ?mulrN1 ?mulN1r ?mulrNN ?mulrN ?mulNr ?mulr1 -?exprD ?opprK ?addrA ?addrK.
  Lemma modulus_split : m1 * m2 = (modulus k l).
  Proof.
    unfold m1, m2, modulus.
    rewrite def_k; r.

    assert ((2 ^ (k - 1) + 2 ^ (k - 1) = 2^k)%N) as ->.
    by rewrite addnn -muln2 mulnC -def_k expnS.

    assert (
      w ^+ (2 ^ (k - 1)) ^+ (l + 2 ^ (m - k)) =
      - w ^+ (2 ^ (k - 1)) ^+ l) as ->. (* using w_neg1 *)
    rewrite -exprM mulnDr.
    rewrite kp_msubk.
    rewrite exprD mulrC w_neg1 mulN1r.
    by rewrite exprM.

    rewrite ?(mulrC _ ('X^_)); r.
    do 2 f_equal.
    by rewrite -polyCM -exprD -!exprM addnn -muln2 mulnA mulnC -def_k expnS mulnA.
  Qed.

  Lemma linear_relation (a b : F) (n : nat) : a - b != 0 -> (b - a)^-1 *: ('X^n - a%:P) + (a - b)^-1 *: ('X^n - b%:P) = 1.
  Proof.
    intros.
    have abneq0 : (a - b)%:P != 0 by
      rewrite polyC_eq0 H.
    have baneq0 : (b - a)%:P != 0 by
      rewrite -opprB polyC_eq0; move: H; rewrite -unitfE -unitrN unitfE.

    rewrite -!mul_polyC.

    apply (@mulfI _ (a - b)%:P abneq0).
    apply (@mulfI _ (b - a)%:P baneq0).

    r; rewrite !mulrA ?(mulrC _ ('X^_)).
    rewrite -!polyCM.
    rewrite mulfK.

    rewrite ?(mulrC _ (a - b)).
    rewrite mulfK.

    rewrite -(opprB a b).
    rewrite (addrC ('X^n * (a - b)%:P)).
    r; rewrite -polyCN -polyCD !opprB !addrA.

    rewrite !polyCD.

    rewrite ?(addrC _ ((- (a * a))%:P)) ?(addrC _ ((a * b)%:P)) !addrA ?(addrC _ ((b * a)%:P)) !addrA ?(addrC _ ((- (b * b))%:P)) //.

    by move: H; rewrite -opprB -unitfE -unitrN unitfE.
    by apply H.
  Qed.

  Let a := w ^+ (2 ^ k') ^+ l.
  Let b := w ^+ (2 ^ k') ^+ (l + 2 ^ (m - k))%N.
  Let u := (b - a)^-1.
  Let v := (a - b)^-1. (* v = -u. *)
  Lemma linear_relation_m1_m2 : u%:P * m1 + v%:P * m2 = 1.
  Proof.
    rewrite !mul_polyC linear_relation //.
    unfold a, b.
    rewrite def_k.
    rewrite -!exprM mulnDr exprD kp_msubk w_neg1 mulrN1 opprK.
    rewrite -(mulr1 (w ^+ (2 ^ (k - 1) * l))) -mulrDr.
    apply mulf_neq0.
    apply expf_neq0.
    admit.
    admit.
  Admitted.

  Lemma coprime_m1_m2 : coprimep m1 m2.
  Proof.
    apply/(Bezout_eq1_coprimepP m1 m2).
    exists (u%:P, v%:P).
    apply linear_relation_m1_m2.
  Qed.

  (* **************** *)
  Let crt_p := p1 * v%:P * m2 + p2 * u%:P * m1.

  Lemma crt_p_size : (size crt_p < (2^k).+1)%N.
  Proof.
    (* size mi = (2^k').+1 and size pi < size mi. *)
    have s1: (size (p1 * v%:P * m2)%R < (2^k).+1)%N. admit.
    have s2: (size (p2 * u%:P * m1)%R < (2^k).+1)%N. admit.
    unfold crt_p.
    have: (maxn (size (p1 * v%:P * m2)%R) (size (p2 * u%:P * m1)%R) < (2^k).+1)%N.
      unfold maxn.
      case: (size (p1 * v%:P * m2)%R < size (p2 * u%:P * m1)%R)%N => //.
    specialize (size_add (p1 * v%:P * m2) (p2 * u%:P * m1)).
    apply leq_ltn_trans.
  Admitted.

  Lemma crt_p_modl : crt_p %% m1 = p1 %% m1.
  Proof.
    unfold crt_p.
    by rewrite -{2}[p1]mulr1 -linear_relation_m1_m2 (mulrDr p1) addrC !mulrA !modpD !modp_mull.
  Qed.

  Lemma crt_p_modr : crt_p %% m2 = p2 %% m2.
  Proof.
    unfold crt_p.
    by rewrite -{2}[p2]mulr1 -linear_relation_m1_m2 (mulrDr p2) addrC !mulrA !modpD !modp_mull.
  Qed.

  Lemma eqp_mod_dvd (d r s : {poly F}) : (r %% d == s %% d) = (d %| r - s).
  Proof.
    apply/eqP/modp_eq0P => eq_rs.
      by rewrite modpD eq_rs -modpD subrr mod0p.
    by rewrite -(subrK s r) modpD eq_rs add0r.
  Qed.

  Lemma rem_m1_m2 (r s : {poly F}) : (r %% (m1 * m2) == s %% (m1 * m2)) = (r %% m1 == s %% m1) && (r %% m2 == s %% m2).
  Proof.
    by rewrite !eqp_mod_dvd (Gauss_dvdp _ coprime_m1_m2).
  Qed.

  Lemma crt_p_mod : p %% (m1 * m2) == crt_p %% (m1 * m2).
  Proof.
    rewrite rem_m1_m2 crt_p_modl crt_p_modr !modp_mod.
    by apply/andP.
  Qed.

  Lemma p_decomp : p = p1 * v%:P * m2 + p2 * u%:P * m1.
  Proof.
    specialize crt_p_mod.
    rewrite modulus_split.
    rewrite modp_small.
    rewrite modp_small.
    move/eqP=> H.
    by apply H.
    rewrite modulus_size.
    by apply crt_p_size.
    by rewrite modulus_size.
  Qed.

  Lemma p_decomp_m1 : p = p1 + (p2 - p1) * u%:P * m1.
  Proof.
    have eq : v%:P * m2 = 1 - u%:P * m1 by
      apply (@addIr _ (u%:P * m1));
      rewrite subrK addrC linear_relation_m1_m2.
    specialize p_decomp.
    rewrite -(mulrA p1) eq (mulrDr p1) mulr1 -(mulrA p2).
    move=> H.
    rewrite -mulrA mulrDl -mulrN1 -(mulrA p1) mulN1r addrC -addrA -(addrC p1) addrC.
    by apply H.
  Qed.

  Lemma p_decomp_m2 : p = p2 + (p1 - p2) * v%:P * m2.
  Proof.
    have eq : u%:P * m1 = 1 - v%:P * m2 by
      apply (@addIr _ (v%:P * m2));
      rewrite subrK linear_relation_m1_m2.
    specialize p_decomp.
    rewrite -(mulrA p2) eq (mulrDr p2) mulr1 -(mulrA p1).
    move=> H.
    rewrite -mulrA mulrDl -mulrN1 -(mulrA p2) mulN1r addrC -addrA -(addrC p2).
    by apply H.
  Qed.

  (* **************** *)

  (* **************** *)
  (*Definition egcdpf (p q : {poly F}) := let e := egcdp p q in let c := lead_coef (e.1 * p + e.2 * q) in (c^-1 *: e.1, c^-1 *: e.2).
  Definition pchinese r1 r2 (e := egcdpf m1 m2) := r1 * e.2 * m2 + r2 * e.1 * m1.
  Lemma pchinese_mod (r : {poly F}) : r %% (m1 * m2) == pchinese (r %% m1) (r %% m2) %% (m1 * m2). Admitted.
  Lemma size_ecgdpf_m1_m2 : (size (egcdp m1 m2).1 = 1)%N /\ (size (egcdp m1 m2).2 = 1)%N. Admitted. (* Needs this assumption. *)
  Lemma hCRT : exists (u v : {poly F}), p = p1 * v * m2 + p2 * u * m1.
  Proof.
    specialize (pchinese_mod p).
    rewrite modulus_split.
    rewrite modp_small.
    rewrite modp_small.
    unfold pchinese.
    move/eqP=> H.
    exists (egcdpf m1 m2).1, (egcdpf m1 m2).2.
    apply H.
    rewrite modulus_size.
    unfold pchinese.
    fold p1 p2.
    admit.
    rewrite modulus_size //.
  Admitted.
  Lemma hCRT1 : exists (u : {poly F}), p = p1 + (p2 - p1) * u * m1. Admitted.
  Lemma hCRT2 : exists (v : {poly F}), p = p2 + (p1 - p2) * v * m2. Admitted.*)
  (* [specialize p_decomp_m2; move=> [q hCRT2]; rewrite hCRT2 | specialize p_decomp_m1; move=> [q hCRT1]; rewrite hCRT1] *)
  (* **************** *)

  Let e := (i*2^(m - k) + l)%N.
  Lemma zero_even_odd : if odd i then m2.[w ^+ e] = 0 else m1.[w ^+ e] = 0.
  Proof.
    pose proof w_even_odd.
    unfold m1, m2, modulus, e.
    case odd eqn:h; rewrite !hornerE def_k -!exprM mulnDl -mulnA.
    {
      rewrite mulnDr (mulnC (2 ^ (k - 1))%N l) (mulnC (2 ^ (k - 1))%N (2 ^ (m - k))%N).
      rewrite -!expnD !addnBA // !subnK //.
      by rewrite !exprD mulrC w_neg1 H addrN.
    }
    {
      rewrite -expnD addnBA // subnK //.
      by rewrite (mulnC (2 ^ (k - 1))%N l) exprD H mul1r addrN.
    }
  Qed.

  Lemma p_eval_w_p1_p2 :
    p.[w ^+ e] = if odd i then p2.[w ^+ e] else p1.[w ^+ e].
  Proof.
    pose proof zero_even_odd as mi_eval_0.
    case odd eqn:h;
      [rewrite p_decomp_m2 | rewrite p_decomp_m1];
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

End NTT.
