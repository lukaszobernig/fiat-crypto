From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section PolyCRT_Field.

Variable F : fieldType.
Implicit Types c : F.
Implicit Types p q : {poly F}.

Lemma contra_neq_iff : forall (T1 T2 : eqType) (x1 x2 : T1) (z1 z2 : T2), (x1 = x2 <-> z1 = z2) -> x1 != x2 <-> z1 != z2.
Proof.
  intros.
  by split; apply contra_neq, H.
Qed.

Lemma lead_coef_neq0 p : (lead_coef p != 0) <-> (p != 0).
Proof.
  apply contra_neq_iff.
  by split; intros; apply/eqP;
    [rewrite -lead_coef_eq0 | rewrite lead_coef_eq0];
    apply/eqP.
Qed.

Lemma polyC_neq0 c : (c%:P != 0) <-> (c != 0).
Proof.
  apply contra_neq_iff.
  by split; intros; apply/eqP;
    [rewrite -polyC_eq0 | rewrite polyC_eq0];
    apply/eqP.
Qed.

Lemma gcdp_neq0 p q : (gcdp p q != 0) <-> (p != 0) || (q != 0).
Proof.
  specialize (gcdp_eq0 p q).
  split;
    [apply contra_neqT | apply contraTneq];
    rewrite negb_or;
    rewrite !negbK;
    [move=> imp; apply/eqP | move/eqP=> imp];
  move: imp;
  rewrite H //.
Qed.

Lemma eqp_eq_iff p q: p != 0 -> q != 0 -> p %= q <-> (lead_coef q) *: p = (lead_coef p) *: q.
Proof.
  rewrite -lead_coef_neq0 => lcp_ne0.
  rewrite -lead_coef_neq0 => lcq_ne0.
  split.
    by apply eqp_eq.
  move=> H.
  apply/eqpP.
  exists (lead_coef q, lead_coef p).
    by apply/andP; split; trivial.
  by apply H.
Qed.

Lemma mul_inv_coef_l_eq1_iff c p : c != 0 -> (c^-1) *: p = 1 <-> p = c%:P.
Proof.
  move=> H.
  split.
    move=> H0.
    apply (@mulfI _ c%:P^-1).
      by rewrite polyCV polyC_neq0 invr_neq0.
    rewrite mulVr.
      by rewrite polyCV mul_polyC //.
    rewrite poly_unitE.
    apply/andP; split.
      by rewrite size_polyC H.
    by rewrite coefC /= unitfE.
  move=> H1.
  rewrite H1 scale_polyC mulVr //.
  by rewrite unitfE.
Qed.

(* For fields we normalise the GCD to be monic. *)
Definition gcdpf p q :=
  let g := gcdp p q in
    (lead_coef g)^-1 *: g.

Lemma gcdpf_eq1 p q : (p != 0) || (q != 0) -> (gcdpf p q = 1) <-> coprimep p q.
Proof.
  move=> poq_ne0.
  have gcd_pq_ne0 : (gcdp p q) != 0 by rewrite gcdp_neq0; apply poq_ne0.
  unfold gcdpf, coprimep.
  rewrite size_poly_eq1.
  rewrite (eqp_eq_iff gcd_pq_ne0).
    rewrite lead_coefC.
    rewrite mul_inv_coef_l_eq1_iff.
      rewrite alg_polyC.
      by rewrite scale1r.
    by rewrite lead_coef_neq0; apply gcd_pq_ne0.
  by apply oner_neq0.
Qed.

(* For fields we normalise the Bezout coefficients to sum to a monic GCD. *)
Definition egcdpf p q :=
  let e := egcdp p q in
    let c := lead_coef (e.1 * p + e.2 * q) in
      (c^-1 *: e.1, c^-1 *: e.2).

Lemma eqp1_ne0 p : (p %= 1) -> (p != 0).
Proof.
  unfold eqp.
  rewrite dvdp1 dvd1p andbT.
  by move/eqP => x; rewrite -size_poly_gt0 x.
Qed.

Lemma Bezout_ne0 p q (e := egcdp p q) : coprimep p q -> e.1 * p + e.2 * q != 0.
Proof.
  specialize (egcdpE p q). fold e. cbn [fst snd]. move=> gcd_eqn.
  rewrite eqp_sym in gcd_eqn.
  eapply eqp_trans in gcd_eqn.
  rewrite -gcdp_eqp1=> gcd_eq1.
  specialize (gcd_eqn gcd_eq1).
  by rewrite eqp1_ne0.
Qed.

Lemma egcdpf_eq1 p q (e := egcdpf p q) : (p != 0) || (q != 0) -> coprimep p q -> 1 = e.1 * p + e.2 * q.
Proof.
  move=> pq_ne0 co_pq.
  have gcdpf_p_q_eq1 : gcdpf p q = 1 by
    move: co_pq; rewrite -gcdpf_eq1.
  rewrite -gcdpf_p_q_eq1.

  unfold gcdpf, e, egcdpf.
  (*cbn [fst snd].*)

  set g := lead_coef (gcdp p q).

  have gcdp_pq_ne0 : gcdp p q != 0 by
    rewrite gcdp_neq0.
  have lcf_gcd_pq_ne0 : lead_coef (gcdp p q) != 0 by
    rewrite lead_coef_neq0.

  have bezout_ne0 : (egcdp p q).1 * p + (egcdp p q).2 * q != 0 by
    rewrite Bezout_ne0.
  have lcf_bezout_ne0 : lead_coef ((egcdp p q).1 * p + (egcdp p q).2 * q) != 0 by
    rewrite lead_coef_neq0.

  have g_unit : g%:P \is a GRing.unit.
  unfold g.
  rewrite poly_unitE.
  apply/andP.
  split.
    by rewrite size_polyC lcf_gcd_pq_ne0.
  by rewrite coefC /= unitfE.

  set x := lead_coef ((egcdp p q).1 * p + (egcdp p q).2 * q).

  have x_unit : x%:P \is a GRing.unit.
  unfold x.
  rewrite poly_unitE.
  apply/andP.
  split.
    by rewrite size_polyC lcf_bezout_ne0.
  by rewrite coefC /= unitfE.

  rewrite -!mul_polyC -!mulrA -mulrDr.

  apply (@mulrI _ g%:P g_unit).
  rewrite -polyCV mulrA (mulrV g_unit) mul1r.

  rewrite [RHS]mulrC.
  apply (@mulrI _ x%:P x_unit).
  rewrite -polyCV !mulrA (mulrV x_unit) mul1r.
  rewrite [RHS]mulrC.

  rewrite !mul_polyC.
  rewrite -(eqp_eq_iff gcdp_pq_ne0 bezout_ne0).

  apply (egcdpE p q).
Qed.

Variables m1 m2 : {poly F}.
Hypothesis nz_m1 : m1 != 0.
Hypothesis nz_m2 : m2 != 0.
Hypothesis co_m1_m2 : coprimep m1 m2.

(* Existence version of CRT for polynomials over fields. *)
Lemma poly_crtf r1 r2 :
  exists x, x %% m1 = r1 %% m1 /\ x %% m2 = r2 %% m2.
Proof.
  move: co_m1_m2; case/Bezout_eq1_coprimepP; move=> [u v] /= uv_eqn.
  exists (r1 * v * m2 + r2 * u * m1); split.
    by rewrite -{2}[r1]mulr1 -uv_eqn mulrDr addrC !mulrA !modpD !modp_mull.
  by rewrite -{2}[r2]mulr1 -uv_eqn mulrDr addrC !mulrA !modpD !modp_mull.
Qed.

Definition pchinese r1 r2 (e := egcdpf m1 m2) :=
  r1 * e.2 * m2 + r2 * e.1 * m1.

Lemma pchinese_modl r1 r2 : pchinese r1 r2 %% m1 = r1 %% m1.
Proof.
  rewrite /pchinese.
  have nz_m1_or_m2: (m1 != 0) || (m2 != 0) by rewrite nz_m1 nz_m2.
  have gcd_eqn := egcdpf_eq1 nz_m1_or_m2 co_m1_m2.
  by rewrite -{2}[r1]mulr1 gcd_eqn mulrDr addrC !mulrA !modpD !modp_mull.
Qed.

Lemma pchinese_modr r1 r2 : pchinese r1 r2 %% m2 = r2 %% m2.
Proof.
  rewrite /pchinese.
  have nz_m1_or_m2: (m1 != 0) || (m2 != 0) by rewrite nz_m1 nz_m2.
  have gcd_eqn := egcdpf_eq1 nz_m1_or_m2 co_m1_m2.
  by rewrite -{2}[r2]mulr1 gcd_eqn mulrDr addrC !mulrA !modpD !modp_mull.
Qed.

Lemma eqp_mod_dvd d p q : (p %% d == q %% d) = (d %| p - q).
Proof.
  apply/eqP/modp_eq0P => eq_pq.
    by rewrite modpD eq_pq -modpD subrr mod0p.
  by rewrite -(subrK q p) modpD eq_pq add0r.
Qed.

Lemma pchinese_remainder r1 r2 :
  (r1 %% (m1 * m2) == r2 %% (m1 * m2)) = (r1 %% m1 == r2 %% m1) && (r1 %% m2 == r2 %% m2).
Proof.
  by rewrite !eqp_mod_dvd Gauss_dvdp.
Qed.

Lemma pchinese_mod p : p %% (m1 * m2) == pchinese (p %% m1) (p %% m2) %% (m1 * m2).
Proof.
  rewrite pchinese_remainder pchinese_modl pchinese_modr !modp_mod.
  by apply/andP.
Qed.

End PolyCRT_Field.