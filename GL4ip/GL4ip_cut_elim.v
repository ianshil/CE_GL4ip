Require Import GL4ip_PSGL4ip_calcs.
Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import ddT.
Require Import gen_tacs.
Require Import gen_seq.
Require Import List_lemmasT.
Require Import existsT.
Require Import univ_gen_ext.
Require Import GL4ip_PSGL4ip_list_lems.
Require Import dd_fc.
Require Import PeanoNat.
Require Import strong_inductionT.
Require Import PSGL4ip_termination_measure.
Require Import PSGL4ip_termination.
Require Import GL4ip_exch.
Require Import GL4ip_ctr.
Require Import GL4ip_Id.
Require Import GL4ip_wkn.
Require Import GL4ip_inv_ImpL_R.
Require Import GL4ip_inv_AndImpL.
Require Import GL4ip_inv_OrImpL.
Require Import GL4ip_inv_AndR_AndL.
Require Import GL4ip_inv_AtomImpL.
Require Import GL4ip_inv_ImpImpL_R.
Require Import GL4ip_inv_ImpImpL_L.
Require Import GL4ip_inv_ImpR.
Require Import GL4ip_inv_OrL.
Require Import GL4ip_PSGL4ip_remove_list.
Require Import GL4ip_PSGL4ip_dec.
Require Import GL4ip_additive_cut.
Require Import Lia.

Inductive CutRule : rlsT (prod (list (MPropF V)) (MPropF V)) :=
  | CutRule_I : forall A C Γ0 Γ1,
          CutRule [(pair (Γ0 ++ Γ1) A) ; (pair (Γ0 ++ A :: Γ1) C)]
                    (pair (Γ0 ++ Γ1) C)
.

Inductive GL4ip_cut_rules : rlsT  (prod (list (MPropF V)) (MPropF V)) :=
  | GL4ip_woc : forall ps c, GL4ip_rules ps c -> GL4ip_cut_rules ps c
  | GL4ip_cut : forall ps c, CutRule ps c -> GL4ip_cut_rules ps c
.

Definition GL4ip_cut_prv s := derrec GL4ip_cut_rules (fun _ => False) s.

Theorem GL4ip_cut_elimination : forall s, (GL4ip_cut_prv s) -> (GL4ip_prv s).
Proof.
unfold GL4ip_cut_prv. unfold GL4ip_prv.
intros s D.
remember (derrec_height D) as n.
revert Heqn. revert D. revert s. revert n.
pose (strong_inductionT (fun (x:nat) => forall (s : list (MPropF V) * MPropF V)
(D : derrec GL4ip_cut_rules (fun _ : list (MPropF V) * MPropF V => False) s),
x = derrec_height D -> derrec GL4ip_rules (fun _ : list (MPropF V) * MPropF V => False) s)). apply d.
clear d. intros. destruct D. inversion f. inversion g.
- apply derI with (ps:=ps) ; auto. apply dersrec_forall. intros.  pose (dersrecD_forall_in_dersrec d H2).
  destruct s. apply X with (k:=derrec_height x) (D:=x) ; auto. apply dersrec_derrec_height_le in i. rewrite H. simpl. lia.
- subst. simpl in X. inversion H0. subst. assert (InT (Γ0 ++ Γ1, A) [(Γ0 ++ Γ1, A); (Γ0 ++ A :: Γ1, C)]). apply InT_eq.
  pose (dersrecD_forall_in_dersrec d H). destruct s. assert (InT (Γ0 ++ A :: Γ1, C) [(Γ0 ++ Γ1, A); (Γ0 ++ A :: Γ1, C)]). apply InT_cons. apply InT_eq.
  pose (dersrecD_forall_in_dersrec d H1). destruct s.
  apply GL4ip_cut_adm0 with (A:=A). apply X with (k:=derrec_height x) (D:=x) ; auto.
  apply dersrec_derrec_height_le in i. lia. apply X with (k:=derrec_height x0) (D:=x0) ; auto.
  apply dersrec_derrec_height_le in i0. lia.
Defined.