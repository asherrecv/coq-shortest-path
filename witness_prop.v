Section GLOBAL_WITNESS_PROP.

Require Import List.
Require Import Arith Omega.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Le.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.
Require Import Bool.

Add LoadPath "/home/dash/Documents/diplom/coq/".
Load arg_min_inequ.
Load delta_func.

Variable g : graph.
Variable dist : set g.(V) -> nat.

Hypothesis Hpath_existence : path_existence g.

Definition delta := 
  proj1_sig (delta_existence g Hpath_existence).
Definition delta_ok := 
  proj2_sig (delta_existence g Hpath_existence).

Definition start_prop :=
  dist g.(s) = 0.
Definition trian_prop := forall u v, 
  g.(E) u v > 0 -> dist v <= dist u + g.(E) u v.
Definition justf_prop := forall v,
  v <> g.(s) -> exists u, g.(E) u v > 0 /\ dist v = dist u + g.(E) u v.

Hypothesis Hstart_prop : start_prop.
Hypothesis Htrian_prop : trian_prop.
Hypothesis Hjustf_prop : justf_prop.

Lemma dist_leq_delta : forall v, 
  dist v <= delta v.
Proof.
  intros v.
  assert (Hdelta : delta_prop g v (delta v)) by apply delta_ok.
  unfold delta_prop in Hdelta.
  destruct Hdelta as [p HSP_v].
  unfold shortest_path in HSP_v.
  destruct HSP_v as [HP_v HSP_v].
  set (tmp_s := g.(s)) in *.
  assert (H_s : tmp_s = g.(s)) by reflexivity.
  induction HP_v.
  rewrite H_s.
  rewrite Hstart_prop.
  auto.
  assert (HE := H).
  apply shortest_path_opt_substructure 
    with (p := p) (d := d) in H.
  subst.
  unfold shortest_path in H.
  destruct H as [HP_up HSP_up].
  apply IHHP_v in HSP_up.
  apply Htrian_prop in HE.
  omega.
  reflexivity.
  unfold shortest_path.
  split.
  apply consp.
  assumption.
  rewrite <- H_s.
  assumption.
  rewrite <- H_s.
  assumption.
Qed.

Lemma dist_geq_delta : forall v,
  dist v >= delta v.
Proof.
  intros v.
     
  (** assume that dists v < delta v for some v **)
  destruct (classic (dist v >= delta v)) as [B|B].
  apply B.
  exfalso.
  apply not_ge in B.

  (** among all v with dists v < delta v, there
    * must be a v' s.t. the inequality is fulfilled
    * and dists(v) is minimal **)
  apply arg_min_inequality in B.

  (** instantiate v' and the shortest path p to v' **)
  destruct B as [v' [B C]].
  assert (D : delta_prop g v' (delta v')).
  apply delta_ok.
  unfold delta_prop in D.
  destruct D as [p D].
  
  (** from the assumption v' = sv derive a contradiction
    * so that we know that v' <> sv **)     
  destruct (classic (v' = g.(s))) as [E|E].
  exfalso.
  subst.
  rewrite Hstart_prop in B.
  assert (E : delta g.(s) = 0).
  assert (F : shortest_path g (g.(s)::nil) g.(s) g.(s) 0).
  split.
  apply zerop.
  intros.
  omega.
  destruct F as [G H].
  destruct D as [I J].
  destruct I.
  reflexivity.
  apply J in G.
  omega.
  omega.

  (** now that we know that v' <> startv we can use the
    * justification property to get an justifying edge 
    * (u, v) to v **)
  apply Hjustf_prop in E.
  destruct E as [u [E G]].

  (** dists u < dists v' since edge weights are positive **)
  assert (H : dist u < dist v').
  omega.

  (** with dists u < dists v' and the choice of v' we 
    * know that dists u >= delta u **)
  apply C in H.

  (** further we know from the lemma above that
    * dist u <= delta u **)
  assert (I : dist u <= delta u).
  apply dist_leq_delta.
  
  (** together dists u = delta u **)
  assert (J : dist u = delta u).
  omega.
  
  (** with the justifying edge (u, v') we can construct
   * a path to v' of cost dist u + c(u, v') **)
  assert (K : delta_prop g u (delta u)).
  apply delta_ok.
  unfold delta_prop in K.
  destruct K as [p' K].
  destruct K as [K L].
  assert (P := E).
  apply lastv_auxilary in K.
  destruct K as [p'' K].
  apply consp with (p := p'') (sv := g.(s)) (d := (dist u)) in E.
  destruct D as [M N]. 
  apply N in E.
  subst. 
  rewrite G in B.
  rewrite J in G.

  (** with this above constructed path we can derive a 
    * contradiction **)
  assert (E' := E).
  clear E.
  rewrite <- J in G.
  rewrite <- G in B.
  omega.
  rewrite J.
  apply K.
Qed.

Theorem dist_eq_delta : forall v,
  dist v = delta v.
Proof.
  intro v.
  apply le_antisym.
  apply dist_leq_delta.
  apply dist_geq_delta.
Qed.

End GLOBAL_WITNESS_PROP.

Check dist_eq_delta.

Check dist_eq_delta.


Section LOCAL_WITNESS_PROP.

Variable n : nat.

Record component : Set := mk_component {
  is_s  : bool;
  i     : (set n);             
  E_i   : (set n) -> nat
}.

Variable dist : set n -> nat.

Definition local_start_prop (c : component) : Prop :=
  dist c.(i) = 0.

Definition local_trian_prop (c : component) : Prop :=
  forall j, c.(E_i) j > 0 -> dist c.(i) <= dist j + c.(E_i) j.

Definition local_justf_prop (c : component) : Prop :=
  exists j, c.(E_i) j > 0 /\ dist c.(i) = dist j + c.(E_i) j.

Definition local_witness (c : component) : Prop :=
  (c.(is_s) = true -> local_start_prop c /\ local_trian_prop c) /\ 
  (c.(is_s) = false -> local_trian_prop c /\ local_justf_prop c).

Axiom get : 
  (set n) -> component.
Axiom get_ok :
  forall c_i, (get c_i).(i) = c_i.

Variable start_i : 
  (set n).
Definition start_component_knowledge :=
  (get start_i).(is_s) = true.

Definition start_component_unique :=
  forall c, c <> (get start_i) -> c.(is_s) = false.
Definition lw_conjunction := forall c, 
  local_witness (get c).

Variable Hstart_component_knowledge :
  start_component_knowledge.
Variable Hstart_component_unique :
  start_component_unique.
Variable Hlw_conjunction : lw_conjunction.


Definition network_E (i : (set n))(j : (set n)) : nat :=
  (get j).(E_i) i.

Definition network_g : graph := mk_graph n network_E (get start_i).(i).

Lemma global_start_prop : dist network_g.(s) = 0.
Proof.
  assert (A : local_witness (get start_i)).
  apply Hlw_conjunction.
  unfold local_witness in A.
  destruct A as [A _].
  assert (B := Hstart_component_knowledge).
  apply A in B.
  destruct B as [B _].
  unfold local_start_prop in B.
  assert (D : network_g.(s) = (get start_i).(i)).
  auto.
  rewrite D.
  apply B.
Qed.

Lemma global_trian_prop : forall u v, 
  network_g.(E) u v > 0 -> dist v <= dist u + network_g.(E) u v.
Proof.
  intros.
  assert (A : local_witness (get v)).
  apply Hlw_conjunction.
  unfold local_witness in A.
  destruct (classic (is_s (get v) = true)) as [B|B].
  destruct A as [A _].
  apply A in B.
  destruct B as [_ B].
  unfold local_trian_prop in B.
  simpl in H.
  unfold network_E in H.
  apply B in H.
  simpl.
  unfold network_E.
  assert (C : (get v).(i) = v).
  apply get_ok.
  rewrite C in H.
  apply H.
  destruct A as [_ A].
  apply not_true_is_false in B.
  apply A in B.
  destruct B as [B _].
  unfold local_trian_prop in B.
  simpl in H.
  unfold network_E in H.
  apply B in H.
  simpl.
  assert (C : (get v).(i) = v).
  apply get_ok.
  rewrite C in H.
  apply H.
Qed.

Lemma distinct : forall c_i c_j, 
  c_i <> c_j -> get c_i <> get c_j.
Proof.
  intros c_i c_j A.
  assert (B : (get c_i).(i) = c_i).
  apply get_ok.
  assert (C : (get c_j).(i) = c_j).
  apply get_ok.
  rewrite <- B in A.
  rewrite <- C in A.
  destruct (classic (get c_i = get c_j)) as [D|D].
  assert (E : (get c_i).(i) = (get c_j).(i)).
  f_equal.
  apply D.
  tauto.
  apply D.
Qed.

Lemma global_justf_prop : forall v, 
  v <> network_g.(s) ->
    exists u, network_g.(E) u v > 0 /\ dist v = dist u + network_g.(E) u v.
Proof.
  intros.
  assert (A : local_witness (get v)).
  apply Hlw_conjunction.
  unfold local_witness in A.
  destruct A as [_ A].
  assert (B : is_s (get v) = false).
  apply Hstart_component_unique.
  simpl in H.
  rewrite get_ok in H.
  apply distinct.
  apply H.
  apply A in B.
  destruct B as [_ B].
  unfold local_justf_prop in B.
  rewrite get_ok in B.
  apply B.
Qed.

Variable Hpath_existence : path_existence network_g.
Definition delta_network_g := 
  proj1_sig (delta_existence network_g Hpath_existence).
Definition delta_network_ok := 
  proj2_sig (delta_existence network_g Hpath_existence).

Theorem dist_eq_network_delta : forall (v : set network_g.(V)),
  dist v = delta_network_g v.
Proof.
  apply dist_eq_delta.
  apply global_start_prop.
  unfold trian_prop.
  apply global_trian_prop.
  unfold justf_prop.
  apply global_justf_prop.
Qed.


Definition start_check(c : component) :=
  andb c.(is_s) (beq_nat (dist c.(i)) 0).
(*
Fixpoint ble_nat (n m : nat) : bool :=
match n with
| O    => true
| S n' => match m with
          | O => false
          | S m' => ble_nat n' m'
          end
end.

Definition blt_nat (n m : nat) : bool :=
  andb (ble_nat n m) (negb (beq_nat n m)).
Check proj1_sig.
Check exist.

Lemma test : forall x y, S x < y -> x < y.
intros.
omega.
Qed.

Fixpoint check_trian(c : component)(j : set n) :=
match j with
| exist O pf => 
            orb 
             (negb 
               (blt_nat 0 (c.(E_i) j)))
             (ble_nat (dist c.(i)) (dist j + c.(E_i) j))
| exist (S j') pf => 
             andb
             (orb 
               (negb 
                 (blt_nat 0 (c.(E_i) j)))
               (ble_nat (dist c.(i)) (dist j + c.(E_i) j)))
             (check_trian 
              c 
              (exist 0 pf))
end.



c.(E_i) j > 0 -> dist c.(i) <= dist j + c.(E_i) j.
*)
  

End LOCAL_WITNESS_PROP.

Extraction start_check.
Extraction component.
Extraction set.

Check dist_eq_network_delta.