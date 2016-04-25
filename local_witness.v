Section LOCAL_WITNESS.

Add LoadPath "/home/dash/Documents/diplom/coq/".
Load witness_prop.

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

End LOCAL_WITNESS.