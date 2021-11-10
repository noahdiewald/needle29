(* Bifurcated Dyn- similar to Dyn.v, but with contents being relations between contexts and bifurcated contexts to model CI's *)

(* update static semantics? *)
Load THS.
Load Vect.
Declare Scope bdyn_scope.
Open Scope bdyn_scope.

Notation "'e^' n" := (Vect e n) (at level 0) : vect_scope.

Definition con : nat -> Set := fun n : nat => e^n -> prop.
Definition bcon: nat -> Set := fun n : nat => e^n -> prop*prop.

Definition kon    : nat -> Type := fun i : nat => forall n : nat, con n -> bcon (n+i) -> Prop.
Definition update : nat -> Type := fun i : nat => forall n : nat, con n ->  con (n+i) -> Prop.

Definition p_i : nat -> Type := fun n : nat => prd n e prop.
(* m for # of entities introduced, n for arity *)
Definition dy  : nat -> nat -> Type := fun m n : nat => prd n nat (kon m).

Definition pex : p_i 1 -> prop := p_exists ent.
Definition pfa : p_i 1 -> prop := p_forall ent.

Fixpoint vexists {n : nat} : con n -> prop
    :=  match n as k return (con k -> prop) with
            | 0     =>  fun c : con 0 => c []
            | S i   =>  fun c : con (S i) => pex (fun x : e => vexists (fun v : e^i => c (x::v)))
        end.
Fixpoint vforall {n : nat} : con n -> prop
    :=  match n as k return (con k -> prop) with
            | 0     =>  fun c : con 0 => c []
            | S i   =>  fun c : con (S i) => pfa (fun x : e => vforall (fun v : e^i => c (x::v)))
        end.

(* extracting the projections of a bcon *)
(* fst and snd correspond to π and π', respectively *)
Definition sem : forall {n : nat}, bcon n -> con n
    := fun {n : nat} (b : bcon n) (v : e^n) => fst (b v).
Definition ci  : forall {n : nat}, bcon n -> con n
    := fun {n : nat} (b : bcon n) (v : e^n) => snd (b v).
(* "accepting" a bcon, thereby merging the sense and CI components of the output *)
Definition acc : forall {n : nat}, bcon n -> con n
    := fun {n : nat} (b : bcon n) (v : e^n) => (sem b v) and (ci b v).

Definition cc : forall {i : nat}, kon i -> update i
    := fun {i : nat} (k : kon i) (n : nat) (c : con n) (d : con (n+i)) => exists b : bcon (n+i), (k n c b) /\ d = (fun v : e^(n+i) => (c (take n v)) and (acc b v)).

(* this is the iffy one- I don't like the existential quantification in the CI *)
Definition NOT : forall {i : nat}, kon i -> kon 0
    := fun {i : nat} (k : kon i) (n : nat) (c : con n) (d : bcon (n+0)) => exists b : bcon (n+i), (k n c b) /\ d = (fun v : e^(n+0) => (not (vexists (fun u : e^i => sem b ((take n v)++u))),vexists (fun u : e^i => ci b ((take n v)++u)))).

Definition b_AND : forall {i j : nat}, kon i -> kon j -> kon (i+j)
    :=  fun {i j : nat} (h : kon i) (k : kon j) (n : nat) (c : con n) (d : bcon (n+(i+j))) =>
        exists (b : bcon (n+i)) (b' : bcon ((n+i)+j)),
            (h n c b) /\ (k (n+i) (fun v : e^(n+i) => (c (take n v)) and (acc b v)) b') /\ d = (fun v : e^(n+(i+j)) => let u := (vcast v (eq_sym (add_assoc n i j))) in ((sem b (take (n+i) u)) and (sem b' u),(ci b (take (n+i) u)) and (ci b' u))).
                                                                                        (* aka (fun v : e^(n+(i+j)) => (((sem b ((take n v)++(take i (drop n v)))) and (sem b' (((take n v)++(take i (drop n v)))++(drop i (drop n v))))),((ci b ((take n v)++(take i (drop n v)))) and (ci b' (((take n v)++(take i (drop n v)))++(drop i (drop n v))))))) *)
Infix "AND" := b_AND (at level 20) : bdyn_scope.

Definition b_THAT : forall {i j : nat}, dy i 1 -> dy j 1 -> dy (i+j) 1
    := fun {i j : nat} (D : dy i 1) (E : dy j 1) (m : nat) => (D m) AND (E m).
Infix "THAT" := b_THAT (at level 20) : bdyn_scope.

(* MUST explore the consequences of the CI's in these derived forms- chances are that they're problematic at best! *)
(* (h OR k) ≈ (NOT ((NOT h) AND (NOT k))) *)
Definition b_OR : forall {i j : nat}, kon i -> kon j -> kon 0
    :=  fun {i j : nat} (h : kon i) (k : kon j) (n : nat) (c : con n) (d : bcon (n+0)) =>
        exists (b : bcon (n+i)) (b' : bcon (n+j)), (h n c b) /\ (k n (fun v : e^n => (c v) and ((not (vexists (fun u : e^i => sem b (v++u)))) and (vexists (fun u : e^i => ci b (v++u))))) b')
            /\ d = (fun v : e^(n+0) => (((vexists (fun u : e^i => sem b ((take n v)++u))) or (vexists (fun t : e^j => sem b' ((take n v)++t)))),((vexists (fun u : e^i => ci b ((take n v)++u))) and (vexists (fun t : e^j => ci b' ((take n v)++t)))))).
Infix "OR" := b_OR (at level 20) : bdyn_scope.

(* (h IMPLIES k) ≈ ((NOT h) OR (h AND k)) *)
Definition b_IMPLIES : forall {i j : nat}, kon i -> kon j -> kon 0
    :=  fun {i j : nat} (h : kon i) (k : kon j) (n : nat) (c : con n) (d : bcon (n+0)) =>
        exists (b b' : bcon (n+i)) (b'' : bcon ((n+i)+j)),
                (h n c b)
            /\  (h n (fun v : e^n => (c v) and ((vexists (fun u : e^i => sem b (v++u))) and (vexists (fun u : e^i => ci b (v++u))))) b')
            /\  (k (n+i) (fun v : e^(n+i) => ((c (take n v)) and ((vexists (fun u : e^i => sem b ((take n v)++u))) and (vexists (fun u : e^i => ci b ((take n v)++u))))) and (acc b' v)) b'')
            /\  d = (fun v : e^(n+0) => (((vexists (fun u : e^i => sem b ((take n v)++u))) implies (vexists (fun u : e^i => vexists (fun t : e^j => (sem b' ((take n v)++u)) and (sem b'' (((take n v)++u)++t)))))),((vexists (fun u : e^i => ci b ((take n v)++u))) and (vexists (fun u : e^i => vexists (fun t : e^j => (ci b' ((take n v)++u)) and (ci b'' (((take n v)++u)++t)))))))).
Infix "IMPLIES" := b_IMPLIES (at level 20) : bdyn_scope.

(* "strong reading" implication: (h sIMPLIES k) ≈ (NOT (h AND (NOT k))) *)
Definition b_sIMPLIES : forall {i j : nat}, kon i -> kon j -> kon 0
    :=  fun {i j : nat} (h : kon i) (k : kon j) (n : nat) (c : con n) (d : bcon (n+0)) =>
        exists (b : bcon (n+i)) (b' : bcon ((n+i)+j)), (h n c b) /\ (k (n+i) (fun v : e^(n+i) => (c (take n v)) and (acc b v)) b')
            /\  d = (fun v : e^(n+0) => ((vforall (fun u : e^i => (sem b ((take n v)++u)) implies (vexists (fun t : e^j => sem b' (((take n v)++u)++t))))),(vexists (fun u : e^i => (ci b ((take n v)++u)) and (vexists (fun t : e^j => ci b' (((take n v)++u)++t))))))).
Infix "sIMPLIES" := b_sIMPLIES (at level 20) : bdyn_scope.



Definition cext : forall i n : nat, con n -> con (n+i) := fun (i n : nat) (c : con n) (v : e^(n+i)) => c (take n v).
Notation "c ⁺" := (cext 1 _ c) (at level 0) : bdyn_scope.

(* EXIST actually doesn't appear to need much alteration *)
Definition EXISTS : forall {i : nat}, dy i 1 -> kon (S i)
    := fun {i : nat} (D : dy i 1) (n : nat) (c : con n) (d : bcon (n+(S i))) => D n (n+1) c⁺ (fun v : e^((n+1)+i) => d (vcast v (add_assoc n 1 i))).

(* (FORALL D) ≈ (NOT (EXISTS (fun j : nat => NOT (D j)))) *)
Definition FORALL : forall {i : nat}, dy i 1 -> kon 0
    :=  fun {i : nat} (D : dy i 1) (n : nat) (c : con n) (d : bcon (n+0)) =>
        exists b : bcon ((n+1)+i), (D n (n+1) c⁺ b) /\ d = (fun v : e^(n+0) => ((pfa (fun x : e => vexists (fun u : e^i => sem b (((take n v)++[x])++u)))),(pex (fun x : e => vexists (fun u : e^i => ci b (((take n v)++[x])++u)))))).

(* (SOME D E) ≈ (EXISTS (D THAT E)) *)
Definition SOME : forall {i j : nat}, dy i 1 -> dy j 1 -> kon (S (i+j))
    :=  fun {i j : nat} (D : dy i 1) (E : dy j 1) (n : nat) (c : con n) (d : bcon (n+(S (i+j)))) =>
        exists (b : bcon ((n+1)+i)) (b' : bcon (((n+1)+i)+j)),
                (D n (n+1) c⁺ b)
            /\  (E n ((n+1)+i) (fun v : e^((n+1)+i) => (c (take n (take (n+1) v))) and (acc b v)) b')
            /\  d = (fun v : e^(n+(S (i+j))) => (((sem b (((take n v)++[head (drop n v)])++(take i (tail (drop n v))))) and (sem b' ((((take n v)++[head (drop n v)])++(take i (tail (drop n v))))++(drop i (tail (drop n v)))))),((ci b (((take n v)++[head (drop n v)])++(take i (tail (drop n v))))) and (ci b' ((((take n v)++[head (drop n v)])++(take i (tail (drop n v))))++(drop i (tail (drop n v)))))))).

(* EVERY w/ "regular," weak IMPLIES: (EVERY D E) ≈ (FORALL (fun m : nat => (D m) IMPLIES (E m))) *)
Definition EVERY : forall {i j : nat}, dy i 1 -> dy j 1 -> kon 0
    :=  fun {i j : nat} (D : dy i 1) (E : dy j 1) (n : nat) (c : con n) (d : bcon (n+0)) =>
        exists (b b' : bcon ((n+1)+i)) (b'' : bcon (((n+1)+i)+j)),
                (D n (n+1) c⁺ b)
            /\  (D n (n+1) (fun v : e^(n+1) => (c (take n v)) and ((vexists (fun u : e^i => sem b (v++u))) and (vexists (fun u : e^i => ci b (v++u))))) b')
            /\  (E n ((n+1)+i) (fun v : e^((n+1)+i) => ((c (take n (take (n+1) v))) and ((vexists (fun u : e^i => sem b ((take (n+1) v)++u))) and (vexists (fun u : e^i => ci b ((take (n+1) v)++u))))) and (acc b' v)) b'')
            /\  d = (fun v : e^(n+0) => ((pfa (fun x : e => (vexists (fun u : e^i => sem b (((take n v)++[x])++u))) implies (vexists (fun u : e^i => vexists (fun t : e^j => (sem b' (((take n v)++[x])++u)) and (sem b'' ((((take n v)++[x])++u)++t)))))))
                                        ,(pex (fun x : e => (vexists (fun u : e^i => ci b (((take n v)++[x])++u))) and (vexists (fun u : e^i => vexists (fun t : e^j => (ci b' (((take n v)++[x])++u)) and (ci b'' ((((take n v)++[x])++u)++t))))))))).

(* EVERY w/ "strong" IMPLIES: (sEVERY D E) ≈ (FORALL (fun m : nat => (D m) sIMPLIES (E m))) *)
Definition sEVERY : forall {i j : nat}, dy i 1 -> dy j 1 -> kon 0
    :=  fun {i j : nat} (D : dy i 1) (E : dy j 1) (n : nat) (c : con n) (d : bcon (n+0)) =>
        exists (b : bcon ((n+1)+i)) (b' : bcon (((n+1)+i)+j)),
                (D n (n+1) c⁺ b)
            /\  (E n ((n+1)+i) (fun v : e^((n+1)+i) => (c (take n (take (n+1) v))) and (acc b v)) b')
            /\  d = (fun v : e^(n+0) => ((pfa (fun x : e => vforall (fun u : e^i => (sem b (((take n v)++[x])++u)) implies (vexists (fun t : e^j => sem b' ((((take n v)++[x])++u)++t))))))
                                        ,(pex (fun x : e => vexists (fun u : e^i => (ci b (((take n v)++[x])++u)) and (vexists (fun t : e^j => ci b' ((((take n v)++[x])++u)++t)))))))).

(* (NO D E) ≈ (NOT (SOME D E)) *)
Definition NO : forall {i j : nat}, dy i 1 -> dy j 1 -> kon 0
    :=  fun {i j : nat} (D : dy i 1) (E : dy j 1) (n : nat) (c : con n) (d : bcon (n+0)) =>
        exists (b : bcon ((n+1)+i)) (b' : bcon (((n+1)+i)+j)),
                (D n (n+1) c⁺ b)
            /\  (E n ((n+1)+i) (fun v : e^((n+1)+i) => (c (take n (take (n+1) v))) and (acc b v)) b')
            /\  d = (fun v : e^(n+0) =>
                        ((not (pex (fun x : e => vexists (fun u : e^i => vexists (fun t : e^j => (sem b (((take n v)++[x])++u)) and (sem b' ((((take n v)++[x])++u)++t)))))))
                        ,(pex (fun x : e => vexists (fun u : e^i => vexists (fun t : e^j => (ci b (((take n v)++[x])++u)) and (ci b' ((((take n v)++[x])++u)++t)))))))).

(* newer version of NO, defined as a primitive; plan is to redefine NOT such that this NO is the result of (NO D E) ≈ (NOT (SOME D E)) *)
Definition NO2 : forall {i j : nat}, dy i 1 -> dy j 1 -> kon 0
    :=  fun {i j : nat} (D : dy i 1) (E : dy j 1) (n : nat) (c : con n) (d : bcon (n+0)) =>
        exists (b : bcon ((n+1)+i)) (b' : bcon (((n+1)+i)+j)),
                (D n (n+1) c⁺ b)
            /\  (E n ((n+1)+i) (fun v : e^((n+1)+i) => (c (take n (take (n+1) v))) and (acc b v)) b')
            /\  d = (fun v : e^(n+0) =>
                        ((not (pex (fun x : e => vexists (fun u : e^i => vexists (fun t : e^j => (sem b (((take n v)++[x])++u)) and (sem b' ((((take n v)++[x])++u)++t)))))))
                        ,(pfa (fun x : e => vforall (fun u : e^i => (sem b (((take n v)++[x])++u)) implies (vexists (fun t : e^j => (ci b (((take n v)++[x])++u)) and (ci b' ((((take n v)++[x])++u)++t))))))))).

(* pretty sure EVERY can be defined similarly to this NO, just with a different proffered output; still going with weak proffered output (but only 2 bcons quantified) *)
(* will be interesting to see if strong vs weak in CI dimension matters *)
Definition EVERY2 : forall {i j : nat}, dy i 1 -> dy j 1 -> kon 0
    :=  fun {i j : nat} (D : dy i 1) (E : dy j 1) (n : nat) (c : con n) (d : bcon (n+0)) =>
        exists (b : bcon ((n+1)+i)) (b' : bcon (((n+1)+i)+j)),
                (D n (n+1) c⁺ b)
            /\  (E n ((n+1)+i) (fun v : e^((n+1)+i) => (c (take n (take (n+1) v))) and (acc b v)) b')
            /\  d = (fun v : e^(n+0) =>
                        ((pfa (fun x : e => (vexists (fun u : e^i =>  sem b (((take n v)++[x])++u))) implies (vexists (fun u : e^i => vexists (fun t : e^j => (sem b (((take n v)++[x])++u)) and (sem b' ((((take n v)++[x])++u)++t)))))))
                        ,(pfa (fun x : e =>  vforall (fun u : e^i => (sem b (((take n v)++[x])++u))  implies (vexists (fun t : e^j => (ci b (((take n v)++[x])++u)) and (ci b' ((((take n v)++[x])++u)++t))))))))).

Section ent_cons.
    Definition cent : forall {n : nat}, con n -> forall (m : nat), p_i 1 -> Prop
        := fun {n : nat} (c : con n) (m : nat) (P : p_i 1) => exists q : m < n, forall v : e^n, (c v) entails (P (jth v m q)).
    Definition ccons : forall {n : nat}, con n -> forall (m : nat), p_i 1 -> Prop
        := fun {n : nat} (c : con n) (m : nat) (P : p_i 1) => exists q : m < n, forall v : e^n, ~((c v) entails (not (P (jth v m q)))).
End ent_cons.

Definition pro : (e -> prop) -> forall i : nat, dy i 1 -> kon i
    :=  fun (P : e -> prop) (i : nat) (D : dy i 1) (n : nat) (c : con n) (d : bcon (n+i)) =>
        exists (m : nat) (q : m < n) (b : bcon (n+i)),
            (forall v : e^n, ~((c v) entails (not (P (jth v m q))))) /\ (D m n c b) /\ d = (fun v : e^(n+i) => (sem b v,(ci b v) and (P (jth (take n v) m q)))).

Definition IT :  forall {i : nat}, dy i 1 -> kon i  := fun {i : nat} => pro nonhuman i.

Definition HE :  forall {i : nat}, dy i 1 -> kon i  := fun {i : nat} => pro male i.

Definition SHE : forall {i : nat}, dy i 1 -> kon i  := fun {i : nat} => pro female i.

(* maybe? *)
Definition THE : forall {i j : nat}, dy i 1 -> dy j 1 -> kon (i+j)
    :=  fun {i j : nat} (D : dy i 1) (E : dy j 1) (n : nat) (c : con n) (d : bcon (n+(i+j))) =>
        exists m : nat, m < n   /\ (forall b : bcon (n+i), (D m n c b) -> forall v : e^n, (c v) entails (vexists (fun u : e^i => acc b (v++u)))) (* or just sem? *)
                                /\  exists b : bcon (n+i), (D m n c b) /\ (E m (n+i) (fun u : e^(n+i) => (c (take n u)) and (acc b u)) (fun v : e^((n+i)+j) => d (vcast v (add_assoc n i j)))).


Definition udyn : forall i : nat, p_i i -> Vect nat i -> kon 0
    :=  fun i : nat =>
        match i as m return (p_i m -> Vect nat m -> kon 0) with
            | 0     => fun (p : prop) (_ : Vect nat 0) (n : nat) (_ : con n) (d : bcon (n+0)) => d = (fun _ : e^(n+0) => (p,truth))
            | S m   => fun (P : e -> p_i m) (u : Vect nat (S m)) (n : nat) (_ : con n) (d : bcon (n+0)) => exists q : (vmax u) < n, d = (fun v : e^(n+0) => (vuncur (S m) e prop P (imap u (take n v) q),truth))
        end.

Definition dyn : forall i : nat, p_i i -> dy 0 i := fun (i : nat) (P : p_i i) => vcur i nat (kon 0) (udyn i P).
(*  P:e→p   ⊢(dyn 1 P) ≈ (fun (x n : nat) (_ : con n) (d : bcon (n+0)) => exists q : x < n, d = (fun v : e^(n+0) => (P (jth (take n v) x q),truth)))
    R:e→e→p ⊢(dyn 2 R) ≈ (fun (x y n : nat) (_ : con n) (d : bcon (n+0)) => exists q : (max x y) < n, d = (fun v : e^(n+0) => (R (jth (take n v) x (max_lub_3 (S x) (S y) n q)) (jth (take n v) y (max_lub_4 (S x) (S y) n q)),truth)))
            or           (fun (x y n : nat) (_ : con n) (d : bcon (n+0)) => exists (q : x < n) (r : y < n), d = (fun v : e^(n+0) => (R (jth (take n v) x q) (jth (take n v) y r),truth))) *)

Section Dyn_ana.
    Definition BEAT : dy 0 2 := dyn 2 beat.
    Definition BRAY : dy 0 1 := dyn 1 bray.
    Definition DONKEY  : dy 0 1 := dyn 1 donkey.
    Definition FARMER : dy 0 1 := dyn 1 farmer.
    Definition OWN : dy 0 2 := dyn 2 own.
    Definition RAIN : dy 0 0 := dyn 0 rain.
End Dyn_ana.

(* attempt at the pejorative fucking *)
Axiom suck : e -> prop.

Definition FING : forall {i : nat}, dy i 1 -> dy i 1
    :=  fun {i : nat} (D : dy i 1) (m n : nat) (c : con n) (d : bcon (n+i)) =>
        exists b : bcon (n+i), (D m n c b) /\ d = (fun v : e^(n+i) => (sem b v,(ci b v) and (pfa (fun x : e => (sem b (replace v m x)) implies (suck x))))).

