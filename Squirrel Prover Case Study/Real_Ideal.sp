(* Declaration part *)
(* Postt-quantum setting *)
(* set postQuantumSound = true. *)
 
(* Import a module or library named Basic, similar to "import numpy" in python *)
include Basic.
 
(* declare clientA and serverB*)
channel cA
channel sB
 
(* declare asymmetric encryption function *)
(* need to use adec in clientA but pk already declared in signature so rename it as a_pk *)
aenc a_enc,a_dec,a_pk
 
(* declare symmetric encryption function *)
senc s_enc,s_dec
 
(* pk is a function in signature to generate public key *)
signature sig,ver,pk
 
(* declare signature function *)
abstract getSigMessage : message * message -> message.
axiom [any] getSigMessage  (x,y:_) : getSigMessage(sig(x,y), pk(y)) = x.
 
(* private key of cA, sB and adversary *)
name skA : index -> message
name skB : index -> message
name DskA : index -> message
 
(* do not need to declare input message x *)
(* name x : message *)
 
(* client's public key for serverB *)
name pkX : message
 
(* need to declare for out by notice *)
name pkA : message
name pkB : message
 
(* random value *)
name r: index -> message
name s: index -> message.
 
abstract ok : message
abstract ko : message.
 
(* Modeling part *)
(* i, j, k => index of cA, sB, session *)
process clientA(i,j,k:index) =
let pkA = pk(skA(i)) in
out(cA, pkA);
in(cA,x);
(* x = <pk(skB), k>, aenc(sign(<k, pk(skA)>, skB), pk(skB)) *)
(* fixed x = pk(skB), aenc(sign(<k, pk(skA)>, skB), pk(skB)) *)
(* y = sign(<k, pk(skA)>, skB) *)
(* getSigMessage = <k, pk(skA)> *)
(* use pkB to decrypt signature and get k*)
let pkB = fst(x) in
let y = a_dec(snd(x),skA(i)) in
let sk = fst( getSigMessage(y, pkB) ) in
if ver(<sk, pkA>, y, pkB) && pkB = pk(skB(j)) then
  out(cA,s_enc(s(i), r(i), sk))
else
  out(cA, diff(ok, ko)).
 
process serverB(j,k:index) = 
new bk;
in(sB, pkX);
out(sB, <pk(skB(j)), a_enc(sig(<bk, pkX>, skB(j)), r(j), pkX)>);
in(sB, m);
let z = s_dec(m, bk) in
null.
 
system real = (!_i !_j !_k cA: clientA(i,j,k)) | (!_j !_k sB: serverB(j,k)).
 
(* Attacker pretends to be serverB *)
(* <pk(DskB), aenc(sign(<Dk, pk(DskB)>, DskB), pk(skA))> *)
name sfresh: index -> message.
process clientACCA1(i,j,k:index) =
let pkA = pk(skA(i)) in
out(cA, pkA);
in(cA,x);
let pkB = fst(x) in
let y = a_dec(snd(x),skA(i)) in
let sk = fst( getSigMessage(y, pkB) ) in
if ver(<sk, pkA>, y, pkB) && pkB = pk(skB(j)) then
  out(cA,s_enc(diff(s(i),sfresh(i)), r(i), sk))
else
  out(cA, diff(ok, ko)).
 
system ideal = (!_i !_j !_k cA: clientACCA1(i,j,k)) | (!_j !_k sB: serverB(j,k)).
 
(*
axiom [any] len_h (x,y:message) : len(h(x,y)) = namelength_message.
axiom len_id (i:index)   : len(id(i))    = namelength_message.
*)
 
(* Technical lemma about lengths. *)
(* Secrecy Proof *)
name m': message.
global lemma [real/left, real/left] StrongSecrecy (i,j,k:index,tau,tau':timestamp[const]):
  [happens(pred(tau))]
  -> equiv(frame@tau, diff(s(i), m'))
  -> [input@tau <> s(i)].
Proof.
intro H.
induction tau => Hap.
(* use reflex with init. *)
(* (init,A,A1,cA1,cA2,cA3,sB1,sB2,DcA,DcA1,DcA2) *)
+ (* tau = init *)
  auto.
+ (* tau = cA1 *)
(* use reflex with cA1. *)
  rewrite equiv Hap.
  intro HA'.
  clear H.
  by fresh HA'.
+ (* tau = cA2 *)
(* use reflex with cA1. *)
  rewrite equiv Hap.
  intro HA1'.
  clear H.
  by fresh HA1'.
+ (* tau = cA3 *)
(* use reflex with cA1. *)
  rewrite equiv Hap.
  intro H'.
  clear H.
  by fresh H'.
+ (* tau = sB1 *)
  rewrite equiv Hap.
  intro H2'.
  clear H.
  by fresh H2'.
+ (* tau = sB2 *)
  rewrite equiv Hap.
  intro H3'.
  clear H.
  by fresh H3'.
Qed.
 
(* Technical lemma. *)
lemma [real/left, ideal/left] diff_refl (x:message) : diff(x,x) = x.
Proof. 
by project. 
Qed.
 
(* Try to prove real and ideal system are equivalence then use trans to prove secrecy *)
(* Equivalence between the real and ideal systems, with some extra messages given to the distinguisher. *)
global lemma [set: real/left;equiv: real/left, ideal/left] real_ideal (i,j,k:index[const],tau:timestamp[const]):
    [happens(tau)] 
    -> equiv(frame@tau, pk(skA(i)), pk(skB(j)), s(i), r(i), skA(i)).
Proof.
  induction tau => Htau.
  + (* tau = init *)
    auto.
  + (* tau = cA1 *)
    expandall; try by rewrite if_false.
    simpl. 
    fa !<_,_>, if _ then _.
(*
received message:
Focused goal (1/5):
Systems: real/left (equivalences: left:real/left, right:ideal/left)
Variables:
  i:index[glob],i0:index[const, glob],j:index[glob],j0:index[const, glob],
  k:index[glob],k0:index[const, glob]
Htau: [happens(cA1(i0, j0, k0))]
IH: [happens(pred (cA1(i0, j0, k0)))] ->
    equiv(frame@pred (cA1(i0, j0, k0)), pk (skB j), pk (skA i), s i, 
          r i, skA i)
----------------------------------------
0: frame@pred (cA1(i0, j0, k0))
1: diff(pk (skA i0), pk (skA i0))
2: pk (skB j)
3: s i
4: r i
5: skA i
*)
  rewrite diff_refl.
  (*
  fresh 1 => //.
Freshness on the left side:
 
Exec failed: [error-6-7]
 Tactic failed: Can only be applied to diff(n_L, n_R).
  *)
  fa 1 => //.
(*
Focused goal (1/5):
Systems: real/left (equivalences: left:real/left, right:ideal/left)
Variables:
  i:index[glob],i0:index[const, glob],j:index[glob],j0:index[const, glob],
  k:index[glob],k0:index[const, glob]
Htau: [happens(cA1(i0, j0, k0))]
IH: [happens(pred (cA1(i0, j0, k0)))] ->
    equiv(frame@pred (cA1(i0, j0, k0)), pk (skB j), pk (skA i), s i, 
          r i, skA i)
----------------------------------------
0: frame@pred (cA1(i0, j0, k0))
1: skA i0
2: pk (skB j)
3: s i
4: r i
5: skA i
*)
  fresh 1 => //.
  (*
Focused goal (1/6):
System: real/left (equivalences: left:real/left, right:ideal/left)
Variables: i,i0,j,j0,k,k0:index[const, glob]
Htau: [happens(cA1(i0, j0, k0))]
IH: [happens(pred (cA1(i0, j0, k0)))] ->
    equiv(frame@pred (cA1(i0, j0, k0)), pk (skA i), pk (skB j), s i, 
          r i, skA i)
----------------------------------------
i0 <> i &&
(forall (i,j,k:index), cA1(i, j, k) < cA1(i0, j0, k0) => i0 <> i) &&
(forall (i,j,k:index), cA2(i, j, k) < cA1(i0, j0, k0) => i0 <> i) &&
forall (i,j,k:index), cA3(i, j, k) < cA1(i0, j0, k0) => i0 <> i 
*)
(*solve the index matching problem, but the error message returned was very general. It was difficult for me to determine the reason.*)
  (have A : i0 = i by auto); rewrite A in *; clear A.
(*
have A : i0 = i.
Focused goal (1/7):
System: real/left (equivalences: left:real/left, right:ideal/left)
Variables: i,i0,j,j0,k,k0:index[const, glob]
Htau: [happens(cA1(i0, j0, k0))]
IH: [happens(pred (cA1(i0, j0, k0)))] ->
    equiv(frame@pred (cA1(i0, j0, k0)), pk (skA i), pk (skB j), s i, 
          r i, skA i)
----------------------------------------
i0 = i 
 
by auto.
Exec failed: [error-20-24]
Tactic failed: cannot close goal
*)
  apply IH.
 
Qed.
 
(* Strong secrecy for the ideal system,expressed using a fresh ideal key ikIR. *)
name ssfresh: index -> message.
global lemma [idealized/left,idealized/left] strong_ideal (i,j,k:index[const]):
  [happens(tau))] -> 
  equiv(frame@tau,if tau = action? then diff(s(i)@tau,ssfresh)).
Proof.
 
Qed.
 
(* The final strong secrecy result is the consequence of the previous lemmas by transitivity. *)
global lemma [set: real/left;equiv: real/left,real/left] SSec_real (tau:timestamp[const]) :
  [happens(tau)] ->
  equiv(frame@tau,if tau = action? then diff(s(i)@tau,ssfresh)).
Proof.
 
Qed.
 
