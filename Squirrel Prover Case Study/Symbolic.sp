(* Declaration part *)
(* Post-quantum setting *)
(* set postQuantumSound = true. *)

(* Import a module or library named Basic, similar to "import numpy" in python *)
include Basic.

(* pk is a function in signature to generate public key *)
signature sig,ver,pk

(* declare signature function *)
abstract getSigMessage : message * message -> message.
axiom [any] getSigMessage  (x,y:_) : getSigMessage(sig(x,y), pk(y)) = x.

(* declare asymmetric encryption function *)
(* need to use adec in clientA but pk already declared in signature so rename it as a_pk *)
aenc a_enc,a_dec,a_pk
(* declare symmetric encryption function *)
senc s_enc,s_dec

(* declare clientA and serverB*)
channel cA
channel sB

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
mutable s (i:index) : message =  zero

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
let y = a_dec(x,skA(i)) in
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

system main = ( !_i !_j !_k cA: clientA(i,j,k) ) | ( !_j !_k sB: serverB(j,k) ). 

(*
System Empty registered with actions (init).
System main registered with actions (init,cA1,cA2,cA3,sB1,sB2).
*)

(*
system main = (!_j !_k serverB(j,k)) | (!_i !_j !_k cA: clientA(i,j,k)). 
system main = out(cA, pkA); out(sB, <pkB, k>); (
              (!_j !_k sB: serverB(j,k) )
           |  (!_i !_j !_k cA: clientA(i,j,k) )
              ).
*)

(* Secrecy Proof *)
name m': message.

global lemma [main/left, main/left] StrongSecrecy (i,j,k:index,tau,tau':timestamp[const]):
  [happens(pred(tau))]
  -> equiv(frame@tau, diff(s(i)@tau',m'))
  -> [input@tau <> s(i)@tau'].
Proof.
intro H.
induction tau => Hap.
(* use reflex with init. *)
(* init,cA1,cA2,cA3,sB1,sB2 *)
+ (* tau = init *)
  auto.
+ (* tau = cA1 *)
(* use reflex with cA1. *)
  rewrite equiv Hap.
  intro H'.
  clear H.
  by fresh H'.
+ (* tau = cA2 *)
  rewrite equiv Hap.
  intro H2'.
  clear H.
  by fresh H2'.
+ (* tau = cA3 *)
  rewrite equiv Hap.
  intro H3'.
  clear H.
  by fresh H3'.
+ (* tau = sB1 *)
  rewrite equiv Hap.
  intro H4'.
  clear H.
  by fresh H4'.
+ (* tau = sB2 *)
  rewrite equiv Hap.
  intro H5'.
  clear H.
  by fresh H5'.
Qed.
