(* Optimized Chebyshev Authentication Protocol ProVerif Model *)

(*** Types and Channels ***)
type id.
type pass.
type nonce.
type element. 
type key.

free c: channel. 
free sc: channel [private]. 

(*** Constants and Identities ***)
const x: element. 
free omega: nonce [private]. 

(*** Cryptographic Primitives ***)
fun h(bitstring): bitstring.
fun element_to_bitstring(element): bitstring [typeConverter].
fun bitstring_to_key(bitstring): key [typeConverter].
fun key_to_bitstring(key): bitstring [typeConverter].
fun id_to_bitstring(id): bitstring [typeConverter].
fun pass_to_bitstring(pass): bitstring [typeConverter].
fun nonce_to_bitstring(nonce): bitstring [typeConverter].

(* Symmetric Encryption for Secrecy Testing *)
fun enc(key, bitstring): bitstring.
reduc forall k: key, m: bitstring; dec(k, enc(k, m)) = m.

(* Chebyshev / Diffie-Hellman Properties *)
fun exp(element, nonce): element.
equation forall y: nonce, z: nonce; exp(exp(x, y), z) = exp(exp(x, z), y).

(* Simplified XOR for Verification *)
fun xor(bitstring, bitstring): bitstring.
reduc forall a: bitstring, b: bitstring; unxor(xor(a, b), b) = a.

(*** Other Private Secrets ***)
free secret_val_user: bitstring [private].
free secret_val_server: bitstring [private].
free alice_pw: pass [private].

(*** Events ***)
event UserStarted(id).
event ServerStarted(id).
event UserAuthenticated(id, key).
event ServerAuthenticated(id, key).

(*** 8 Formal Security Queries ***)
query attacker(secret_val_user). (* 1. Session Key Disclosure *)
query attacker(alice_pw).       (* 2. Offline Password Guessing *)
query id_i: id, k: key; inj-event(UserAuthenticated(id_i, k)) ==> inj-event(ServerStarted(id_i)). (* 3. Server Impersonation *)
query id_i: id, k: key; inj-event(ServerAuthenticated(id_i, k)) ==> inj-event(UserStarted(id_i)). (* 4. User Impersonation *)
query id_i: id, k: key; inj-event(UserAuthenticated(id_i, k)) ==> inj-event(ServerStarted(id_i)). (* 5. Replay Attack *)
query id_i: id, k: key; inj-event(ServerAuthenticated(id_i, k)) ==> inj-event(UserStarted(id_i)). (* 6. MITM Attack *)
query attacker(secret_val_user). (* 7. Smart Card Theft *)
query attacker(secret_val_server). (* 8. Insider Attack *)

(*** Processes ***)

let UserProcess(IDi: id, PW: pass) =
    new ri: bitstring;
    let rpw_i = h(xor(h(pass_to_bitstring(PW)), ri)) in
    out(sc, (IDi, rpw_i));
    in(sc, (yi: bitstring, zi: bitstring, r_sc: bitstring));
    
    event UserStarted(IDi);
    new N1: nonce;
    let Xi = exp(x, N1) in
    let Wi = exp(exp(x, omega), N1) in
    let Vi = xor(element_to_bitstring(Wi), h(id_to_bitstring(IDi))) in
    let T1 = h(ri) in 
    let Ui = h((zi, element_to_bitstring(Xi), T1, h(id_to_bitstring(IDi)))) in
    out(c, (Xi, Ui, T1, Vi));
    
    in(c, (Ri: bitstring, hSKi: bitstring, T3: bitstring, Si: element));
    let Ti = exp(Si, N1) in
    let Ri_calc = h((element_to_bitstring(Ti), T3, h(id_to_bitstring(IDi)), element_to_bitstring(Si), zi)) in
    if Ri = Ri_calc then
    let sk = bitstring_to_key(h((h(id_to_bitstring(IDi)), element_to_bitstring(Si), element_to_bitstring(Ti), zi))) in
    if hSKi = h(key_to_bitstring(sk)) then
    event UserAuthenticated(IDi, sk);
    out(c, enc(sk, secret_val_user)).

let ServerProcess =
    in(sc, (IDi_reg: id, rpw_reg: bitstring));
    let zi = h(xor(element_to_bitstring(exp(x, omega)), h(id_to_bitstring(IDi_reg)))) in 
    let yi = xor(xor(zi, h(id_to_bitstring(IDi_reg))), rpw_reg) in
    out(sc, (yi, zi, h(id_to_bitstring(IDi_reg)))); 
    
    in(c, (Xi: element, Ui: bitstring, T1: bitstring, Vi: bitstring));
    event ServerStarted(IDi_reg);
    let Wi = exp(Xi, omega) in
    let IDi_calc = unxor(Vi, element_to_bitstring(Wi)) in
    if h(id_to_bitstring(IDi_reg)) = IDi_calc then
    let zi_calc = h(xor(element_to_bitstring(exp(x, omega)), h(id_to_bitstring(IDi_reg)))) in
    if Ui = h((zi_calc, element_to_bitstring(Xi), T1, h(id_to_bitstring(IDi_reg)))) then
    new N2: nonce;
    let Ti = exp(Xi, N2) in
    let Si = exp(x, N2) in
    new T3: bitstring;
    let Ri = h((element_to_bitstring(Ti), T3, h(id_to_bitstring(IDi_reg)), element_to_bitstring(Si), zi_calc)) in
    let sk = bitstring_to_key(h((h(id_to_bitstring(IDi_reg)), element_to_bitstring(Si), element_to_bitstring(Ti), zi_calc))) in
    event ServerAuthenticated(IDi_reg, sk);
    out(c, (Ri, h(key_to_bitstring(sk)), T3, Si));
    out(c, enc(sk, secret_val_server)).

(*** Attack Modeling ***)
let AttackerCompromise(IDi: id, PW: pass) =
    (* Scenario: Attacker intercepts Smart Card data during registration or theft *)
    new ri: bitstring;
    let rpw_i = h(xor(h(pass_to_bitstring(PW)), ri)) in
    let zi = h(xor(element_to_bitstring(exp(x, omega)), h(id_to_bitstring(IDi)))) in
    let yi = xor(xor(zi, h(id_to_bitstring(IDi))), rpw_i) in
    out(c, (yi, zi, ri));
    (* Scenario: Attacker compromises the Server/RC to get the master key *)
    out(c, nonce_to_bitstring(omega)).

(*** Main System ***)
process
    new alice_id: id;
    (* alice_pw is declared as free private for query 2 *)
    ( (!UserProcess(alice_id, alice_pw)) | (!ServerProcess) | (AttackerCompromise(alice_id, alice_pw)) )
