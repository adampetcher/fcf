
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  match b1 with
  | True ->
    (match b2 with
     | True -> False
     | False -> True)
  | False -> b2

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, y) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (x, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val id : 'a1 -> 'a1 **)

let id x =
  x

type sumbool =
| Left
| Right

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False ->
    (match b2 with
     | True -> False
     | False -> True)

type 'a t =
| Nil0
| Cons0 of 'a * nat * 'a t

(** val map2 : ('a1 -> 'a2 -> 'a3) -> nat -> 'a1 t -> 'a2 t -> 'a3 t **)

let rec map2 g n v1 v2 =
  match v1 with
  | Nil0 ->
    (match v2 with
     | Nil0 -> Nil0
     | Cons0 (h, n0, t0) ->
       Obj.magic (fun _ -> assert false (* absurd case *)))
  | Cons0 (h1, n0, t1) ->
    (match v2 with
     | Nil0 -> Obj.magic (fun _ -> assert false (* absurd case *)) t1
     | Cons0 (h2, n1, t2) -> Cons0 ((g h1 h2), n1, (map2 g n1 t1 t2)))

(** val fold_left2 :
    ('a1 -> 'a2 -> 'a3 -> 'a1) -> 'a1 -> nat -> 'a2 t -> 'a3 t -> 'a1 **)

let rec fold_left2 f a n v w =
  match v with
  | Nil0 ->
    (match w with
     | Nil0 -> a
     | Cons0 (h, n0, t0) -> Obj.magic (fun _ -> id))
  | Cons0 (vh, vn, vt) ->
    (match w with
     | Nil0 -> Obj.magic (fun _ -> id) vt
     | Cons0 (wh, n0, wt) -> fold_left2 f (f a vh wh) n0 vt wt)

type bvector = bool t

(** val bVxor : nat -> bvector -> bool t -> bool t **)

let bVxor n v =
  map2 xorb n v

type 'a eq_dec = 'a -> 'a -> sumbool

type 'a eqDec =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_EqDec *)

(** val eqb0 : 'a1 eqDec -> 'a1 -> 'a1 -> bool **)

let eqb0 eqDec0 =
  eqDec0

(** val eqDec_dec : 'a1 eqDec -> 'a1 -> 'a1 -> sumbool **)

let eqDec_dec h a b =
  let x = eqb0 h a b in
  (match x with
   | True -> Left
   | False -> Right)

(** val eqb_vector : 'a1 eqDec -> nat -> 'a1 t -> 'a1 t -> bool **)

let eqb_vector eqd n v1 v2 =
  fold_left2 (fun b a1 a2 ->
    match b with
    | True -> eqb0 eqd a1 a2
    | False -> False) True n v1 v2

(** val bool_EqDec : bool eqDec **)

let bool_EqDec =
  eqb

(** val eqbBvector : nat -> bvector -> bvector -> bool **)

let eqbBvector n v1 v2 =
  eqb_vector bool_EqDec n v1 v2

(** val bvector_EqDec : nat -> bvector eqDec **)

let bvector_EqDec n =
  eqbBvector n

(** val eqbPair :
    'a1 eqDec -> 'a2 eqDec -> ('a1, 'a2) prod -> ('a1, 'a2) prod -> bool **)

let eqbPair dA dB p1 p2 =
  match eqb0 dA (fst p1) (fst p2) with
  | True -> eqb0 dB (snd p1) (snd p2)
  | False -> False

(** val pair_EqDec : 'a1 eqDec -> 'a2 eqDec -> ('a1, 'a2) prod eqDec **)

let pair_EqDec dA dB =
  eqbPair dA dB

type blist = bool list

(** val bvector_eq_dec : nat -> bvector -> bvector -> sumbool **)

let bvector_eq_dec n v1 v2 =
  eqDec_dec (bvector_EqDec n) v1 v2

(** val shiftOut : blist -> nat -> (bvector, blist) prod option **)

let rec shiftOut s = function
| O -> Some (Pair (Nil0, s))
| S n' ->
  (match s with
   | Nil -> None
   | Cons (b, s') ->
     (match shiftOut s' n' with
      | Some p ->
        let Pair (v', s'') = p in Some (Pair ((Cons0 (b, n', v')), s''))
      | None -> None))

type 'x comp =
| Ret of 'x eq_dec * 'x
| Bind of __ comp * (__ -> 'x comp)
| Rnd of nat
| Repeat of 'x comp * ('x -> bool)

(** val bvector_exists : nat -> bvector **)

let rec bvector_exists = function
| O -> Nil0
| S n0 -> Cons0 (True, n0, (bvector_exists n0))

(** val comp_base_exists : 'a1 comp -> 'a1 **)

let rec comp_base_exists = function
| Ret (e, a) -> Obj.magic (fun _ e0 a0 -> Obj.magic a0) __ e a
| Bind (c0, c1) ->
  Obj.magic (fun _ _ x iHX c2 h -> Obj.magic h iHX) __ __ c0
    (Obj.magic comp_base_exists c0) c1 (fun b -> comp_base_exists (c1 b))
| Rnd n -> Obj.magic (bvector_exists n)
| Repeat (c0, b) ->
  Obj.magic (fun _ x iHX b0 -> iHX) __ c0 (comp_base_exists c0) b

(** val comp_eq_dec : 'a1 comp -> 'a1 eq_dec **)

let rec comp_eq_dec = function
| Ret (e, a) -> Obj.magic (fun _ e0 a0 -> Obj.magic e0) __ e a
| Bind (c0, c1) ->
  Obj.magic (fun _ _ x iHX c2 h -> h (comp_base_exists x)) __ __ c0
    (Obj.magic comp_eq_dec c0) c1 (fun b -> comp_eq_dec (c1 b))
| Rnd n -> let h = bvector_eq_dec n in Obj.magic h
| Repeat (c0, b) ->
  Obj.magic (fun _ x iHX b0 -> iHX) __ c0 (comp_eq_dec c0) b

type 'a comp_state =
| Cs_done of 'a * blist
| Cs_eof
| Cs_more of 'a comp * blist

(** val evalDet_step : 'a1 comp -> blist -> 'a1 comp_state **)

let rec evalDet_step c s =
  match c with
  | Ret (pf, a) -> Cs_done (a, s)
  | Bind (c1, c2) ->
    (match evalDet_step (Obj.magic c1) s with
     | Cs_done (b, s') -> Cs_more ((Obj.magic c2 b), s')
     | Cs_eof -> Cs_eof
     | Cs_more (c1', s') -> Cs_more ((Bind ((Obj.magic c1'), c2)), s'))
  | Rnd n ->
    (match shiftOut s n with
     | Some p ->
       let Pair (v, s') = p in
       Cs_more ((Ret ((Obj.magic (bvector_eq_dec n)), (Obj.magic v))), s')
     | None -> Cs_eof)
  | Repeat (c0, p) ->
    Cs_more ((Bind ((Obj.magic c0), (fun a ->
      match Obj.magic p a with
      | True -> Ret ((comp_eq_dec c0), (Obj.magic a))
      | False -> Repeat (c0, p)))), s)

type key = bvector

type plaintext = bvector

(** val pRFE_Encrypt :
    nat -> (bvector -> bvector -> bvector) -> key -> plaintext -> (bvector,
    bool t) prod comp **)

(** val pRFE_Encrypt_prog :
    nat -> (bvector -> bvector -> bvector) -> bvector -> plaintext -> blist
    -> (bvector, bool t) prod comp_state **)

let bool_to_mybool b =
  match b with
    | true -> True
    | false -> False

let rec randomBits x =
  if(x == 0) then Nil else 
  let b = Random.bool() in 
  let ls' = randomBits (x - 1) in 
  (Cons (bool_to_mybool b, ls'))

let rec append ls1 ls2 =
  match ls1 with
  | Nil -> ls2
  | Cons (x, ls1') -> Cons (x, (append ls1' ls2)) 

let rec runComp_h c s =
  match (evalDet_step c s) with
  | Cs_done (b, s') -> Cs_done (b, s')
  | Cs_eof -> let newBits = randomBits 1000 in runComp_h c (append s newBits)
  | Cs_more (c', s') -> runComp_h c' s' 

exception InvalidCompState;;

let runComp c = 
  match (runComp_h c Nil) with
  | Cs_done (b, s') -> b
  | Cs_eof -> raise InvalidCompState
  | Cs_more (c', s') -> raise InvalidCompState

let pRFE_KeyGen eta =
  Rnd eta

let pRFE_Encrypt eta f k p =
  Bind ((Rnd eta), (fun r -> Ret
    ((eqDec_dec (pair_EqDec (bvector_EqDec eta) (bvector_EqDec eta))), (Pair
    ((Obj.magic r), (bVxor eta p (Obj.magic f k r)))))))

let pRFE_Decrypt eta f k c =
  bVxor eta (snd c) (f k (fst c))

let prf = bVxor 

let pRFE_Encrypt_prog eta k p =
  runComp (pRFE_Encrypt eta (prf eta) k p)

let pRFE_KeyGen_prog eta =
  runComp (pRFE_KeyGen eta)

let pRFE_Decrypt_prog eta =
  pRFE_Decrypt eta (prf eta)

;;

let rec nat_of_int i =
  if (i == 0) then O else (S (nat_of_int (i - 1)))



let bool_to_bit b =
  match b with
  | True -> 1
  | False -> 0

let rec print_bvector (v : bvector) =
  match v with
  | Nil0 -> ()
  | Cons0 (b, n, v') -> let _ = print_int (bool_to_bit b) in (print_bvector v');;

let size = (nat_of_int 64);;

Random.self_init;;
let key = pRFE_KeyGen_prog size;;

print_string "Here's the key:\n";;
print_bvector key;;
print_string "\n";;

(** use the key gen function to make a random plaintext **)
let pt = pRFE_KeyGen_prog size;;
print_string "Here's the plaintext:\n";;
print_bvector pt;;
print_string "\n";;

let ct = pRFE_Encrypt_prog size key pt;;
print_string "Here's the ciphertext:\n";;
print_bvector (fst ct);;
print_string "\n";;
print_bvector (snd ct);;
print_string "\n";;

let pt2 = pRFE_Decrypt_prog size key ct;;
print_string "Here's the plaintext after decryption:\n";;
print_bvector pt2;;
print_string "\n";;