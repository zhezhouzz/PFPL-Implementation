fun pLn s = print (s ^ "\n");

signature TY =
sig
    datatype t = N
               | Pf of t * t
    val eq : t * t -> bool
    val layout: t -> string
end

structure Ty : TY =
struct
datatype t = N
           | Pf of t * t
fun eq (t1, t2) =
    case (t1, t2) of
        (N, N) => true
      | (Pf (t11, t12), Pf (t21, t22)) =>
        (eq (t11, t21)) andalso (eq (t12, t22))
      | _ => false
fun layout N = "N"
  | layout (Pf (t1, t2)) = "(" ^ (layout t1) ^ "→" ^ (layout t2) ^ ")"
end

signature E =
sig
    datatype t = Z
               | S of t
               | V of string
               | Ifz of t * t * string * t
               | Lam of Ty.t * string * t
               | Ap of t * t
               | Fix of Ty.t * string * t
    val eq : t * t -> bool
    val layout: t -> string
    val subst: t * string * t -> t
end

structure E : E =
struct
datatype t = Z
           | S of t
           | V of string
           | Ifz of t * t * string * t
           | Lam of Ty.t * string * t
           | Ap of t * t
           | Fix of Ty.t * string * t
fun eq (e1, e2) =
    case (e1, e2) of
        (Z, Z) => true
      | (S e1, S e2) => eq (e1, e2)
      | (V x, V y) => x = y
      | (Ifz (e1, e2, x1, e3), Ifz (e1', e2', x1', e3')) =>
        (eq (e1, e1')) andalso
        (eq (e2, e2')) andalso
        (eq (e3, e3')) andalso
        (x1 = x1')
      | (Lam (t, x, e), Lam (t', x', e')) =>
        (Ty.eq (t, t')) andalso
        (eq (e, e')) andalso
        (x = x')
      | (Ap (e1, e2), Ap (e1', e2')) =>
        (eq (e1, e1')) andalso
        (eq (e2, e2'))
      | (Fix (t, x, e), Fix (t', x', e')) =>
        (eq (e, e')) andalso
        (Ty.eq (t, t')) andalso
        (x = x')
      | _ => false

fun n2int Z = 0
  | n2int (S n) = 1 + (n2int n)
  | n2int _ = raise Fail "not a N"

fun layout Z = "0"
  | layout (S n) = "(S " ^ (layout n) ^ ")"
  | layout (V x) = x
  | layout (Ifz (e1, e2, x, e3)) =
    "(ifz " ^ (layout e1) ^ " then " ^ (layout e2) ^ " else " ^ x ^ "." ^ (layout e3) ^ ")"
  | layout (Lam (t, x, e)) = "λ[" ^ (Ty.layout t) ^ "](" ^ x ^ "." ^ (layout e) ^ ")"
  | layout (Ap (e1, e2)) = "ap(" ^ (layout e1) ^ " " ^ (layout e2) ^ ")"
  | layout (Fix (t, x, e)) = "fix[" ^ (Ty.layout t) ^ "](" ^ x ^ "." ^ (layout e) ^ ")"

fun subst (e, id, eid) =
    case e of
        Z => Z
      | S e => S (subst (e, id, eid))
      | V id' =>
        if id = id' then eid else V id'
      | Ifz (e1, e2, x, e3) =>
        if x = id
        then Ifz (subst (e1, id, eid), subst (e2, id, eid), x, e3)
        else Ifz (subst (e1, id, eid), subst (e2, id, eid), x, subst (e3, id, eid))
      | Lam (t, x, e1) =>
        if x = id
        then Lam (t, x, e1)
        else Lam (t, x, subst (e1, id, eid))
      | Ap (e1, e2) => Ap (subst (e1, id, eid), subst (e2, id, eid))
      | Fix (t, x, e1) =>
        if x = id
        then Fix (t, x, e1)
        else Fix (t, x, subst (e1, id, eid))
end

structure Gamma =
struct
type t = E.t -> Ty.t option

val empty = fn _ => NONE
fun update (gamma, e, t) = fn e' => if E.eq (e, e') then SOME t else gamma e'
fun get (gamma, e) = gamma e
end

structure Static =
struct

open E
open Gamma

fun static (gamma, e) =
    case e of
        Z => SOME Ty.N
      | S e =>
        (case static (gamma, e) of
             SOME Ty.N => SOME Ty.N
           | _ => NONE)
      | V id => gamma (V id)
      | Ifz (e1, e2, x, e3) =>
        (case (static (gamma, e1), static (gamma, e2),
               static (update (gamma, V x, Ty.N), e3)) of
             (SOME N, SOME t2, SOME t3) =>
             if Ty.eq (t2, t3) then SOME t2 else NONE
           | _ => NONE
        )
      | Lam (t, x, e1) =>
        (case static (update (gamma, V x, t), e1) of
             SOME t' => SOME (Ty.Pf (t, t'))
           | _ => NONE
        )
      | Ap (e1, e2) =>
        (case (static (gamma, e1), static (gamma, e2)) of
             (SOME (Ty.Pf (t1, t2)), SOME t3) =>
             if Ty.eq (t1, t3) then SOME t2 else NONE
           | _ => NONE
        )
      | Fix (t, x, e1) =>
        (case static (update (gamma, V x, t), e1) of
             SOME t' =>
             if Ty.eq (t, t') then SOME t else NONE
           | _ => NONE
        )

fun eval e =
    let
        val gamma = Gamma.empty
        val tyOpt = static (Gamma.empty, e)
        val tyStr = case tyOpt of NONE => "Type Error" | SOME t => Ty.layout t
    in
        (E.layout e) ^ " : " ^ tyStr
    end
end

structure Dynamic =
struct
datatype value =
         Z
         | S of value
         | Lam of Ty.t * string * E.t

datatype thunk = Value of value
               | Exp of E.t

exception PCF_RUNTIME

fun value2e v =
    case v of
        Z => E.Z
      | S v => E.S (value2e v)
      | Lam (t, x, e) => E.Lam (t, x, e)

fun step e =
    case e of
        E.Z => Value Z
      | E.S e =>
        (case step e of
             Value v => Value (S v)
           | Exp e => Exp (E.S e)
        )
      | E.Ifz (e1, e2, x, e3) =>
        (case step e1 of
             Exp e1 => Exp (E.Ifz (e1, e2, x, e3))
           | Value Z => Exp (e2)
           | Value (S v) => Exp (E.subst (e3, x, value2e v))
           | _ => raise PCF_RUNTIME
        )
      | E.Lam (t, x, e) => Value (Lam (t, x, e))
      | E.Ap (e1, e2) =>
        (case step e1 of
             Exp e1 => Exp (E.Ap (e1, e2))
           | Value (Lam (t, x, e1)) =>
             (case step e2 of
                  Exp e2 => Exp (E.Ap (E.Lam (t, x, e1), e2))
                | Value v2 => Exp (E.subst (e1, x, value2e v2))
             )
           | _ => raise PCF_RUNTIME
        )
      | E.Fix (t, x, e) => Exp (E.subst (e, x, E.Fix (t, x, e)))
      | E.V id => raise Fail ("Runtime Error: Unbound id:" ^ id)

fun smallstep e =
    let
        val _ = pLn (Static.eval e)
    in
        case step e of
            Exp e => smallstep e
          | Value v => pLn ">>>> value <<<<"
    end
end

open E;

let
    val exp1 = Ifz (S(S(S Z)), Z, "x", V "x")
    val exp2 = Lam (Ty.N, "y", Ifz (S(S(S Z)), Z, "x", V "y"))
    val exp3 = Lam (Ty.N, "y", Ifz (S(S(S Z)), Z, "x", V "z"))
    val exp4 = Fix (Ty.Pf (Ty.N, Ty.N), "f", Lam (Ty.N, "x", S (Ap (V "f", V "x"))))
    val exp5 = Ap (Fix (Ty.Pf (Ty.N, Ty.N), "f", Lam (Ty.N, "x", S (Ap (V "f", V "x")))), Z)
    val exp6 = Fix (Ty.N, "n", S (V "n"))
    val _ = Dynamic.smallstep exp1
    val _ = Dynamic.smallstep exp2
    val _ = Dynamic.smallstep exp3
    val _ = Dynamic.smallstep exp4
    (* val _ = Dynamic.smallstep exp5 *) (*Loop forever...*)
    (* val _ = Dynamic.smallstep exp6 *) (*Loop forever*)
in
    ()
end;;
