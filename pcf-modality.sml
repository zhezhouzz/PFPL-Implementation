fun pLn s = print (s ^ "\n");

signature TY =
sig
    datatype t = N
               | Pf of t * t
               | Comp of t
    val eq : t * t -> bool
    val layout: t -> string
end

structure Ty : TY =
struct
datatype t = N
           | Pf of t * t
           | Comp of t
fun eq (t1, t2) =
    case (t1, t2) of
        (N, N) => true
      | (Pf (t11, t12), Pf (t21, t22)) =>
        (eq (t11, t21)) andalso (eq (t12, t22))
      | (Comp t1, Comp t2) => eq (t1, t2)
      | _ => false
fun layout N = "N"
  | layout (Pf (t1, t2)) = "(" ^ (layout t1) ^ "→" ^ (layout t2) ^ ")"
  | layout (Comp t1) = "(" ^ (layout t1) ^ " comp)"
end

signature E =
sig
    datatype tv = Z
                | S of tv
                | V of string
                | Lam of Ty.t * string * tm
                | Comp of Ty.t * string * tm
         and tm = Ifz of tv * tm * string * tm
                | Ap of tv * tv
                | Ret of tv
                | Bnd of tv * string * tm
    val layoutv: tv * bool -> string
    val layoutm: tm * bool -> string
    val substv: tv * string * tv -> tv
    val substm: tm * string * tv -> tm
end

structure E : E =
struct
datatype tv = Z
            | S of tv
            | V of string
            | Lam of Ty.t * string * tm
            | Comp of Ty.t * string * tm
     and tm = Ifz of tv * tm * string * tm
            | Ap of tv * tv
            | Ret of tv
            | Bnd of tv * string * tm

fun tryNat Z = SOME 0
  | tryNat (S v) =
    (case tryNat v of
         SOME n => SOME (n + 1)
      | NONE => NONE
    )
  | tryNat _ = NONE

fun layoutv Z = "0"
  | layoutv (S n) =
    (case tryNat (S n) of
         SOME n => Int.toString n
       | NONE => "(S " ^ (layoutv n) ^ ")"
    )
  | layoutv (V x) = x
  | layoutv (Lam (t, x, m)) = "λ[" ^ (Ty.layout t) ^ "](" ^ x ^ "." ^ (layoutm m) ^ ")"
  | layoutv (Comp (t, x, m)) = "comp[" ^ (Ty.layout t) ^ "](" ^ x ^ "." ^ (layoutm m) ^ ")"
and layoutm (Ifz (v1, m1, x, m2)) = "(ifz " ^ (layoutv v1) ^ " then " ^ (layoutm m1) ^ " else " ^ x ^ "." ^ (layoutm m2) ^ ")"
  | layoutm (Ap (v1, v2)) = "(" ^ (layoutv v1) ^ " " ^ (layoutv v2) ^ ")"
  | layoutm (Ret v) = "(ret " ^ (layoutv v) ^ ")"
  | layoutm (Bnd (v1, x, m2)) = "(" ^ x ^ "← " ^ (layoutv v1) ^ "; " ^ (layoutm m2) ^ ")"

fun layoutv (Z, _) = "0"
  | layoutv (S n, ifp) =
    (case tryNat (S n) of
         SOME n => Int.toString n
       | NONE => if ifp then "(S " ^ (layoutv (n, false)) ^ ")" else "S" ^ (layoutv (n, false))
    )
  | layoutv (V x, _) = x
  | layoutv (Lam (t, x, m), _) = "λ[" ^ (Ty.layout t) ^ "](" ^ x ^ "." ^ (layoutm (m, false)) ^ ")"
  | layoutv (Comp (t, x, m), _) = "comp[" ^ (Ty.layout t) ^ "](" ^ x ^ "." ^ (layoutm (m, false)) ^ ")"
and layoutm (Ifz (v1, m1, x, m2), ifp) =
    if ifp then
        "(ifz " ^ (layoutv (v1, false)) ^ " then " ^ (layoutm (m1, false)) ^ " else " ^ x ^ "." ^ (layoutm (m2, true)) ^ ")"
    else
        "ifz " ^ (layoutv (v1, false)) ^ " then " ^ (layoutm (m1, false)) ^ " else " ^ x ^ "." ^ (layoutm (m2, true))
  | layoutm (Ap (v1, v2), ifp) =
    if ifp then
        "(" ^ (layoutv (v1, true)) ^ " " ^ (layoutv (v2, true)) ^ ")"
    else
        (layoutv (v1, true)) ^ " " ^ (layoutv (v2, true))
  | layoutm (Ret v, ifp) =
    if ifp then
        "(ret " ^ (layoutv (v, true)) ^ ")"
    else
        "ret " ^ (layoutv (v, true))
  | layoutm (Bnd (v1, x, m2), ifp) =
    if ifp then
        "(" ^ x ^ "← " ^ (layoutv (v1, false)) ^ "; " ^ (layoutm (m2, false)) ^ ")"
    else
        x ^ "← " ^ (layoutv (v1, false)) ^ "; " ^ (layoutm (m2, false))

(* fun spaces n = *)
(*     case n of *)
(*         0 => "" *)
(*       | S n => (spaces n) ^ " " *)
(* val tab n = 2 + n *)

fun substv (v, id, vid) =
    case v of
        Z => Z
      | S v => S (substv (v, id, vid))
      | V id' =>
        if id = id' then vid else V id'
      | Lam (t, x, m1) =>
        if x = id
        then Lam (t, x, m1)
        else Lam (t, x, substm (m1, id, vid))
      | Comp (t, x, m1) =>
        if x = id
        then Comp (t, x, m1)
        else Comp (t, x, substm (m1, id, vid))
and substm (m, id, vid) =
    case m of
        Ifz (v1, m2, x, m3) =>
        if x = id
        then Ifz (substv (v1, id, vid), substm (m2, id, vid), x, m3)
        else Ifz (substv (v1, id, vid), substm (m2, id, vid), x, substm (m3, id, vid))
      | Ap (v1, v2) => Ap (substv (v1, id, vid), substv (v2, id, vid))
      | Ret v => Ret (substv (v, id, vid))
      | Bnd (v1, x, m2) =>
        if x = id
        then Bnd (substv (v1, id, vid), x, m2)
        else Bnd (substv (v1, id, vid), x, substm (m2, id, vid))
end

structure Gamma =
struct
type t = string -> Ty.t option

val empty = fn _ => NONE
fun update (gamma, x, t) = fn y => if x = y then SOME t else gamma y
fun get (gamma, y) = gamma y
end

structure Static =
struct

open E
open Gamma

datatype vty =
         Strict of Ty.t
         | NoVty

datatype mty =
         Weak of Ty.t
         | NoMty

fun staticv (gamma, v) =
    case v of
        Z => Strict Ty.N
      | S v =>
        (case staticv (gamma, v) of
             Strict Ty.N => Strict Ty.N
           | _ => NoVty)
      | V id =>
        (case gamma id of
             SOME t => Strict t
           | NONE => NoVty
        )
      | Lam (t, x, m) =>
        (case staticm (update (gamma, x, t), m) of
             Weak t' => Strict (Ty.Pf (t, t'))
           | _ => NoVty
        )
      | Comp (t, x, m) =>
        (case staticm (update (gamma, x, Ty.Comp t), m) of
             Weak t' =>
             if Ty.eq (t, t') then Strict (Ty.Comp t) else NoVty
           | _ => NoVty
        )
and staticm (gamma, m) =
    case m of
        Ifz (v1, m2, x, m3) =>
        (case (staticv (gamma, v1), staticm (gamma, m2),
               staticm (update (gamma, x, Ty.N), m3)) of
             (Strict N, Weak t2, Weak t3) =>
             if Ty.eq (t2, t3) then Weak t2 else NoMty
           | _ => NoMty
        )
      | Ap (v1, v2) =>
        (case (staticv (gamma, v1), staticv (gamma, v2)) of
             (Strict (Ty.Pf (t1, t2)), Strict t3) =>
             if Ty.eq (t1, t3) then Weak t2 else NoMty
           | _ => NoMty
        )
      | Ret v =>
        (case staticv (gamma, v) of
             Strict t => Weak t
           | _ => NoMty)
      | Bnd (v1, x, m2) =>
        (case (staticv (gamma, v1)) of
             Strict (Ty.Comp t) =>
             (case staticm (update (gamma, x, t), m2) of
                  Weak t' => Weak t'
                | _ => NoMty
             )
           | _ => NoMty
        )
fun evalm e =
    let
        val gamma = Gamma.empty
        val tyOpt = staticm (Gamma.empty, e)
        val tyStr =
            case tyOpt of
                Weak t => "{weak} " ^ (Ty.layout t)
              | NoMty => "Type Error"
    in
        (E.layoutm (e, false)) ^ " : " ^ tyStr
    end
fun evalv e =
    let
        val gamma = Gamma.empty
        val tyOpt = staticv (Gamma.empty, e)
        val tyStr =
            case tyOpt of
                Strict t => "{strict} " ^ (Ty.layout t)
              | NoVty => "Type Error"
    in
        (E.layoutv (e, false)) ^ " : " ^ tyStr
    end
end

structure Dynamic =
struct

datatype thunk = Done of E.tm
               | Computation of E.tm

exception PCF_RUNTIME

fun stepm m =
    case m of
        E.Ifz (v1, m2, x, m3) =>
        (case v1 of
             E.Z => Computation m2
           | E.S v1 => Computation (E.substm (m3, x, v1))
           | _ => raise PCF_RUNTIME
        )
      | E.Ap (v1, v2) =>
        (case v1 of
             E.Lam (t, x, m1) => Computation (E.substm (m1, x, v2))
           | _ => raise PCF_RUNTIME
        )
      | E.Ret v => Done (E.Ret v)
      | E.Bnd (v1, x, m2) =>
        (case v1 of
             E.Comp (t, y, m1) =>
             (case stepm (E.substm (m1, y, E.Comp (t, y, m1))) of
                  Done (E.Ret v1) =>
                  let
                      val v1 = E.substv (v1, x, v1)
                  in
                      Computation (E.substm (m2, x, v1))
                  end
                | Computation m1 => Computation (E.Bnd (E.Comp (t, y, m1), x, m2))
                | _ => raise Fail "Runtime Error: Bnd"
             )
           | _ => raise Fail "Runtime Error: Bnd"
        )

fun smallstep m =
    let
        val _ = pLn (Static.evalm m)
    in
        case stepm m of
            Done (E.Ret v) =>  pLn ">>>> done <<<<"
          | Computation m => smallstep m
          | _ => raise Fail "Runtime Error: Bnd"
    end

end

structure Macro =
struct
open E;
val Nat = Ty.N
fun TyC t = Ty.Comp t
val NatComp = TyC Nat
val Nat2Nat = Ty.Pf (Nat, Nat)
fun Comp0 (t, m) = Comp (t, "neverused", m)
val One = S Z
val Two = S One
val Three = S Two
val Four = S Three
val x = V "x"
val x0 = V "x0"
val x1 = V "x1"
val x2 = V "x2"
val x3 = V "x3"
val x4 = V "x4"
val x5 = V "x5"
val f0 = V "f0"
val f1 = V "f1"
val f2 = V "f2"
val f3 = V "f3"
end

open E;
open Macro;

let
    val exp1 = Ifz (Two, Ret Z, "x1", Ret x1)
    val _ = pLn (Static.evalm exp1)
    val exp2 = Lam (Nat, "x0", Ifz (Three, Ret Z, "x1", Ret x1))
    val _ = pLn (Static.evalv exp2)
    val exp3 = Lam (Nat, "x0", Ifz (Three, Ret Z, "x1", Ret x2))
    val _ = pLn (Static.evalv exp3)
    val exp4 = Bnd (Comp0 (NatComp, Ret (Comp0 (Nat, Ifz (Two, Ret Z, "x0", Ret x0)))), "x0", Bnd (x0, "x1", Ret x1))
    val _ = pLn (Static.evalm exp4)
    val exp5 = Comp (Nat2Nat, "f0",
                     Ret (Lam (Nat, "x0",
                               Ifz (x0, Ret Z, "x1",
                                    Bnd (f0, "x2", Ap (x2, x1))
                                   )
                              )
                         )
                    )
    val exp5 = Bnd (exp5, "g", Ap (V "g", Three))
    val exp6 = Bnd (Comp (Ty.Pf (Nat, Nat), "r", Ret(Lam (Nat, "y", Ifz (S(S(S Z)), Ret Z, "x", Ret (V "y"))))), "g", Ap (V "g", S(S(S Z))))
    val _ = pLn (Static.evalm exp5)
    val _ = pLn (Static.evalm exp6)
    val _ = Dynamic.smallstep exp1
    val _ = Dynamic.smallstep exp4
    val _ = Dynamic.smallstep exp5
    val _ = Dynamic.smallstep exp6
in
    ()
end;;
