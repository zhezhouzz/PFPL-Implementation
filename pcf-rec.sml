fun pLn s = print (s ^ "\n");
val counter = ref 0
fun newSym () =
    let
        val ret = "tmp" ^ (Int.toString (!counter))
        val _ = counter := ((!counter) + 1)
    in
        ret
    end
signature TY =
sig
    datatype t = Empty
               | Unit
               | TyV of string
               | Pf of t * t
               | Sum of t * t
               | Recursive of string * t
               | AnyTy
    val eq : t * t -> bool
    val layout: t -> string
    val subst : t * string * t -> t
end

structure Ty : TY =
struct
datatype t = Empty
           | Unit
           | TyV of string
           | Pf of t * t
           | Sum of t * t
           | Recursive of string * t
           | AnyTy
fun layout Empty = "0"
  | layout Unit = "1"
  | layout (TyV x) = x
  | layout (Pf (t1, t2)) = "(" ^ (layout t1) ^ "→" ^ (layout t2) ^ ")"
  | layout (Sum (t1, t2)) = "(" ^ (layout t1) ^ "+" ^ (layout t2) ^ ")"
  | layout (Recursive (x, t)) = "rec(" ^ x ^ "." ^ (layout t) ^ ")"
  | layout AnyTy = "_"
fun subst (body, x, v) =
    case body of
        Empty => Empty
      | Unit => Unit
      | AnyTy => AnyTy
      | Sum (t1, t2) => Sum (subst (t1, x, v), subst (t2, x, v))
      | Pf (t1, t2) => Pf (subst (t1, x, v), subst (t2, x, v))
      | TyV y => if x = y then v else TyV y
      | Recursive (y, body) =>
        if x = y then Recursive (y, body) else Recursive (y, subst (body, x, v))
fun eq (t1, t2) =
    case (t1, t2) of
        (Empty, Empty) => true
      | (Unit, Unit) => true
      | (TyV x, TyV x') => x = x'
      | (Pf (t11, t12), Pf (t21, t22)) =>
        (eq (t11, t21)) andalso (eq (t12, t22))
      | (Sum (t11, t12), Sum (t21, t22)) =>
        (eq (t11, t21)) andalso (eq (t12, t22))
      | (Recursive (x, t), Recursive (x', t')) =>
        let
            val tmp = newSym ()
        in
            (eq (subst (t, x, TyV tmp), subst (t', x, TyV tmp)))
        end
      | (AnyTy, _) => true
      | (_, AnyTy) => true
      | _ => false
end

signature E =
sig
    datatype t = Unit
               | In1 of t
               | In2 of t
               | Cases of t * string * t * t
               | Fold of string * Ty.t * t
               | Unfold of t
               | Cant of t
               | V of string
               | Lam of Ty.t * string * t
               | Ap of t * t
    val layout: t * bool -> string
    val subst: t * string * t -> t
end

structure E : E =
struct
datatype t = Unit
           | In1 of t
           | In2 of t
           | Cases of t * string * t * t
           | Fold of string * Ty.t * t
           | Unfold of t
           | Cant of t
           | V of string
           | Lam of Ty.t * string * t
           | Ap of t * t

(* fun tryNat Z = SOME 0 *)
(*   | tryNat (S v) = *)
(*     (case tryNat v of *)
(*          SOME n => SOME (n + 1) *)
(*       | NONE => NONE *)
(*     ) *)
(*   | tryNat _ = NONE *)

fun paren s = "(" ^ s ^ ")"
fun layout (Unit, _) = "()"
  | layout (In1 e, ifp) =
    let
        val s = "1·" ^ (layout (e, true))
    in
        if ifp then paren s else s
    end
  | layout (In2 e, ifp) =
    let
        val s = "2·" ^ (layout (e, true))
    in
        if ifp then paren s else s
    end
  | layout (Cases (e1, x, e2, e3), ifp) =
    let
        val s1 = layout (e1, false)
        val s2 = layout (e2, false)
        val s3 = layout (e3, false)
        val s = "case " ^ s1 ^ " of " ^ x ^ " => " ^ s2 ^ " | " ^ x ^ " => " ^ s3
    in
        if ifp then paren s else s
    end
  | layout (Cant e, ifp) =
    let
        val s = "cant " ^ (layout (e, true))
    in
        if ifp then paren s else s
    end
  | layout (Fold (alpha, t, e), _) =
    let
        val s = "fold[" ^ alpha ^ "." ^ (Ty.layout t) ^ "](" ^ (layout (e, false)) ^ ")"
    in
        s
    end
  | layout (Unfold e, _) =
    let
        val s = "unfold(" ^ (layout (e, true)) ^ ")"
    in
        s
    end
  | layout (V x, _) = x
  | layout (Lam (t, x, e), _) = "λ[" ^ (Ty.layout t) ^ "](" ^ x ^ ".(" ^ (layout (e, false)) ^ ")"
  | layout (Ap (e1, e2), ifp) =
    let
        val s = (layout (e1, true)) ^ " " ^ (layout (e2, true))
    in
        if ifp then paren s else s
    end

fun subst (body, x, v) =
    case body of
        Unit => Unit
      | In1 e => In1 (subst (e, x, v))
      | In2 e => In2 (subst (e, x, v))
      | Cases (e1, x', e2, e3) =>
        if x = x'
        then
            Cases (subst (e1, x, v), x', e2, e3)
        else
            Cases (subst (e1, x, v), x', subst (e2, x, v), subst (e3, x, v))
      | Fold (vart, t, e) => Fold (vart, t, subst (e, x, v))
      | Unfold e => Unfold (subst (e, x, v))
      | Cant e => Cant (subst (e, x, v))
      | V x' => if x = x' then v else V x'
      | Lam (t, x', e) =>
        if x = x'
        then
            Lam (t, x, e)
        else
            Lam (t, x', subst (e, x, v))
      | Ap (e1, e2) => Ap (subst (e1, x, v), subst (e2, x, v))
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

datatype staticTy =
         Exact of Ty.t
         | NoTy

fun static (gamma, e) =
    case e of
        Unit => Exact Ty.Unit
      | In1 e =>
        (case static (gamma, e) of
             Exact t => Exact (Ty.Sum (t, Ty.AnyTy))
           | _ => NoTy
        )
      | In2 e =>
        (case static (gamma, e) of
             Exact t => Exact (Ty.Sum (Ty.AnyTy, t))
           | _ => NoTy
        )
      | Cases (e1, x, e2, e3) =>
        (case static (gamma, e1) of
             Exact (Ty.Sum (t2, t3)) =>
             (case (static (update (gamma, x, t2), e2),
                    static (update (gamma, x, t3), e3)) of
                  (Exact t4, Exact t4') =>
                  if Ty.eq (t4, t4') then Exact t4 else NoTy
                | _ => NoTy
             )
           | _ => NoTy
        )
      | Cant e =>
        (case static (gamma, e) of
             Exact Ty.Empty => Exact Ty.AnyTy
           | _ => NoTy
        )
      | Fold (alpha, t, e) =>
        (case static (gamma, e) of
             Exact t' =>
             if Ty.eq (t', Ty.subst (t, alpha, Ty.Recursive (alpha, t)))
             then Exact (Ty.Recursive (alpha, t))
             else NoTy
           | _ => NoTy
        )
      | Unfold e =>
        (case static (gamma, e) of
             Exact (Ty.Recursive (alpha, t)) =>
             Exact (Ty.subst (t, alpha, Ty.Recursive (alpha, t)))
           | _ => NoTy
        )
      | V x =>
        (case gamma x of
             SOME t => Exact t
           | NONE => NoTy
        )
      | Lam (t, x, e) =>
        (case static (update (gamma, x, t), e) of
             Exact t' => Exact (Ty.Pf (t, t'))
           | NoTy => NoTy
        )
      | Ap (e1, e2) =>
        (case (static (gamma, e1), static (gamma, e2))of
             (Exact (Ty.Pf (t1, t2)), Exact t1') =>
             if Ty.eq (t1, t1') then Exact t2 else NoTy
           | _ => NoTy
        )
fun eval e =
    let
        val gamma = Gamma.empty
        val tyOpt = static (Gamma.empty, e)
        val tyStr =
            case tyOpt of
                Exact t => Ty.layout t
              | NoVty => "Type Error"
    in
        (E.layout (e, false)) ^ " : " ^ tyStr
    end
end

structure Dynamic =
struct

open E;

datatype value =
         VUnit
         | VIn1 of t
         | VIn2 of t
         | VLam of Ty.t * string * t
         | VFold of string * Ty.t * t

datatype thunk = Done of value
               | Computation of t

fun v2e VUnit = Unit
  | v2e (VIn1 e) = In1 e
  | v2e (VIn2 e) = In2 e
  | v2e (VLam (t, x, e)) = Lam (t, x, e)
  | v2e (VFold (vart, t, e)) = Fold (vart, t, e)

exception PCF_RUNTIME

fun step e =
    case e of
        Unit => Done VUnit
      | In1 e => Done (VIn1 e)
      | In2 e => Done (VIn2 e)
      | Lam (t, x, e) => Done (VLam (t, x, e))
      | Ap (e1, e2) =>
        (case step e1 of
             Computation e1 => Computation (Ap (e1, e2))
           | Done (VLam (t, x, e1)) =>
             Computation (subst (e1, x, e2))
           | _ => raise PCF_RUNTIME
        )
      | Fold (vart, t, e) => Done (VFold (vart, t, e))
      | Unfold e =>
        (case step e of
             Computation e => Computation (Unfold e)
           | Done (VFold (vart, t, e)) => Computation e
           | _ => raise PCF_RUNTIME
        )
      | V x => raise PCF_RUNTIME
      | Cant e => raise PCF_RUNTIME
      | Cases (e1, x, e2, e3) =>
        (case step e1 of
             Computation e1 => Computation (Cases (e1, x, e2, e3))
           | Done (VIn1 e1) => Computation (subst (e2, x, e1))
           | Done (VIn2 e1) => Computation (subst (e3, x, e1))
           | _ => raise PCF_RUNTIME
        )
fun smallstep e =
    let
        val _ = pLn (Static.eval e)
    in
        case step e of
            Done v =>  pLn ">>>> done <<<<"
          | Computation e => smallstep e
                                       (* | _ => raise Fail "Runtime Error" *)
    end

end

structure Macro =
struct
open E;
val tt = (In1 Unit)
val ff = (In2 Unit)
val zero = Fold ("t", Ty.Sum (Ty.Unit, Ty.TyV "t"), In1 Unit)
fun succ n = Fold ("t", Ty.Sum (Ty.Unit, Ty.TyV "t"), In2 n)
val one = succ zero
val two = succ one
val three = succ two
val Nat = Ty.Recursive ("t", Ty.Sum (Ty.Unit, Ty.TyV "t"))
fun ifz (e1, e2, x, e3) =
    Cases (Unfold e1, x, e2, e3)

fun selfty t =
    let
        val tmp = newSym ()
    in
        Ty.Recursive (tmp, Ty.Pf (Ty.TyV tmp,t))
    end

fun self (t, x, e) =
    let
        val recFuncTy = newSym ()
    in
        Fold(recFuncTy, Ty.Pf (Ty.TyV recFuncTy, t),
             Lam(Ty.Recursive (recFuncTy, Ty.Pf (Ty.TyV recFuncTy, t)), x,
                 e
                )
            )
    end

fun unroll selfFunc =
    Ap(Unfold(selfFunc), selfFunc)

fun selfap (selfFunc, e) =
    Ap(unroll selfFunc, e)
end

open E;
open Macro;

let
    (* val _ = pLn (Static.eval tt) *)
    (* val _ = pLn (Static.eval zero) *)
    (* val _ = pLn (Static.eval one) *)
    (* val _ = pLn (Static.eval two) *)
    (* val _ =  pLn (Static.eval (ifz (one, two, "x", three))) *)
    (* val _ =  pLn (Static.eval (Lam (Nat, "y", ifz (one, two, "x", V "y")))) *)
    val exp1 = ifz (one, two, "x", one)
    val fun1 = Lam (Nat, "z0", ifz (V "z0", two, "z1", V "z1"))
    val exp2 = Ap (fun1, exp1)
    val fun2 = self (Ty.Pf (Nat, Nat), "Yf",
                     Lam(Nat, "x",
                         ifz(V "x", zero, "y", selfap(V "Yf", V "y"))
                        )
                    )
    (* val fun2 = self (Ty.Pf (Nat, Nat), "Yf", *)
    (*                  Lam(Nat, "x", *)
    (*                      zero *)
    (*                     ) *)
    (*                 ) *)
    (* val _ = pLn (Static.eval fun2) *)
    val exp3 = selfap (fun2, three)
    (* val _ = Dynamic.smallstep exp2 *)
    val _ = Dynamic.smallstep exp3
in
    ()
end;;
