fun pLn s = print (s ^ "\n");
fun paren s = "(" ^ s ^ ")"
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
               | Comp of t
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
           | Comp of t
           | AnyTy
fun layout Empty = "0"
  | layout Unit = "1"
  | layout (TyV x) = x
  | layout (Pf (t1, t2)) = "(" ^ (layout t1) ^ "→" ^ (layout t2) ^ ")"
  | layout (Sum (t1, t2)) = "(" ^ (layout t1) ^ "+" ^ (layout t2) ^ ")"
  | layout (Recursive (x, t)) = "rec(" ^ x ^ "." ^ (layout t) ^ ")"
  | layout (Comp t) = "comp(" ^ (layout t) ^ ")"
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
      | Comp body => Comp (subst (body, x, v))
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
      | (Comp t1, Comp t2) => eq (t1, t2)
      | (AnyTy, _) => true
      | (_, AnyTy) => true
      | _ => false
end

signature E =
sig
    datatype v = Unit
               | In1 of v
               | In2 of v
               | V of string
               | Lam of Ty.t * string * m
               | Fold of string * Ty.t * v
               | Comp of m
         and m = Ret of v
               | Bnd of v * string * m
               | Unfold of v
               | Cant of v
               | Cases of v * string * m * m
               | Ap of v * v
    val layoutv: v * bool -> string
    val layoutm: m * bool -> string
    val substv: v * string * v -> v
    val substm: m * string * v -> m
end

structure E : E =
struct
datatype v = Unit
           | In1 of v
           | In2 of v
           | V of string
           | Lam of Ty.t * string * m
           | Fold of string * Ty.t * v
           | Comp of m
     and m = Ret of v
           | Bnd of v * string * m
           | Unfold of v
           | Cant of v
           | Cases of v * string * m * m
           | Ap of v * v

fun layoutv (Unit, _) = "()"
  | layoutv (In1 v, ifp) =
    let
        val s = "1·" ^ (layoutv (v, true))
    in
        if ifp then paren s else s
    end
  | layoutv (In2 v, ifp) =
    let
        val s = "2·" ^ (layoutv (v, true))
    in
        if ifp then paren s else s
    end
  | layoutv (Fold (alpha, t, v), _) =
    let
        val s = "fold[" ^ alpha ^ "." ^ (Ty.layout t) ^ "](" ^ (layoutv (v, false)) ^ ")"
    in
        s
    end
  | layoutv (V x, _) = x
  | layoutv (Lam (t, x, m), _) = "λ[" ^ (Ty.layout t) ^ "](" ^ x ^ ".(" ^ (layoutm (m, false)) ^ ")"
  | layoutv (Comp m, _) = "comp(" ^ (layoutm (m, false))  ^ ")"
and layoutm (Cases (v1, x, m2, m3), ifp) =
    let
        val s1 = layoutv (v1, false)
        val s2 = layoutm (m2, false)
        val s3 = layoutm (m3, false)
        val s = "case " ^ s1 ^ " of " ^ x ^ " => " ^ s2 ^ " | " ^ x ^ " => " ^ s3
    in
        if ifp then paren s else s
    end
  | layoutm (Cant v, ifp) =
    let
        val s = "cant " ^ (layoutv (v, true))
    in
        if ifp then paren s else s
    end
  | layoutm (Unfold v, _) =
    let
        val s = "unfold(" ^ (layoutv (v, true)) ^ ")"
    in
        s
    end
  | layoutm (Ap (v1, v2), ifp) =
    let
        val s = (layoutv (v1, true)) ^ " " ^ (layoutv (v2, true))
    in
        if ifp then paren s else s
    end
  | layoutm (Ret v1, _) = "ret(" ^ (layoutv (v1, false))  ^ ")"
  | layoutm (Bnd (v1, x, m), _) = "bnd(" ^ x ^ "← " ^ (layoutv (v1, true)) ^ ";" ^ (layoutm (m, false))  ^ ")"

fun substv (body, x, value) =
    case body of
        Unit => Unit
      | In1 v => In1 (substv (v, x, value))
      | In2 v => In2 (substv (v, x, value))
      | Fold (vart, t, v) => Fold (vart, t, substv (v, x, value))
      | V x' => if x = x' then value else V x'
      | Lam (t, x', m) =>
        if x = x'
        then
            Lam (t, x', m)
        else
            Lam (t, x', substm (m, x, value))
      | Comp m => Comp (substm (m, x, value))
and substm (body, x, value) =
    case body of
        Cases (v1, x', m2, m3) =>
        if x = x'
        then
            Cases (substv (v1, x, value), x', m2, m3)
        else
            Cases (substv (v1, x, value), x', substm (m2, x, value), substm (m3, x, value))
      | Unfold v => Unfold (substv (v, x, value))
      | Cant v => Cant (substv (v, x, value))
      | Ap (v1, v2) => Ap (substv (v1, x, value), substv (v2, x, value))
      | Ret v => Ret (substv (v, x, value))
      | Bnd (v1, x', m2) =>
        if x = x'
        then
            Bnd (substv (v1, x, value), x', m2)
        else
            Bnd (substv (v1, x, value), x', substm (m2, x, value))
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

datatype vTy =
         Strict of Ty.t
         | NoVTy

datatype mTy =
         Weak of Ty.t
         | NoMTy

fun staticv (gamma, v) =
    case v of
        Unit => Strict Ty.Unit
      | In1 v =>
        (case staticv (gamma, v) of
             Strict t => Strict (Ty.Sum (t, Ty.AnyTy))
           | _ => NoVTy
        )
      | In2 v =>
        (case staticv (gamma, v) of
             Strict t => Strict (Ty.Sum (Ty.AnyTy, t))
           | _ => NoVTy
        )
      | Fold (alpha, t, v) =>
        (case staticv (gamma, v) of
             Strict t' =>
             if Ty.eq (t', Ty.subst (t, alpha, Ty.Recursive (alpha, t)))
             then Strict (Ty.Recursive (alpha, t))
             else NoVTy
           | _ => NoVTy
        )
      | V x =>
        (case gamma x of
             SOME t => Strict t
           | NONE => NoVTy
        )
      | Lam (t, x, m) =>
        (case staticm (update (gamma, x, t), m) of
             Weak t' => Strict (Ty.Pf (t, t'))
           | NoMTy => NoVTy
        )
      | Comp m =>
        (case staticm (gamma, m) of
             Weak t' => Strict (Ty.Comp t')
           | NoMTy => NoVTy
        )
and staticm (gamma, m) =
    case m of
        Ret v =>
        (case staticv (gamma, v) of
             Strict t => Weak t
           | _ => NoMTy
        )
      | Cases (v1, x, m2, m3) =>
        (case staticv (gamma, v1) of
             Strict (Ty.Sum (t2, t3)) =>
             (case (staticm (update (gamma, x, t2), m2),
                    staticm (update (gamma, x, t3), m3)) of
                  (Weak t4, Weak t4') =>
                  if Ty.eq (t4, t4') then Weak t4 else NoMTy
                | _ => NoMTy
             )
           | _ => NoMTy
        )
      | Cant v =>
        (case staticv (gamma, v) of
             Strict Ty.Empty => Weak Ty.AnyTy
           | _ => NoMTy
        )
      | Unfold v =>
        (case staticv (gamma, v) of
             Strict (Ty.Recursive (alpha, t)) =>
             Weak (Ty.subst (t, alpha, Ty.Recursive (alpha, t)))
           | _ => (print "Static Unfold Error\n"; NoMTy)
        )
      | Ap (v1, v2) =>
        (case (staticv (gamma, v1), staticv (gamma, v2))of
             (Strict (Ty.Pf (t1, t2)), Strict t1') =>
             if Ty.eq (t1, t1') then Weak t2 else NoMTy
           | (Strict t1, Strict t2) => (print "Static Ap Error\n";
                                        pLn (layoutm (Ap (v1, v2), false));
                                        pLn (Ty.layout t1);
                                        pLn (Ty.layout t2);
                                        NoMTy)
           | _ => NoMTy
        )
      | Bnd (v, x, m) =>
        (case staticv (gamma, v) of
             Strict (Ty.Comp t) =>
             (case staticm (update (gamma, x, t), m) of
                  Weak t' => Weak t'
                | _ => (print "Static Bnd[1] Error\n"; NoMTy)
             )
           | _ => (print "Static Bnd[2] Error\n"; NoMTy)
        )
fun evalv v =
    let
        val gamma = Gamma.empty
        val tyOpt = staticv (Gamma.empty, v)
        val tyStr =
            case tyOpt of
                Strict t => "{Strict} " ^ (Ty.layout t)
              | NoVty => "Type Error"
    in
        (E.layoutv (v, false)) ^ " : " ^ tyStr
    end
fun evalm m =
    let
        val gamma = Gamma.empty
        val tyOpt = staticm (Gamma.empty, m)
        val tyStr =
            case tyOpt of
                Weak t => "{Weak} " ^ (Ty.layout t)
              | NoMty => "Type Error"
    in
        (E.layoutm (m, false)) ^ " : " ^ tyStr
    end
end

structure Dynamic =
struct

open E;

datatype thunk = Done of m
               | Computation of m

exception PCF_RUNTIME

fun stepm m =
    case m of
        Ap (v1, v2) =>
        (case v1 of
             Lam (t, x, m1) => Computation (substm (m1, x, v2))
           | _ => raise PCF_RUNTIME
        )
      | Unfold v =>
        (case v of
             Fold (_, _, v) => Done (Ret v)
           | _ => raise PCF_RUNTIME
        )
      | Cant v => raise PCF_RUNTIME
      | Cases (v1, x, m2, m3) =>
        (case v1 of
             (In1 v1) => Computation (substm (m2, x, v1))
           | (In2 v1) => Computation (substm (m3, x, v1))
           | _ => raise PCF_RUNTIME
        )
      | Ret v => Done (Ret v)
      | Bnd (v1, x, m2) =>
        (case v1 of
             Comp m1 =>
             (case stepm m1 of
                  Done (Ret v1) => Computation (substm (m2, x, v1))
                | Computation m1 => Computation (Bnd (Comp m1, x, m2))
                | _ => raise PCF_RUNTIME
             )
           | _ => raise PCF_RUNTIME
        )
fun smallstep m =
    let
        val _ = pLn (Static.evalm m)
    in
        case stepm m of
            Done (Ret v) => pLn ">>>> done <<<<"
          | Computation m => smallstep m
          | _ => raise Fail "Runtime Error"
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
    let
        val tmp = newSym ()
    in
        Bnd (Comp (Unfold e1), tmp, Cases (V tmp, x, e2, e3))
    end

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
        Fold(recFuncTy, Ty.Pf (Ty.TyV recFuncTy, Ty.Comp t),
             Lam(Ty.Recursive (recFuncTy, Ty.Pf (Ty.TyV recFuncTy, Ty.Comp t)), x,
                 Ret (Comp e)
                )
            )
    end

fun unroll selfFunc =
    let
        val tmp = newSym ()
        val tmp' = newSym ()
    in
        Bnd (Comp (Unfold selfFunc), tmp,
             Bnd (Comp (Ap(V tmp, selfFunc)), tmp',
                  Ret (V tmp')
                 )
            )
    end

fun selfap (selfFunc, e) =
    let
        val tmp = newSym ()
        val tmp' = newSym ()
    in
        Bnd (Comp (unroll selfFunc), tmp, Bnd (V tmp, tmp', Ap(V tmp', e)))
    end
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
    val x1 = newSym ()
    val x2 = newSym ()
    val x3 = newSym ()
    val x4 = newSym ()
    val x5 = newSym ()
    val x6 = newSym ()
    (* val exp1 = ifz (one, Ret two, "x", Ret one) *)
    (* val fun1 = Lam (Nat, "z1", ifz (V "z1", Ret two, "z2", Ret (V "z2"))) *)
    (* val exp2 = Bnd (Comp (exp1), "z0", Ap (fun1, V "z0")) *)
    val fun2 = self (Ty.Pf (Nat, Nat), "Yf",
                     Ret(
                         Lam(Nat, "x",
                             ifz(V "x", Ret zero, "y", selfap(V "Yf", V "y"))
                            )
                     )
                    )
    (* val fun2 = self (Ty.Pf (Nat, Nat), "Yf", *)
    (*                  Ret( *)
    (*                      Lam(Nat, x1, *)
    (*                          ifz(V x1, Ret zero, x2, *)
    (*                              Bnd (Comp ( *)
    (*                                        Bnd (Comp (Unfold (V "Yf")), x4, *)
    (*                                             Bnd (Comp (Ap(V x4, V "Yf")), x5, *)
    (*                                                  Ret (V x5) *)
    (*                                                 ) *)
    (*                                            ) *)
    (*                                    ), x3, Ap(V x3, V x2)) *)
    (*                             ) *)
    (*                         ) *)
    (*                  ) *)
    (*                 ) *)
    (* val fun2 = *)
    (*     Fold("N2NSelf", Ty.Pf (Ty.TyV "N2NSelf", Ty.Comp (Ty.Pf (Nat, Nat))), *)
    (*          Lam(Ty.Recursive ("N2NSelf", Ty.Pf (Ty.TyV "N2NSelf", Ty.Comp (Ty.Pf (Nat, Nat)))), "Yf", *)
    (*              Ret (Comp *)
    (*                       (Ret( *)
    (*                             Lam(Nat, x1, *)
    (*                                 ifz(V x1, Ret zero, x2, *)
    (*                                     Bnd (Comp ( *)
    (*                                               Bnd (Comp (Unfold (V "Yf")), x4, *)
    (*                                                    Bnd (Comp (Ap(V x4, V "Yf")), x5, *)
    (*                                                         Ret (V x5) *)
    (*                                                        ) *)
    (*                                                   ) *)
    (*                                           ), x3, Bnd (V x3, x6, Ap(V x6, V x2))) *)
    (*                                    ) *)
    (*                                ) *)
    (*                         ) *)
    (*                       ) *)
    (*                  ) *)
    (*             ) *)
    (*         ) *)
    val _ = pLn (Static.evalv fun2)
                val exp3 = selfap (fun2, two)
                (* val _ = Dynamic.smallstep exp1 *)
                (* val _ = Dynamic.smallstep exp2 *)
                val _ = Dynamic.smallstep exp3
in
    ()
end;;
