fun pLn s = print (s ^ "\n");
val counter = ref 0
fun paren s = "(" ^ s ^ ")"
fun angel s = "<" ^ s ^ ">"
fun newSym () =
    let
        val ret = "tmp" ^ (Int.toString (!counter))
        val _ = counter := ((!counter) + 1)
    in
        ret
    end
fun list2string f p l =
    let
        val r =
            List.foldl (fn (e, r) =>
                           case r of
                               NONE => SOME (f e)
                             | SOME r => SOME (r ^ p ^ (f e))
                       ) NONE l
    in
        case r of
            NONE => ""
          | SOME r => r
    end

structure Ty =
struct
datatype t = Unit
           | Int
           | Record of (string * t) list
           | Pf of t * t
fun layout (Unit, _) = "unit"
  | layout (Int, _) = "Int"
  | layout (Record l, _) = angel (list2string (fn (id, ty) => id ^ "↪ " ^ (layout (ty, false))) ", " l)
  | layout (Pf (t1, t2), ifp) =
    let
        val s = (layout (t1, true)) ^ "⇀" ^ (layout (t2, true))
    in
        if ifp then paren s else s
    end
        (* fun subst (body, x, v) = *)
        (*     case body of *)
        (*         Empty => Empty *)
        (*       | Unit => Unit *)
        (*       | AnyTy => AnyTy *)
        (*       | Sum (t1, t2) => Sum (subst (t1, x, v), subst (t2, x, v)) *)
        (*       | Pf (t1, t2) => Pf (subst (t1, x, v), subst (t2, x, v)) *)
        (*       | TyV y => if x = y then v else TyV y *)
        (*       | Recursive (y, body) => *)
        (*         if x = y then Recursive (y, body) else Recursive (y, subst (body, x, v)) *)
        (* fun eq (t1, t2) = *)
        (*     case (t1, t2) of *)
        (*         (Empty, Empty) => true *)
        (*       | (Unit, Unit) => true *)
        (*       | (TyV x, TyV x') => x = x' *)
        (*       | (Pf (t11, t12), Pf (t21, t22)) => *)
        (*         (eq (t11, t21)) andalso (eq (t12, t22)) *)
        (*       | (Sum (t11, t12), Sum (t21, t22)) => *)
        (*         (eq (t11, t21)) andalso (eq (t12, t22)) *)
        (*       | (Recursive (x, t), Recursive (x', t')) => *)
        (*         let *)
        (*             val tmp = newSym () *)
        (*         in *)
        (*             (eq (subst (t, x, TyV tmp), subst (t', x, TyV tmp))) *)
        (*         end *)
        (*       | (AnyTy, _) => true *)
        (*       | (_, AnyTy) => true *)
        (*       | _ => false *)
end

structure E =
struct
datatype t = Unit
           | Int of int
           | Record of (string * t) list
           | Field of t * string
           | Lam of string * t
           | Ap of t * t
           | V of string
           | Plus of t * t
           | Times of t * t
fun layout (Unit, _) = "()"
  | layout (Int n, _) = Int.toString n
  | layout (Record l, _) = angel (list2string (fn (id, e) => id ^ "↪ " ^ (layout (e, true))) ", " l)
  | layout (Field (e, id), _) = id ^ "·" ^ (layout (e, true))
  | layout (Lam (x, e), _) = "λ" ^ x ^ ".(" ^ (layout (e, false)) ^ ")"
  | layout (Ap (e1, e2), ifp) =
    let
        val s = (layout (e1, true)) ^ " " ^ (layout (e2, false))
    in
        if ifp then paren s else s
    end
  | layout (V x, _) = x
  | layout (Plus (e1, e2), ifp) =
    let
        val s = (layout (e1, true)) ^ " + " ^ (layout (e2, false))
    in
        if ifp then paren s else s
    end
  | layout (Times (e1, e2), ifp) =
    let
        val s = (layout (e1, true)) ^ " ⊗ " ^ (layout (e2, false))
    in
        if ifp then paren s else s
    end
fun subst (body: t, id, e) =
    let
        (* val _ = pLn ((layout (body, true)) ^ " " ^ id ^ " " ^ (layout (e, true))) *)
    in
        case body of
            Unit => Unit
          | Int n => Int n
          | Record l => Record (List.map (fn (id, x) => (id, subst (x, id, e))) l)
          | Field (body, id') => Field (subst (body, id, e), id')
          | Lam (x, body) =>
            if x = id
            then
                Lam (x, body)
            else
                Lam (x, subst (body, id, e))
          | Ap (body1, body2) =>
            Ap (subst (body1, id, e), subst (body2, id, e))
          | V x => if x = id then e else V x
          | Plus (body1, body2) =>
            Plus (subst (body1, id, e), subst (body2, id, e))
          | Times (body1, body2) =>
            Times (subst (body1, id, e), subst (body2, id, e))
    end
end

structure Dynamic =
struct
open E

fun findInRecord (l, id) =
    let
        val r =
            List.foldl (fn ((id', e'), r) =>
                           if id = id'
                           then
                               case r of
                                   NONE => SOME e'
                                 | SOME _ => raise Fail ("Duplicated Filed: " ^ id)
                           else
                               r
                       ) NONE l
    in
        case r of
            NONE => raise Fail ("Can't find the field: " ^ id)
          | SOME r => r
    end
datatype d = Done of t
           | Computation of t
fun step e =
    case e of
        Unit => Done Unit
      | Int n => Done (Int n)
      | Record l => Done (Record l)
      | Field (e, id) =>
        (case step e of
             Done e =>
             (case e of
                  Record l => Computation (findInRecord (l, id))
                | _ => raise Fail "Not a record term"
             )
           | Computation e => Computation (Field (e, id))
        )
      | Lam (x, e) => Done (Lam (x, e))
      | Ap (e1, e2) =>
        (case step e1 of
             Computation e1 => Computation (Ap (e1, e2))
           | Done (Lam (x, e1)) =>
             (case step e2 of
                  Computation e2 => Computation (Ap (Lam (x, e1), e2))
                | Done e2 => Computation (subst (e1, x, e2))
             )
           | _ => raise Fail "Not a λ term"
        )
      | V x => raise Fail ("Unbound variable: " ^ x)
      | Plus (e1, e2) =>
        (case step e1 of
             Computation e1 => Computation (Plus (e1, e2))
           | Done (Int n1) =>
             (case step e2 of
                  Computation e2 => Computation (Plus (Int n1, e2))
                | Done (Int n2) => Computation (Int (n1 + n2))
                | _ => raise Fail "Not a int term after +"
             )
           | _ => raise Fail "Not a int term before +"
        )
      | Times (e1, e2) =>
        (case step e1 of
             Computation e1 => Computation (Times (e1, e2))
           | Done (Int n1) =>
             (case step e2 of
                  Computation e2 => Computation (Times (Int n1, e2))
                | Done (Int n2) => Computation (Int (n1 * n2))
                | _ => raise Fail "Not a int term after ×"
             )
           | _ => raise Fail "Not a int term before ×"
        )
fun smallstep e =
    let
        val _ = pLn (layout (e, false))
    in
        case step e of
            Done e => pLn ">>>> done <<<<"
          | Computation e => smallstep e
    end
end;

open E;
open Dynamic;

val distCart =
    let
        val r = newSym ()
    in
        Lam (r, Plus (Field (V r, "x"), Field (V r, "y")))
    end
val lenCart =
    let
        val r = newSym ()
    in
        Lam (r, Times (Field (V r, "x"), Field (V r, "y")))
    end
val distPol =
    let
        val r = newSym ()
    in
        Lam (r, Field (V r, "r"))
    end
val lenPol =
    let
        val r = newSym ()
    in
        Lam (r, Field (V r, "th"))
    end

structure ObjectBased =
struct
open E;
fun objectVector data =
    let
        val cart = Record [("dist", Ap (distCart, data)), ("len", Ap (lenCart, data))]
        val pol = Record [("dist", Ap (distPol, data)), ("len", Ap (lenPol, data))]
    in
        Record [("cart", cart), ("pol", pol)]
    end
fun new (c, data) =
    let
        val method = newSym ()
    in
        Field (objectVector data, c)
    end
fun call (obj, method) =
    Field (obj, method)
end

structure MethodBased =
struct
open E;
val methodVector =
    let
        val dist = Record [("cart", distCart), ("pol", distPol)]
        val len = Record [("cart", lenCart), ("pol", lenPol)]
    in
        Record [("dist", dist), ("len", len)]
    end
fun new (c, data) =
    let
        val method = newSym ()
    in
        Lam (method, Ap (Field (V method, c), data))
    end
fun call (obj, method) =
    Ap (obj, Field (methodVector, method))
end

open ObjectBased;
let
    val pointCart = Record [("x", Int 1), ("y", Int 1)]
    val obj = new ("cart", pointCart)
    val exp = call (obj, "dist")
    val _ = smallstep exp
in
    ()
end;

open MethodBased;
let
    val pointCart = Record [("x", Int 1), ("y", Int 1)]
    val obj = new ("cart", pointCart)
    val exp = call (obj, "dist")
    val _ = smallstep exp
in
    ()
end;
