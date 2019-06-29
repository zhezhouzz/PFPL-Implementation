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
           | Fold of t
           | Unfold of t
fun layout (Unit, _) = "()"
  | layout (Int n, _) = Int.toString n
  | layout (Record l, _) = angel (list2string (fn (id, e) => id ^ "↪ " ^ (layout (e, true))) ", " l)
  | layout (Field (e, id), _) = id ^ "·" ^ (layout (e, true))
  | layout (Lam (x, e), _) = "λ" ^ x ^ ".(" ^ (layout (e, false)) ^ ")"
  | layout (Ap (e1, e2), ifp) =
    let
        val s = (layout (e1, true)) ^ " " ^ (layout (e2, true))
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
  | layout (Fold e, _) = "fold(" ^ (layout (e, false)) ^ ")"
  | layout (Unfold e, _) = "unfold(" ^ (layout (e, false)) ^ ")"
fun subst (body: t, id, e) =
    let
        (* val _ = pLn ((layout (body, true)) ^ " " ^ id ^ " " ^ (layout (e, true))) *)
    in
        case body of
            Unit => Unit
          | Int n => Int n
          | Record l => Record (List.map (fn (id', x) => (id', subst (x, id, e))) l)
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
          | Fold body => Fold (subst (body, id, e))
          | Unfold body => Unfold (subst (body, id, e))
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
                | _ => raise Fail "Not a int term after ⊗"
             )
           | _ => raise Fail "Not a int term before ⊗"
        )
      | Fold e => Done (Fold e)
      | Unfold e =>
        (case step e of
             Computation e => Computation (Unfold e)
           | Done (Fold e) => Computation e
           | _ => (pLn (layout (e, false)); raise Fail "Unfold a no fold term")
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
val objectVector =
    let
        val data = newSym ()
        val cart = Record [("dist", Ap (distCart, V data)), ("len", Ap (lenCart, V data))]
        val pol = Record [("dist", Ap (distPol, V data)), ("len", Ap (lenPol, V data))]
    in
        Lam (data, Record [("cart", cart), ("pol", pol)])
    end
fun new (c, data) =
    let
        val method = newSym ()
    in
        Field (Ap (objectVector, data), c)
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

fun self (Yf, e) = Fold (Lam (Yf, e))
fun unroll e = Ap (Unfold e, e)
val distCartSelf =
    let
        val r = newSym ()
        val cv = newSym ()
        val mv = newSym ()
    in
        Lam (cv,
             Lam (mv,
                  Lam (r, Plus (Field (V r, "x"), Field (V r, "y")))
                 )
            )
    end
val lenCartSelf =
    let
        val r = newSym ()
        val cv = newSym ()
        val mv = newSym ()
    in
        Lam (cv,
             Lam (mv,
                  Lam (r,
                       Ap (Field (V mv, "len"), (Ap (Field (V cv, "cart"), V r)))
                       (* Record (Field (unroll (V cv), "cart"), V r) *)
                       (* Ap (Field (unroll (V cv), "cart"), V r) *)
                      (* V cv *)
                      )
                 )
            )
    end
val distPolSelf =
    let
        val r = newSym ()
        val cv = newSym ()
        val mv = newSym ()
    in
        Lam (cv,
             Lam (mv,
                  Lam (r, Field (V r, "r"))
                 )
            )
    end
val lenPolSelf =
    let
        val r = newSym ()
        val cv = newSym ()
        val mv = newSym ()
    in
        Lam (cv,
             Lam (mv,
                  Lam (r, (Ap (Field (V mv, "dist"), V r)))
                 )
            )
    end

structure ObjectBasedSelf =
struct
open E;
val emv =
    let
        val this = newSym ()
    in
        Record [("dist", Lam (this, Field (V this, "dist"))),
                ("len", Lam (this, Field (V this, "len")))]
    end
val ecv =
    let
        val this = newSym ()
        val data = newSym ()
        val cart = Lam (data,
                        Record [
                            ("dist", Ap (Ap (Ap (distCartSelf, unroll (V this)), emv), V data)),
                            ("len", Ap (Ap (Ap (lenCartSelf, unroll (V this)), emv), V data))
                        ]
                       )
        val pol = Lam (data,
                        Record [
                            ("dist", Ap (Ap (Ap (distPolSelf, unroll (V this)), emv), V data)),
                            ("len", Ap (Ap (Ap (lenPolSelf, unroll (V this)), emv), V data))
                        ]
                       )
    in
        self (this,
              Record [
                  ("cart", cart),
                  ("pol", pol)
              ]
             )
    end
fun new (c, data) =
    let
        val method = newSym ()
    in
        Ap (Field (unroll ecv, c), data)
    end
fun call (obj, method) =
    Field (obj, method)
end

open ObjectBased;
let
    val point = Record [("x", Int 1), ("y", Int 1)]
    val obj = new ("cart", point)
    val exp = call (obj, "dist")
    val _ = smallstep exp
in
    ()
end;

open MethodBased;
let
    val point = Record [("x", Int 1), ("y", Int 1)]
    val obj = new ("cart", point)
    val exp = call (obj, "dist")
    val _ = smallstep exp
in
    ()
end;

open ObjectBasedSelf;
let
    val point = Record [("x", Int 1), ("y", Int 1)]
    val obj = new ("cart", point)
    val exp = call (obj, "dist")
    val _ = smallstep exp
    val exp = call (obj, "len")
    (* Loop forever! *)
    val _ = smallstep exp
in
    ()
end;
