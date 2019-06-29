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
           | Lam of string * t
           | Ap of t * t
           | V of string
           | Plus of t * t
           | Times of t * t
           | In of string * t
           | Isin of string * t * string * t * t
fun layout (Unit, _) = "()"
  | layout (Int n, _) = Int.toString n
  | layout (In (a, e), _) = a ^ "·" ^ (layout (e, true))
  | layout (Isin (a, e, x, e1, e2), _) = "match " ^ (layout (e, false)) ^ " as (" ^ a ^ "·" ^ x ^ " ↪ " ^ (layout (e1, false)) ^ "; ow ↪ " ^ (layout (e2, false)) ^ ")"
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
fun subst (body: t, id, e) =
    let
        (* val _ = pLn ((layout (body, true)) ^ " " ^ id ^ " " ^ (layout (e, true))) *)
    in
        case body of
            Unit => Unit
          | Int n => Int n
          | In (a, body) => In (a, subst (body, id, e))
          | Isin (a, e0, x, e1, e2) =>
            if x = id
            then
                Isin (a, (subst (e0, id, e)), x, e1, (subst (e1, id, e)))
            else
                Isin (a, (subst (e0, id, e)), x, (subst (e1, id, e)), (subst (e2, id, e)))
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

datatype d = Done of t
           | Computation of t
fun step e =
    case e of
        Unit => Done Unit
      | Int n => Done (Int n)
      | In (a, e) => Done (In (a, e))
      | Isin (a, e0, x, e1, e2) =>
        (case step e0 of
             Computation e0 => Computation (Isin (a, e0, x, e1, e2))
           | Done (In (a', e0)) =>
             if a' = a
             then
                 Computation (subst (e1, x, e0))
             else
                 Computation e2
           | Done e0 => raise Fail ("match error: " ^ (layout (e0, false)))
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

let
    val exp1 = In ("MyInt", Int 29)
    val fun1 = Lam ("input", Isin ("MyInt", V "input", "x", Times (V "x", V "x"), Int 0))
    val exp2 = Ap (fun1, exp1)
    val exp3 = In ("HisInt", Int 29)
    val _ = smallstep exp2
    (* val _ = smallstep (Ap (fun1, exp2)) *)
    val _ = smallstep (Ap (fun1, exp3))
in
    ()
end;
