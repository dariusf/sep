import Bench.SmtLib.Parser

namespace Bench.SmtLib
namespace Parser

private instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

private def ok? (r : Except String α) : Bool :=
  match r with | .ok _ => true | .error _ => false

private def err? (r : Except String α) : Option String :=
  match r with | .ok _ => none | .error e => some e

#guard Sexp.parse "(a b (c))" == .ok #[.list #[.atom "a", .atom "b", .list #[.atom "c"]]]

#guard Sexp.parse "; comment\n(a) ; trailing" == .ok #[.list #[.atom "a"]]

#guard Sexp.parse "(set-info :source |line1\nline2|)" ==
  .ok #[.list #[.atom "set-info", .atom ":source", .atom "|line1\nline2|"]]

#guard Sexp.parse "(a \"str )\" 12)" ==
  .ok #[.list #[.atom "a", .atom "\"str )\"", .atom "12"]]

#guard !ok? (Sexp.parse "(a")
#guard !ok? (Sexp.parse ")")

private def example1 : String :=
  "(set-logic QF_SHLS)
   (set-info :status unsat)
   (declare-sort RefSll_t 0)
   (declare-datatypes ((Sll_t 0)) (((c_Sll_t (next RefSll_t)))))
   (declare-heap (RefSll_t Sll_t))
   (define-fun-rec ls ((in RefSll_t) (out RefSll_t)) Bool
     (or (and (= in out) (_ emp RefSll_t Sll_t))
         (exists ((u RefSll_t))
           (and (distinct in out)
                (sep (pto in (c_Sll_t u)) (ls u out))))))
   (declare-const x RefSll_t)
   (declare-const y RefSll_t)
   (assert (sep (pto x (c_Sll_t y)) (ls y (as nil RefSll_t))))
   (assert (not (ls x (as nil RefSll_t))))
   (check-sat)"

private def expected1 : Array Command :=
  #[.setLogic "QF_SHLS",
    .setInfo ":status" "unsat",
    .declareSort "RefSll_t" 0,
    .declareDatatypes #[{ name := "Sll_t", constructors := #[{ name := "c_Sll_t", fields := #[{ name := "next", sort := .named "RefSll_t" }] }] }],
    .declareHeap #[(.named "RefSll_t", .named "Sll_t")],
    .defineFunRec #[{ name := "ls", params := #[{ name := "in", sort := .named "RefSll_t" }, { name := "out", sort := .named "RefSll_t" }], result := .bool, body := .or #[
        .and #[.eq #[.var "in", .var "out"], .emp],
        .exists #[{ name := "u", sort := .named "RefSll_t" }]
          (.and #[.distinct #[.var "in", .var "out"],
                  .sep #[.pto (.var "in") "c_Sll_t" #[.var "u"], .app "ls" #[.var "u", .var "out"]]])] }],
    .declareConst "x" (.named "RefSll_t"),
    .declareConst "y" (.named "RefSll_t"),
    .assert (.sep #[.pto (.var "x") "c_Sll_t" #[.var "y"], .app "ls" #[.var "y", .nil "RefSll_t"]]),
    .assert (.not (.app "ls" #[.var "x", .nil "RefSll_t"])),
    .checkSat]

#guard (parseProblem "t.smt2" example1).map (·.commands) == .ok expected1

#guard (parseProblem "t.smt2" example1).toOption.bind (·.status) == some "unsat"

#guard (parseProblem "t.smt2" example1).toOption.bind (·.entailment) ==
  some (.sep #[.pto (.var "x") "c_Sll_t" #[.var "y"], .app "ls" #[.var "y", .nil "RefSll_t"]],
        .app "ls" #[.var "x", .nil "RefSll_t"])

#guard (parseProblem "t.smt2" "(assert (< (+ n (- 1)) (* 2 m)))").map (·.commands) ==
  .ok #[.assert (.lt (.add #[.var "n", .neg (.intLit 1)]) (.mul #[.intLit 2, .var "m"]))]

#guard (parseProblem "t.smt2" "(assert (=> (and true false) (wand a b)))").map (·.commands) ==
  .ok #[.assert (.implies (.and #[.true, .false]) (.wand (.var "a") (.var "b")))]

#guard (parseProblem "t.smt2"
  "(define-funs-rec ((p ((x Int)) Bool) (q ((y Int)) Bool)) ((q x) (p y)))").map (·.commands) ==
  .ok #[.defineFunRec #[
    { name := "p", params := #[{ name := "x", sort := .int }], result := .bool, body := .app "q" #[.var "x"] },
    { name := "q", params := #[{ name := "y", sort := .int }], result := .bool, body := .app "p" #[.var "y"] }]]

#guard (parseProblem "t.smt2" "(assert (let ((a 1)) (ite true a 2)))").map (·.commands) ==
  .ok #[.assert (.letIn #[("a", .intLit 1)] (.ite .true (.var "a") (.intLit 2)))]

#guard err? (parseProblem "t.smt2" "(frobnicate 1)") ==
  some "t.smt2: unknown command 'frobnicate': (frobnicate 1)"

#guard !ok? (parseProblem "t.smt2" "(assert (pto x))")
#guard !ok? (parseProblem "t.smt2" "(assert (as cons Int))")

end Parser
end Bench.SmtLib
