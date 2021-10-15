(* # Grammar construction *)

(* ## Allow sets *)
type 'a allow_set

val allowAll : ('label -> 'label -> int) -> 'label allow_set
val allowNone : ('label -> 'label -> int) -> 'label allow_set
val allowOneMore : 'label -> 'label allow_set -> 'label allow_set
val allowOneLess : 'label -> 'label allow_set -> 'label allow_set

(* ## Productions *)
type ('label, 'res, 'self) breakable_production

val atom
  : 'label
  -> ('self -> 'res)
  -> ('label, 'res, 'self) breakable_production
val prefix
  : 'label
  -> ('self -> 'res -> 'res)
  -> 'label allow_set (* right *)
  -> ('label, 'res, 'self) breakable_production
val postfix
  : 'label
  -> ('res -> 'self -> 'res)
  -> 'label allow_set (* left *)
  -> ('label, 'res, 'self) breakable_production
val infix
  : 'label
  -> ('res -> 'self -> 'res -> 'res)
  -> 'label allow_set (* left *)
  -> 'label allow_set (* right *)
  -> ('label, 'res, 'self) breakable_production

(* ## Grammar construction *)

type ('label, 'res, 'self) breakable_grammar

val emptyGrammar
  : ('label, 'res, 'self) breakable_grammar
val addProd
  : ('label, 'res, 'self) breakable_production
  -> ('label, 'res, 'self) breakable_grammar
  -> ('label, 'res, 'self) breakable_grammar
val addPrec
  : 'label (* left *)
  -> 'label (* right *)
  -> bool (* may group left *)
  -> bool (* may group right *)
  -> ('label, 'res, 'self) breakable_grammar
  -> ('label, 'res, 'self) breakable_grammar

(* ## Grammar processing *)

type ('label, 'res, 'self) breakable_gen_grammar

val finalize
  : ('label -> 'label -> int)
  -> ('label, 'res, 'self) breakable_grammar
  -> ('label, 'res, 'self) breakable_gen_grammar

(* ## Grammar queries after processing *)

type lclosed
type lopen
type rclosed
type ropen

type ('res, 'self, 'l, 'r) breakable_input

val getAtom
  : ('label, 'res, 'self) breakable_gen_grammar
  -> 'label
  -> ('res, 'self, lclosed, rclosed) breakable_input
val getPrefix
  : ('label, 'res, 'self) breakable_gen_grammar
  -> 'label
  -> ('res, 'self, lclosed, ropen) breakable_input
val getPostfix
  : ('label, 'res, 'self) breakable_gen_grammar
  -> 'label
  -> ('res, 'self, lopen, rclosed) breakable_input
val getInfix
  : ('label, 'res, 'self) breakable_gen_grammar
  -> 'label
  -> ('res, 'self, lopen, ropen) breakable_input

(* ## Parsing *)

type ('res, 'self, 'r) state
type ('res, 'self) permanent_node
type 'a sequence

val init
  : unit
  -> ('res, 'self, ropen) state

val addAtom
  : ('res, 'self, lclosed, rclosed) breakable_input
  -> 'self
  -> ('res, 'self, ropen) state
  -> ('res, 'self, rclosed) state
val addPrefix
  : ('res, 'self, lclosed, ropen) breakable_input
  -> 'self
  -> ('res, 'self, ropen) state
  -> ('res, 'self, ropen) state
val addPostfix
  : ('res, 'self, lopen, rclosed) breakable_input
  -> 'self
  -> ('res, 'self, rclosed) state
  -> ('res, 'self, rclosed) state option
val addInfix
  : ('res, 'self, lopen, ropen) breakable_input
  -> 'self
  -> ('res, 'self, rclosed) state
  -> ('res, 'self, ropen) state option

val finalizeParse
  : ('res, 'self, rclosed) state
  -> ('res, 'self) permanent_node sequence option (* NonEmpty *)

(* ## Querying the result *)

type ('self, 'tokish) breakable_error
type ('self, 'tokish) ambiguity

val constructResult
  : ('self -> 'tokish)
  -> 'tokish
  -> 'tokish
  -> ('res, 'self, lclosed, rclosed) breakable_input
  -> ('res, 'self) permanent_node sequence (* NonEmpty *)
  -> ('res, ('self, 'tokish) breakable_error) Result.t

val foldError
  : (('self, 'tokish) ambiguity sequence -> 'a)
  -> ('self, 'tokish) breakable_error
  -> 'a

val seqFoldl
  : ('acc -> 'a -> 'acc)
  -> 'acc
  -> 'a sequence
  -> 'acc

val ambiguity
  : ('self -> 'self -> 'tokish sequence sequence -> 'a)
  -> ('self, 'tokish) ambiguity
  -> 'a
