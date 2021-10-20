module type Self = sig
  type atom_self
  type infix_self
  type prefix_self
  type postfix_self
  type label
  type tokish

  val lpar_tok : tokish
  val rpar_tok : tokish

  val atom_to_str : atom_self -> tokish
  val infix_to_str : infix_self -> tokish
  val prefix_to_str : prefix_self -> tokish
  val postfix_to_str : postfix_self -> tokish

  val compareLabel : label -> label -> int
end

module type S = sig
  type atom_self
  type infix_self
  type prefix_self
  type postfix_self
  type label
  type tokish

  (* ## Allow sets *)
  type allow_set

  val allowAll : allow_set
  val allowNone : allow_set
  val allowOneMore : label -> allow_set -> allow_set
  val allowOneLess : label -> allow_set -> allow_set

  (* ## Productions *)
  type production

  val atom : label -> production
  val infix : label -> allow_set -> allow_set -> production
  val prefix : label -> allow_set -> production
  val postfix : label -> allow_set -> production

  (* ## Grammar construction *)
  type grammar
  val emptyGrammar : grammar
  val addProd : production -> grammar -> grammar
  val addPrec : label -> label -> bool -> bool -> grammar -> grammar

  (* ## Grammar processing *)
  type gen_grammar
  val finalize : grammar -> gen_grammar

  (* ## Grammar queries after processing *)
  type lclosed
  type lopen
  type rclosed
  type ropen

  type ('l, 'r) input

  val getAtom : gen_grammar -> label -> (lclosed, rclosed) input
  val getInfix : gen_grammar -> label -> (lopen, ropen) input
  val getPrefix : gen_grammar -> label -> (lclosed, ropen) input
  val getPostfix : gen_grammar -> label -> (lopen, rclosed) input

  (* ## Parsing *)
  type 'r state
  type permanent_node
  type 'a sequence

  val init : unit -> ropen state

  val addAtom
      : (lclosed, rclosed) input -> atom_self -> ropen state -> rclosed state
  val addPrefix
      : (lclosed, ropen) input -> prefix_self -> ropen state -> ropen state
  val addPostfix
      : (lopen, rclosed) input -> postfix_self -> rclosed state -> rclosed state option
  val addInfix
      : (lopen, ropen) input -> infix_self -> rclosed state -> ropen state option

  val finalizeParse : rclosed state -> permanent_node sequence option (* NonEmpty *)

  (* ## Querying the result *)
  type error
  type ambiguity
  type res =
    | Atom of atom_self
    | Infix of res * infix_self * res
    | Prefix of prefix_self * res
    | Postfix of res * postfix_self

  val constructResult
      : (lclosed, rclosed) input
        -> permanent_node sequence (* NonEmpty *)
        -> (res, error) Result.t

  val foldError
      : (ambiguity sequence -> 'a) -> error -> 'a

  val seqFoldl
      : ('acc -> 'a -> 'acc)
        -> 'acc
        -> 'a sequence
        -> 'acc

  val ambiguity
      : ((atom_self, prefix_self) Either.t -> (atom_self, postfix_self) Either.t -> tokish sequence sequence -> 'a)
        -> ambiguity
        -> 'a
end

module Make (Se : Self) : S
       with type label = Se.label
        and type atom_self = Se.atom_self
        and type infix_self = Se.infix_self
        and type prefix_self = Se.prefix_self
        and type postfix_self = Se.postfix_self
        and type tokish = Se.tokish
