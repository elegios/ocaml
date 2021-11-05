module Boot = struct
module Utils = struct
module IntSet = Set.Make (struct
  let compare = Stdlib.compare

  type t = int
end)

type intset = IntSet.t

(* Returns the last element *)
let rec last xs =
  match xs with
  | [] ->
      raise (Invalid_argument "Utils.last")
  | [x] ->
      x
  | _ :: xs ->
      last xs

let findindex x l =
  let rec findidx l c =
    match l with
    | [] ->
        raise Not_found
    | y :: ys ->
        if x = y then c else findidx ys (c + 1)
  in
  findidx l 0

let find_associndex x l =
  let rec findidx l c =
    match l with
    | [] ->
        raise Not_found
    | (y, v) :: ys ->
        if x = y then (v, c) else findidx ys (c + 1)
  in
  findidx l 0

let ( <| ) f x = f x

let ( >> ) f g x = g (f x)

let map_option f op = match op with Some t -> Some (f t) | None -> None

let rec map2sc f l1 l2 =
  match (l1, l2) with
  | [], _ ->
      []
  | _, [] ->
      []
  | x :: xs, y :: ys ->
      f x y :: map2sc f xs ys

let rec filtermap f ls =
  match ls with
  | x :: xs -> (
    match f x with Some y -> y :: filtermap f xs | None -> filtermap f xs )
  | [] ->
      []

let foldmap f k ls =
  let rec work f k ls a =
    match ls with
    | x :: xs ->
        let k', x' = f k x in
        work f k' xs (x' :: a)
    | [] ->
        (k, List.rev a)
  in
  work f k ls []

let rec option_split lst =
  match lst with
  | Some x :: xs -> (
    match option_split xs with Some xs' -> Some (x :: xs') | None -> None )
  | None :: _ ->
      None
  | [] ->
      Some []

let string_of_intlist il =
  let s = Bytes.create (List.length il) in
  il
  |> List.fold_left
       (fun i x ->
         Bytes.set s i (char_of_int x) ;
         i + 1 )
       0
  |> ignore ;
  Bytes.to_string s

let intlist_of_string s =
  let rec work n a =
    if n >= 0 then work (n - 1) (int_of_char s.[n] :: a) else a
  in
  work (String.length s) []

let write_binfile filename str =
  let f = open_out_bin filename in
  output_bytes f str ; flush f ; close_out f

let read_binfile filename =
  let f = open_in_bin filename in
  let size = in_channel_length f in
  let s = Bytes.create size in
  try
    let rec readinput pos size =
      let read = input f s pos size in
      if read != 0 then readinput (pos + read) (size - read) else ()
    in
    readinput 0 size ; close_in f ; s
  with Invalid_argument _ -> raise (Sys_error "Cannot read file")

let rec fold_interval f a s e =
  if s = e then f a s else fold_interval f (f a s) (s + 1) e

let genlist f n =
  let rec work i a = if i >= 0 then work (i - 1) (f (i - 1) :: a) else a in
  work n []

let xor b1 b2 = (b1 || b2) && not (b1 && b2)

let sign_extension v n =
  if (v lsr (n - 1)) land 1 = 0 then v else (-1 lsl n) lor v

type 'a list_zipper =
  | ZipLeftEnd of 'a list
  | ZipRightEnd of 'a list
  | Zipper of 'a list * 'a * 'a list

let list_to_zipper l = ZipLeftEnd l

let list_zipper_right ls = function
  | [] ->
      ZipRightEnd ls
  | x :: xs ->
      Zipper (ls, x, xs)

let list_zip_right = function
  | ZipLeftEnd [] ->
      ZipRightEnd []
  | ZipLeftEnd (x :: xs) ->
      Zipper ([], x, xs)
  | ZipRightEnd xs ->
      ZipRightEnd xs
  | Zipper (ls, x, r :: rs) ->
      Zipper (x :: ls, r, rs)
  | Zipper (ls, x, []) ->
      ZipRightEnd (x :: ls)

module Int = struct
  type t = int

  let compare = compare
end
end
module Ustring = struct
(*
Copyright (c) 2010, David Broman
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice,
      this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the Linköping University nor the names of its
      contributors may be used to endorse or promote products derived from
      this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

type uchar = int

type tree = Uchars of uchar array | Branch of tree * tree

type encoding =
  | Ascii
  | Latin1
  | Utf8
  | Utf16le
  | Utf16be
  | Utf32le
  | Utf32be
  | Auto

exception Decode_error of (encoding * int)

let space_char = 0x20

(*
  Comments state which test case the differnet functions are tested in.
  ST = successful test, ET=Exception test, i.e., when the funtion raise
  an exception
*)

let valid_uchar c = c >= 0 && c <= 0x1FFFFF

(* Internal function for generate one uchar out of a tree *)
let collapse t =
  let rec make_list us ls =
    match us with
    | Uchars a ->
        a :: ls
    | Branch (t1, t2) ->
        make_list t1 (make_list t2 ls)
  in
  Array.concat (make_list t [])

(* If necessary, collapse a ustring and update the reference *)
let collapse_ustring s =
  match !s with
  | Uchars a ->
      a
  | Branch (_, _) as t ->
      let a = collapse t in
      s := Uchars (collapse t) ;
      a

(* Create a new string where "\x0D\x0A" or "\x0D" are replaced with '\x0A'.
   A with the new string and the size is returned. *)
let normalize_newlines s =
  let len = String.length s in
  let s2 = Bytes.create len in
  let rec worker i n prev_x0d =
    if i < len then
      let c = s.[i] in
      if c = '\x0D' then (
        Bytes.set s2 n '\x0A' ;
        worker (i + 1) (n + 1) true )
      else if c = '\x0A' && prev_x0d then worker (i + 1) n false
      else (
        Bytes.set s2 n c ;
        worker (i + 1) (n + 1) false )
    else n
  in
  let n = worker 0 0 false in
  (Bytes.to_string s2, n)

(* Internal and can be used if we shall convert a UTF-8 stream later on.
   Returns a tuple with the size in bytes of the encoded string (source string)
   and an array with the uchars. *)
let from_utf8_worker s slen fail =
  (* Due to peformance requirements, we do not use the validate function.*)
  let rec calc_size_from_utf8 s i c =
    if i < slen then
      if int_of_char s.[i] land 0b10000000 = 0 then
        calc_size_from_utf8 s (i + 1) (c + 1)
      else if int_of_char s.[i] land 0b11100000 = 0b11000000 then
        calc_size_from_utf8 s (i + 2) (c + 1)
      else if int_of_char s.[i] land 0b11110000 = 0b11100000 then
        calc_size_from_utf8 s (i + 3) (c + 1)
      else if int_of_char s.[i] land 0b11111000 = 0b11110000 then
        calc_size_from_utf8 s (i + 4) (c + 1)
      else fail ()
    else if i > slen then c - 1
    else c
  in
  let alen = calc_size_from_utf8 s 0 0 in
  let a = Array.make alen 0 in
  let rec convert i j =
    if j >= alen then i
    else
      let s1 = int_of_char s.[i] in
      if s1 land 0b10000000 = 0 then (
        a.(j) <- s1 ;
        convert (i + 1) (j + 1) )
      else if s1 land 0b11100000 = 0b11000000 then
        let s2 = int_of_char s.[i + 1] in
        if s2 land 0b11000000 <> 0b10000000 then fail ()
        else
          let c = ((s1 land 0b11111) lsl 6) lor (s2 land 0b111111) in
          if c <= 0b1111111 then fail ()
          else (
            a.(j) <- c ;
            convert (i + 2) (j + 1) )
      else if s1 land 0b11110000 = 0b11100000 then
        let s2 = int_of_char s.[i + 1] in
        let s3 = int_of_char s.[i + 2] in
        if s2 land 0b11000000 <> 0b10000000 || s3 land 0b11000000 <> 0b10000000
        then fail ()
        else
          let c =
            ((s1 land 0b1111) lsl 12)
            lor ((s2 land 0b111111) lsl 6)
            lor (s3 land 0b111111)
          in
          if c <= 0b11111111111 then fail ()
          else (
            a.(j) <- c ;
            convert (i + 3) (j + 1) )
      else if s1 land 0b11111000 = 0b11110000 then
        let s2 = int_of_char s.[i + 1] in
        let s3 = int_of_char s.[i + 2] in
        let s4 = int_of_char s.[i + 3] in
        if
          s2 land 0b11000000 <> 0b10000000
          || s3 land 0b11000000 <> 0b10000000
          || s4 land 0b11000000 <> 0b10000000
        then fail ()
        else
          let c =
            ((s1 land 0b111) lsl 18)
            lor ((s2 land 0b111111) lsl 12)
            lor ((s3 land 0b111111) lsl 6)
            lor (s4 land 0b111111)
          in
          if c <= 0b1111111111111111 then fail ()
          else (
            a.(j) <- c ;
            convert (i + 4) (j + 1) )
      else fail ()
  in
  let i = convert 0 0 in
  (i, a)

let rec to_latin1 s =
  match !s with
  | Uchars a -> (
      let len = Array.length a in
      let sout = Bytes.create len in
      try
        for i = 0 to len - 1 do
          Bytes.set sout i (char_of_int a.(i))
        done ;
        Bytes.to_string sout
      with Invalid_argument _ -> raise (Invalid_argument "Ustring.to_latin1") )
  | Branch (_, _) as t ->
      s := Uchars (collapse t) ;
      to_latin1 s

let from_uchars a =
  Array.iter
    (fun c ->
      if not (valid_uchar c) then raise (Invalid_argument "Ustring.from_uchars")
      else () )
    a ;
  ref (Uchars a)

(*   Note: Function should not throw an exception, since only well defined
         unicode characters are available internally. *)
let rec to_utf8 s =
  let calc_size_to_utf8 a =
    Array.fold_left
      (fun n ae ->
        if ae <= 0b1111111 then n + 1
        else if ae <= 0b11111111111 then n + 2
        else if ae <= 0b1111111111111111 then n + 3
        else n + 4 )
      0 a
  in
  match !s with
  | Uchars a ->
      let ilen = Array.length a in
      let olen = calc_size_to_utf8 a in
      let sout = Bytes.create olen in
      let rec convert i j =
        if i >= ilen then ()
        else
          let ai = a.(i) in
          if ai <= 0b1111111 then (
            Bytes.set sout j (char_of_int ai) ;
            convert (i + 1) (j + 1) )
          else if ai <= 0b11111111111 then (
            Bytes.set sout j (char_of_int ((ai lsr 6) lor 0b11000000)) ;
            Bytes.set sout (j + 1)
              (char_of_int (ai land 0b111111 lor 0b10000000)) ;
            convert (i + 1) (j + 2) )
          else if ai <= 0b1111111111111111 then (
            Bytes.set sout j (char_of_int ((ai lsr 12) lor 0b11100000)) ;
            Bytes.set sout (j + 1)
              (char_of_int ((ai lsr 6) land 0b111111 lor 0b10000000)) ;
            Bytes.set sout (j + 2)
              (char_of_int (ai land 0b111111 lor 0b10000000)) ;
            convert (i + 1) (j + 3) )
          else (
            Bytes.set sout j (char_of_int ((ai lsr 18) lor 0b11110000)) ;
            Bytes.set sout (j + 1)
              (char_of_int ((ai lsr 12) land 0b111111 lor 0b10000000)) ;
            Bytes.set sout (j + 2)
              (char_of_int ((ai lsr 6) land 0b111111 lor 0b10000000)) ;
            Bytes.set sout (j + 3)
              (char_of_int (ai land 0b111111 lor 0b10000000)) ;
            convert (i + 1) (j + 4) )
      in
      convert 0 0 ; Bytes.to_string sout
  | Branch (_, _) as t ->
      s := Uchars (collapse t) ;
      to_utf8 s

(**** Op module  **********************************************************)

module Op = struct
  type ustring = tree ref

  type sid = int

  module SidSet = Set.Make (struct
    let compare = Stdlib.compare

    type t = sid
  end)

  type sidset = SidSet.t

  module SidMap = Map.Make (struct
    let compare = Stdlib.compare

    type t = sid
  end)

  type 'a sidmap = 'a SidMap.t

  let ( ^. ) s1 s2 = ref (Branch (!s1, !s2))

  let ( ^.. ) s1 s2 =
    let s1 = collapse_ustring s1 in
    let s2 = collapse_ustring s2 in
    ref (Uchars (Array.append s1 s2))

  let ( =. ) s1 s2 =
    let s1 = collapse_ustring s1 in
    let s2 = collapse_ustring s2 in
    s1 = s2

  let ( <>. ) s1 s2 = not (s1 =. s2)

  let us s =
    let s2, len2 = normalize_newlines s in
    ref (Uchars (Array.init len2 (fun i -> int_of_char s2.[i])))

  let uc c = int_of_char (if c = '\x0D' then '\x0A' else c)

  let is_ascii_lower_alpha c = uc 'a' <= c && c <= uc 'z'

  let is_ascii_upper_alpha c = uc 'A' <= c && c <= uc 'Z'

  module OrderedUString = struct
    type t = ustring

    let equal x y = x =. y

    let hash t = Hashtbl.hash (collapse_ustring t)
  end

  module USHashtbl = Hashtbl.Make (OrderedUString)

  let symtab1 = USHashtbl.create 1024

  let (symtab2 : (int, ustring) Hashtbl.t) = Hashtbl.create 1024

  let idcount = ref 0

  let sid_of_ustring s =
    try USHashtbl.find symtab1 s
    with Not_found ->
      incr idcount ;
      USHashtbl.add symtab1 s !idcount ;
      Hashtbl.add symtab2 !idcount s ;
      !idcount

  let ustring_of_sid i = Hashtbl.find symtab2 i

  let string_of_sid i = ustring_of_sid i |> to_utf8

  let usid s = sid_of_ustring (us s)

  let ustring_of_bool b = if b then us "true" else us "false"

  let bool_of_ustring s =
    if s =. us "true" then true
    else if s =. us "false" then false
    else raise (Invalid_argument "bool_of_ustring")

  let ustring_of_int i = us (string_of_int i)

  let int_of_ustring s =
    try int_of_string (to_latin1 s) with _ -> raise (Failure "int_of_ustring")

  let ustring_of_float f = us (string_of_float f)

  let float_of_ustring s =
    try float_of_string (to_latin1 s)
    with _ -> raise (Failure "float_of_ustring")

  let uprint_char c = print_string (to_utf8 (from_uchars [|c|]))

  let uprint_string s = print_string (to_utf8 s)

  let uprint_int i = print_int i

  let uprint_float f = print_float f

  let uprint_endline s = print_endline (to_utf8 s)

  let uprint_newline () = print_newline ()

  let list2ustring lst = ref (Uchars (Array.of_list lst))

  let ustring2list s = Array.to_list (collapse !s)

  let array2ustring a = ref (Uchars a)

  let ustring2array s = collapse !s

  let uprint_bool b = print_string (if b then "true" else "false")
end

type ustring = Op.ustring

type t = Op.ustring

let compare s1 s2 =
  let s1 = collapse_ustring s1 in
  let s2 = collapse_ustring s2 in
  compare s1 s2

let equal s1 s2 = Op.( =. ) s1 s2

let not_equal s1 s2 = Op.( <>. ) s1 s2

let hash t = Hashtbl.hash (collapse_ustring t)

let rec length s =
  match !s with
  | Uchars a ->
      Array.length a
  | Branch (_, _) as t ->
      s := Uchars (collapse t) ;
      length s

let rec get s n =
  match !s with
  | Uchars a -> (
    try a.(n)
    with Invalid_argument _ -> raise (Invalid_argument "Ustring.get") )
  | Branch (_, _) as t ->
      s := Uchars (collapse t) ;
      get s n

let rec set s n c =
  match !s with
  | Uchars a -> (
    try a.(n) <- c
    with Invalid_argument _ -> raise (Invalid_argument "Ustring.set") )
  | Branch (_, _) as t ->
      s := Uchars (collapse t) ;
      set s n c

let make n c = ref (Uchars (Array.make n c))

let create n = make n (Op.uc ' ')

let copy s = ref (Uchars (collapse_ustring s))

let sub s start len =
  let s2 = collapse_ustring s in
  try ref (Uchars (Array.sub s2 start len))
  with Invalid_argument _ -> raise (Invalid_argument "Ustring.sub")

let rec rindex_from_internal s i c =
  try
    if s.(i) = c then i
    else if i = 0 then raise Not_found
    else rindex_from_internal s (i - 1) c
  with Invalid_argument _ -> raise (Invalid_argument "Ustring.rindex_from")

let rindex_from s i c =
  let s2 = collapse_ustring s in
  if Array.length s2 = 0 then raise Not_found
  else rindex_from_internal (collapse_ustring s) i c

let rindex s c = rindex_from s (length s - 1) c

let fast_append s1 s2 = Op.( ^. ) s1 s2

let fast_concat sep sl =
  let rec worker sl ack first =
    match sl with
    | [] ->
        ack
    | s :: ss ->
        if first then worker ss s false
        else worker ss (Op.( ^. ) (Op.( ^. ) ack sep) s) false
  in
  worker sl (Op.us "") true

let concat sep sl = copy (fast_concat sep sl)

let count s c =
  let s2 = collapse_ustring s in
  Array.fold_left (fun a b -> if b = c then a + 1 else a) 0 s2

(* Internal *)
let find_trim_left s =
  let len = Array.length s in
  let rec worker i =
    if i >= len then i else if s.(i) > space_char then i else worker (i + 1)
  in
  worker 0

(* Internal *)
let find_trim_right s =
  let rec worker i =
    if i = 0 then i else if s.(i - 1) > space_char then i else worker (i - 1)
  in
  worker (Array.length s)

let trim_left s =
  let s2 = collapse_ustring s in
  let left = find_trim_left s2 in
  let len = Array.length s2 - left in
  ref (Uchars (Array.sub s2 left len))

let trim_right s =
  let s2 = collapse_ustring s in
  let left = 0 in
  let len = find_trim_right s2 in
  ref (Uchars (Array.sub s2 left len))

let trim s =
  let s2 = collapse_ustring s in
  let left = find_trim_left s2 in
  let len = find_trim_right s2 - left in
  if len <= 0 then ref (Uchars [||]) else ref (Uchars (Array.sub s2 left len))

let empty () = ref (Uchars [||])

let split s c =
  let s2 = collapse_ustring s in
  let c2 = collapse_ustring c in
  let len = Array.length s2 in
  let len_c2 = Array.length c2 in
  let rec has_char ch i =
    if i < len_c2 then if c2.(i) = ch then true else has_char ch (i + 1)
    else false
  in
  let rec worker last i acc =
    if i < len then
      if has_char s2.(i) 0 then
        worker (i + 1) (i + 1)
          (ref (Uchars (Array.sub s2 last (i - last))) :: acc)
      else worker last (i + 1) acc
    else ref (Uchars (Array.sub s2 last (i - last))) :: acc
  in
  if len = 0 then [] else List.rev (worker 0 0 [])

let starts_with s2 s1 = try equal (sub s1 0 (length s2)) s2 with _ -> false

let ends_with s2 s1 =
  try equal (sub s1 (length s1 - length s2) (length s2)) s2 with _ -> false

(* TODO implement*)
let unix2dos s = s

let string2hex s =
  let l = String.length s in
  let rec worker i a first =
    let sep = if first then "" else "," in
    if i >= l then a
    else
      let zero = if s.[i] <= '\x0f' then "0" else "" in
      let s2 = Printf.sprintf "%s%s%x" sep zero (int_of_char s.[i]) in
      worker (i + 1) (Op.( ^. ) a (Op.us s2)) false
  in
  worker 0 (Op.us "") true

let append s1 s2 = Op.( ^.. ) s1 s2

let from_latin1 s = Op.us s

let from_latin1_char c = Op.us (String.make 1 c)

let from_utf8 s =
  let fail () = raise (Invalid_argument "Ustring.from_utf8") in
  let s2, len2 = normalize_newlines s in
  let i, a = from_utf8_worker s2 len2 fail in
  if i = len2 then ref (Uchars a) else fail ()

let rec to_uchars s =
  match !s with
  | Uchars a ->
      a
  | Branch (_, _) as t ->
      s := Uchars (collapse t) ;
      to_uchars s

let latin1_to_uchar c = Op.uc c

let validate_utf8_string s n =
  let fail pos = raise (Decode_error (Utf8, pos)) in
  let rec validate i =
    if i >= n then i
    else
      let s1 = int_of_char s.[i] in
      if s1 land 0b10000000 = 0 then validate (i + 1)
      else if s1 land 0b11100000 = 0b11000000 then
        if i + 1 >= n then i
        else
          let s2 = int_of_char s.[i + 1] in
          if s2 land 0b11000000 <> 0b10000000 then fail i
          else
            let c = ((s1 land 0b11111) lsl 6) lor (s2 land 0b111111) in
            if c <= 0b1111111 then fail i else validate (i + 2)
      else if s1 land 0b11110000 = 0b11100000 then
        if i + 2 >= n then i
        else
          let s2 = int_of_char s.[i + 1] in
          let s3 = int_of_char s.[i + 2] in
          if
            s2 land 0b11000000 <> 0b10000000
            || s3 land 0b11000000 <> 0b10000000
          then fail i
          else
            let c =
              ((s1 land 0b1111) lsl 12)
              lor ((s2 land 0b111111) lsl 6)
              lor (s3 land 0b111111)
            in
            if c <= 0b11111111111 then fail i else validate (i + 3)
      else if s1 land 0b11111000 = 0b11110000 then
        if i + 3 >= n then i
        else
          let s2 = int_of_char s.[i + 1] in
          let s3 = int_of_char s.[i + 2] in
          let s4 = int_of_char s.[i + 3] in
          if
            s2 land 0b11000000 <> 0b10000000
            || s3 land 0b11000000 <> 0b10000000
            || s4 land 0b11000000 <> 0b10000000
          then fail i
          else
            let c =
              ((s1 land 0b111) lsl 18)
              lor ((s2 land 0b111111) lsl 12)
              lor ((s3 land 0b111111) lsl 6)
              lor (s4 land 0b111111)
            in
            if c <= 0b1111111111111111 then fail i else validate (i + 4)
      else fail i
  in
  validate 0

(* INTERNAL - check that an ascii string is correct
   Return the number of correct ascii characters *)
let validate_ascii_string s n =
  let rec validate i =
    if i < n && s.[i] < char_of_int 128 then validate (i + 1) else i
  in
  validate 0

(* INTERNAL - used by lexing_from_channel
   This function is applied to Lexing.from_function.
   Exception "Invalid_argument" from function Stdlib.input should
   not happen. *)
let lexing_function ic enc_type inbuf outbuf stream_pos s n =
  let pos = ref 0 in
  let write_from buf =
    let blen = Bytes.length !buf in
    if n - !pos <= blen then (
      Bytes.blit !buf 0 s !pos (n - !pos) ;
      buf := Bytes.sub !buf (n - !pos) (blen - (n - !pos)) ;
      pos := n )
    else (
      Bytes.blit !buf 0 s !pos blen ;
      buf := Bytes.empty ;
      pos := !pos + blen )
  in
  (* Read n characters from input or until end of file
     Make sure it does not a partial read *)
  let input_string ic n =
    let rec worker s pos =
      let rlen = input ic s pos (n - pos) in
      if rlen = 0 then Bytes.sub s 0 pos
      else if rlen + pos = n then s
      else worker s (pos + rlen)
    in
    Bytes.to_string (worker (Bytes.create n) 0)
  in
  let read_to_inbuf i =
    let l1 = Bytes.length !inbuf in
    if l1 >= i then 0
    else
      let s2 = input_string ic (i - l1) in
      let l2 = String.length s2 in
      let s3 = Bytes.create (l1 + l2) in
      Bytes.blit !inbuf 0 s3 0 l1 ;
      Bytes.blit (Bytes.of_string s2) 0 s3 l1 l2 ;
      inbuf := s3 ;
      l2
  in
  let rec convert () =
    match !enc_type with
    | Ascii ->
        let rlen = read_to_inbuf n in
        stream_pos := !stream_pos + rlen ;
        let len_inbuf = Bytes.length !inbuf in
        let n2 = validate_ascii_string (Bytes.to_string !inbuf) len_inbuf in
        write_from inbuf ;
        if n2 = len_inbuf then !pos
        else raise (Decode_error (Ascii, !stream_pos - (len_inbuf - n2)))
    | Latin1 ->
        write_from outbuf ;
        let rlen = read_to_inbuf (n - !pos) in
        outbuf :=
          Bytes.cat !outbuf
            (Bytes.of_string (to_utf8 (from_latin1 (Bytes.to_string !inbuf)))) ;
        inbuf := Bytes.empty ;
        stream_pos := !stream_pos + rlen ;
        write_from outbuf ;
        !pos
    | Utf8 -> (
        let rlen = read_to_inbuf n in
        stream_pos := !stream_pos + rlen ;
        let len_inbuf = Bytes.length !inbuf in
        try
          let n2 = validate_utf8_string (Bytes.to_string !inbuf) len_inbuf in
          outbuf := Bytes.cat !outbuf (Bytes.sub !inbuf 0 n2) ;
          inbuf := Bytes.sub !inbuf n2 (len_inbuf - n2) ;
          write_from outbuf ;
          !pos
        with Decode_error (_, errpos) ->
          raise (Decode_error (Utf8, !stream_pos - (len_inbuf - errpos))) )
    | Utf16le ->
        assert false (* Not yet implemented *)
    | Utf16be ->
        assert false (* Not yet implemented *)
    | Utf32le ->
        assert false
    | Utf32be ->
        assert false
    | Auto -> (
        let rlen = read_to_inbuf n in
        stream_pos := !stream_pos + rlen ;
        let len_inbuf = Bytes.length !inbuf in
        let n2 = validate_ascii_string (Bytes.to_string !inbuf) len_inbuf in
        (* Keep on reading just ascii? *)
        if n2 = len_inbuf then (write_from inbuf ; !pos)
        else
          (* Use Utf8 or Latin1? *)
          let rlen = read_to_inbuf (n + 3) in
          (* Enough for utf8 char *)
          stream_pos := !stream_pos + rlen ;
          try
            let _ =
              validate_utf8_string (Bytes.to_string !inbuf)
                (Bytes.length !inbuf)
            in
            enc_type := Utf8 ;
            convert ()
          with Decode_error (_, _) ->
            enc_type := Latin1 ;
            convert () )
  in
  convert ()

let utf32be = Bytes.of_string "\x00\x00\xFE\xFF"

let utf32le = Bytes.of_string "\xFF\xFE\x00\x00"

let utf16be = Bytes.of_string "\xFE\xFF"

let utf16le = Bytes.of_string "\xFF\xFE"

let utf8 = Bytes.of_string "\xEF\xBB\xBF"

(* INTERNAL - Read in BOM *)
let read_bom ic =
  let s = Bytes.create 4 in
  let l = ref 0 in
  try
    really_input ic s 0 2 ;
    l := 2 ;
    if Bytes.sub s 0 2 = utf16be then (Utf16be, Bytes.empty)
    else (
      really_input ic s 2 1 ;
      l := 3 ;
      if Bytes.sub s 0 3 = utf8 then (Utf8, Bytes.empty)
      else if Bytes.sub s 0 2 = utf16le && Bytes.get s 2 != '\x00' then
        (Utf16le, Bytes.sub s 2 1)
      else (
        really_input ic s 3 1 ;
        l := 4 ;
        if s = utf32be then (Utf32be, Bytes.empty)
        else if s = utf32le then (Utf32le, Bytes.empty)
        else (Auto, s) ) )
  with End_of_file -> (Auto, Bytes.sub s 0 !l)

(* Internal *)
let lexing_function ?(encode_type = Auto) ic =
  match encode_type with
  | Auto ->
      let enc, buf = read_bom ic in
      lexing_function ic (ref enc) (ref buf) (ref Bytes.empty)
        (ref (Bytes.length buf))
  | _ ->
      lexing_function ic (ref encode_type) (ref Bytes.empty) (ref Bytes.empty)
        (ref 0)

let lexing_from_channel ?(encode_type = Auto) ic =
  Lexing.from_function (lexing_function ~encode_type ic)

let lexing_from_ustring s = Lexing.from_string (to_utf8 s)

let read_from_channel ?(encode_type = Auto) ic =
  let reader = lexing_function ~encode_type ic in
  let readsize = 4096 in
  let buf = ref Bytes.empty in
  (* Should not fail, since UTF-8 is already checked*)
  let fail () = assert false in
  fun _ ->
    let s = Bytes.create readsize in
    let read_l = reader s readsize in
    let s2 = Bytes.cat !buf (Bytes.sub s 0 read_l) in
    let len2 = Bytes.length s2 in
    let i, a = from_utf8_worker (Bytes.to_string s2) len2 fail in
    buf := Bytes.sub s2 i (len2 - i) ;
    ref (Uchars a)

let convert_escaped_chars s =
  let rec conv esc s =
    match (esc, s) with
    | false, 0x5C :: ss ->
        conv true ss (*  \ *)
    | false, c :: ss ->
        c :: conv false ss
    | false, [] ->
        []
    | true, 0x27 :: ss ->
        0x27 :: conv false ss (*  "\'" *)
    | true, 0x22 :: ss ->
        0x22 :: conv false ss (*  "\"" *)
    | true, 0x3f :: ss ->
        0x3f :: conv false ss (*  "\?" *)
    | true, 0x5c :: ss ->
        0x5c :: conv false ss (*  "\\" *)
    | true, 0x6E :: ss ->
        0x0A :: conv false ss (*  "\n" *)
    | true, 0x74 :: ss ->
        0x09 :: conv false ss (*  "\t" *)
    | true, 0x72 :: ss ->
        0x0D :: conv false ss (*  "\r" *)
    | true, _ ->
        raise (Invalid_argument "Ustring.convert_escaped_char")
  in
  let a2 = conv false (Array.to_list (collapse_ustring s)) in
  ref (Uchars (Array.of_list a2))

let read_file ?(encode_type = Auto) fn =
  let ic = open_in fn in
  let reader = read_from_channel ~encode_type ic in
  let rec readloop sack =
    let s = reader 4096 in
    if length s = 0 then sack else readloop (Op.( ^. ) sack s)
  in
  let sout = readloop (Op.us "") in
  close_in ic ; sout

let write_file ?(encode_type = Utf8) fn s =
  let data =
    match encode_type with
    | Utf8 ->
        to_utf8 s
    | Latin1 ->
        to_latin1 s
    | _ ->
        failwith "Encoding not supported."
  in
  Utils.write_binfile fn (Bytes.of_string data)
end
module Rope = struct
open Ustring.Op

(* The tree of a rope is either a Leaf or a Concat node.

   A Leaf node consists of an element container. They represent a part of the
   sequence.

   A Slice node represents a part of an array, without explicitly making a copy
   of it.

   A Concat node represents the concatentation of two ropes. It contains the
   two recursive tree structures and a length field corresponding to the
   combined length of the two ropes, so that we can look up the length in
   constant time. *)
type 'a u =
  | Leaf of 'a array
  | Slice of {v: 'a array; off: int; len: int}
  | Concat of {lhs: 'a u; rhs: 'a u; len: int}

(* A rope is represented as a reference to its tree data structure. This lets
   us collapse the tree before performing an operation on it, which in turn
   allows constant time concatenation. *)
type 'a t = 'a u ref

let create_array (n : int) (f : int -> 'a) : 'a t = ref (Leaf (Array.init n f))

let empty_array = Obj.magic (ref (Leaf [||]))

let _length_array (s : 'a u) : int =
  match s with
  | Leaf a ->
      Array.length a
  | Slice {len; _} | Concat {len; _} ->
      len

let length_array (s : 'a t) : int = _length_array !s

let rec _get_array (s : 'a u) (i : int) : 'a =
  match s with
  | Leaf a ->
      a.(i)
  | Slice {v; off; _} ->
      v.(off + i)
  | Concat {lhs; rhs; _} ->
      let n = _length_array lhs in
      if i < n then _get_array lhs i else _get_array rhs (i - n)

let get_array (s : 'a t) (i : int) : 'a = _get_array !s i

let _collapse_array (s : 'a t) : 'a array =
  let rec collapse dst s i =
    match s with
    | Leaf a ->
        let n = Array.length a in
        Array.blit a 0 dst i n ; i + n
    | Slice {v; off; len} ->
        Array.blit v off dst i len ; i + len
    | Concat {lhs; rhs; _} ->
        collapse dst rhs (collapse dst lhs i)
  in
  match !s with
  | Leaf a ->
      a
  | Slice {v; off; len} ->
      let a = Array.sub v off len in
      s := Leaf a ;
      a
  | Concat {len; _} ->
      (* NOTE(larshum, 2021-02-12): the implementation guarantees that Concat
       * nodes are non-empty. *)
      let dst = Array.make len (get_array s 0) in
      let _ = collapse dst !s 0 in
      s := Leaf dst ;
      dst

let concat_array (l : 'a t) (r : 'a t) : 'a t =
  let ln = length_array l in
  let rn = length_array r in
  if ln = 0 then r
  else if rn = 0 then l
  else ref (Concat {lhs= !l; rhs= !r; len= ln + rn})

let set_array (s : 'a t) (idx : int) (v : 'a) : 'a t =
  let rec helper s i =
    match s with
    | Leaf a ->
        let a' = Array.copy a in
        a'.(i) <- v ; Leaf a'
    | Slice {v= value; off; len} ->
        let a' = Array.sub value off len in
        a'.(i) <- v ; Leaf a'
    | Concat {lhs; rhs; len} ->
        let n = _length_array lhs in
        if i < n then Concat {lhs= helper lhs i; rhs; len}
        else Concat {lhs; rhs= helper rhs (i - n); len}
  in
  ref (helper !s idx)

let cons_array (v : 'a) (s : 'a t) : 'a t =
  let n = length_array s in
  if n = 0 then ref (Leaf [|v|])
  else ref (Concat {lhs= Leaf [|v|]; rhs= !s; len= n + 1})

let snoc_array (s : 'a t) (v : 'a) : 'a t =
  let n = length_array s in
  if n = 0 then ref (Leaf [|v|])
  else ref (Concat {lhs= !s; rhs= Leaf [|v|]; len= n + 1})

let split_at_array (s : 'a t) (idx : int) : 'a t * 'a t =
  let n = length_array s in
  if idx = 0 then (empty_array, s)
  else if idx = n then (s, empty_array)
  else
    match !s with
    | Leaf a ->
        ( ref (Slice {v= a; off= 0; len= idx})
        , ref (Slice {v= a; off= idx; len= n - idx}) )
    | Slice {v; off; _} ->
        ( ref (Slice {v; off; len= idx})
        , ref (Slice {v; off= off + idx; len= n - idx}) )
    | Concat _ ->
        let a = _collapse_array s in
        ( ref (Slice {v= a; off= 0; len= idx})
        , ref (Slice {v= a; off= idx; len= n - idx}) )

let sub_array (s : 'a t) (off : int) (cnt : int) : 'a t =
  let n = length_array s in
  if n = 0 then empty_array
  else
    let cnt = min (n - off) cnt in
    match !s with
    | Leaf a ->
        ref (Slice {v= a; off; len= cnt})
    | Slice {v; off= o; _} ->
        ref (Slice {v; off= o + off; len= cnt})
    | Concat _ ->
        let a = _collapse_array s in
        ref (Slice {v= a; off; len= cnt})

let iter_array (f : 'a -> unit) (s : 'a t) : unit =
  let rec iter = function
    | Leaf a ->
        Array.iter f a
    | Slice {v; off; len} ->
        for i = off to off + len - 1 do
          f v.(i)
        done
    | Concat {lhs; rhs; _} ->
        iter lhs ; iter rhs
  in
  iter !s

let iteri_array (f : int -> 'a -> unit) (s : 'a t) : unit =
  let rec iteri off = function
    | Leaf a ->
        Array.iteri (fun i e -> f (i + off) e) a ;
        Array.length a
    | Slice {v; off= o; len} ->
        for i = o to o + len - 1 do
          f (i + off - o) v.(i)
        done ;
        len
    | Concat {lhs; rhs; _} ->
        let n = iteri off lhs in
        iteri (off + n) rhs
  in
  iteri 0 !s |> ignore

let map_array_array (f : 'a -> 'b) (s : 'a t) : 'b t =
  let a = _collapse_array s in
  ref (Leaf (Array.map f a))

let mapi_array_array (f : int -> 'a -> 'b) (s : 'a t) : 'b t =
  let a = _collapse_array s in
  ref (Leaf (Array.mapi f a))

let foldl_array (f : 'a -> 'b -> 'a) (acc : 'a) (s : 'b t) : 'a =
  let a = _collapse_array s in
  Array.fold_left f acc a

let reverse_array (s : 'a t) : 'a t =
  let a = _collapse_array s in
  let a' = Array.copy a in
  let n = Array.length a' in
  for i = 0 to n - 1 do
    a'.(i) <- a.(n - i - 1)
  done ;
  ref (Leaf a')

let combine_array_array (l : 'a t) (r : 'b t) : ('a * 'b) t =
  let ln = length_array l in
  let rn = length_array r in
  if ln != rn then raise (Invalid_argument "Rope.combine")
  else
    let a1, a2 = (_collapse_array l, _collapse_array r) in
    ref (Leaf (Array.map2 (fun x y -> (x, y)) a1 a2))

let equal_array (f : 'a -> 'a -> bool) (l : 'a t) (r : 'a t) : bool =
  let ln = length_array l in
  let rn = length_array r in
  if ln != rn then false
  else
    let a1, a2 = (_collapse_array l, _collapse_array r) in
    let r = ref true in
    Array.iter2 (fun x y -> if f x y then () else r := false) a1 a2 ;
    !r

let foldr_array (f : 'a -> 'b -> 'b) (s : 'a t) (acc : 'b) : 'b =
  let a = _collapse_array s in
  Array.fold_right f a acc

let foldr2_array (f : 'a -> 'b -> 'c -> 'c) (l : 'a t) (r : 'b t) (acc : 'c) :
    'c =
  let ln = length_array l in
  let rn = length_array r in
  if ln != rn then raise (Invalid_argument "Rope.foldr2")
  else
    let a1, a2 = (_collapse_array l, _collapse_array r) in
    let r = ref acc in
    for i = ln - 1 downto 0 do
      r := f a1.(i) a2.(i) !r
    done ;
    !r

module Convert = struct
  let to_array_array (s : 'a t) : 'a array = _collapse_array s

  let of_array_array (a : 'a array) : 'a t = ref (Leaf a)

  let to_list_array (s : 'a t) : 'a list = Array.to_list (to_array_array s)

  let of_list_array (l : 'a list) : 'a t = of_array_array (Array.of_list l)

  let to_ustring_array (s : int t) : ustring = array2ustring (to_array_array s)

  let of_ustring_array (u : ustring) : int t = of_array_array (ustring2array u)
end
end
module Tensor = struct
open Ustring.Op

module type TENSOR = sig
  type ('a, 'b) t

  val get_exn : ('a, 'b) t -> int array -> 'a

  val set_exn : ('a, 'b) t -> int array -> 'a -> unit

  val shape : ('a, 'b) t -> int array

  val rank : ('a, 'b) t -> int

  val size : ('a, 'b) t -> int

  val reshape_exn : ('a, 'b) t -> int array -> ('a, 'b) t

  val slice_exn : ('a, 'b) t -> int array -> ('a, 'b) t

  val sub_exn : ('a, 'b) t -> int -> int -> ('a, 'b) t

  val copy : ('a, 'b) t -> ('a, 'b) t

  val transpose_exn : ('a, 'b) t -> int -> int -> ('a, 'b) t
end

module type GENERIC = sig
  include TENSOR

  val create : int array -> (int array -> 'a) -> ('a, 'b) t
end

module type BARRAY = sig
  open Bigarray

  include TENSOR

  val create_int : int array -> (int array -> int) -> (int, int_elt) t

  val create_float :
    int array -> (int array -> float) -> (float, float64_elt) t

  val to_genarray_clayout : ('a, 'b) t -> ('a, 'b, c_layout) Genarray.t

  val of_genarray_clayout : ('a, 'b, c_layout) Genarray.t -> ('a, 'b) t
end

module type UOP = sig
  type ('a, 'b) t

  val iter_slice : (int -> ('a, 'b) t -> unit) -> ('a, 'b) t -> unit

  val to_data_array : ('a, 'b) t -> 'a array

  val to_ustring : ('a -> ustring) -> ('a, 'b) t -> ustring
end

module type BOP = sig
  type ('a, 'b) t1

  type ('c, 'd) t2

  val equal : ('a -> 'c -> bool) -> ('a, 'b) t1 -> ('c, 'd) t2 -> bool
end

let prod = Array.fold_left ( * ) 1

let cartesian_to_linear_idx shape idx =
  let rank = Array.length shape in
  let n = Array.length idx in
  let tmp_ofs = ref 0 in
  let tmp = ref 0 in
  for k = 0 to n - 1 do
    tmp := 1 ;
    for l = k + 1 to rank - 1 do
      tmp := !tmp * shape.(l)
    done ;
    tmp_ofs := !tmp_ofs + (!tmp * idx.(k))
  done ;
  !tmp_ofs

let transpose create shape get_exn t dim0 dim1 =
  let shape' = shape t in
  let rank = Array.length shape' in
  if dim0 >= 0 && dim0 < rank && dim1 >= 0 && dim1 < rank then (
    let tmp = shape'.(dim0) in
    shape'.(dim0) <- shape'.(dim1) ;
    shape'.(dim1) <- tmp ;
    create shape' (fun idx ->
        let idx' = Array.copy idx in
        let tmp = idx'.(dim0) in
        idx'.(dim0) <- idx'.(dim1) ;
        idx'.(dim1) <- tmp ;
        get_exn t idx' ) )
  else raise (Invalid_argument "Tensor.transpose")

module Generic : GENERIC = struct
  type ('a, _) t =
    {data: 'a array; shape: int array; rank: int; stride: int; size: int}

  let rank t = t.rank

  let shape t = Array.copy t.shape

  let size t = t.size

  let is_valid_index shape idx =
    let valid = ref true in
    Array.iteri (fun i n -> valid := !valid && n >= 0 && n < shape.(i)) idx ;
    !valid

  let get_exn t idx =
    if Array.length idx = rank t && is_valid_index t.shape idx then
      let linear_idx = cartesian_to_linear_idx t.shape idx + t.stride in
      t.data.(linear_idx)
    else raise (Invalid_argument "Tensor.Op_mseq_generic.get_exn")

  let set_exn t idx v =
    if is_valid_index t.shape idx then
      let linear_idx = cartesian_to_linear_idx t.shape idx + t.stride in
      t.data.(linear_idx) <- v
    else raise (Invalid_argument "Tensor.Op_mseq_generic.set_exn")

  let reshape_exn t shape =
    if t.size = prod shape then
      let rank = Array.length shape in
      {t with shape; rank}
    else raise (Invalid_argument "Tensor.Dense.reshape_exn")

  let slice_exn t slice =
    if Array.length slice = 0 then t
    else if is_valid_index t.shape slice then
      let n = Array.length slice in
      let stride = cartesian_to_linear_idx t.shape slice + t.stride in
      let rank = t.rank - n in
      let shape = if rank > 0 then Array.sub t.shape n rank else [||] in
      let size = prod shape in
      {t with stride; rank; shape; size}
    else raise (Invalid_argument "Tensor.Dense.slice_exn")

  let sub_exn t ofs len =
    if t.rank > 0 && ofs >= 0 && ofs + len <= t.shape.(0) then (
      let stride = cartesian_to_linear_idx t.shape [|ofs|] + t.stride in
      let shape = Array.copy t.shape in
      shape.(0) <- len ;
      {t with stride; size= prod shape; shape} )
    else raise (Invalid_argument "Tensor.Dense.sub_exn")

  (* Adoped from OCaml Bigarray implementation *)
  let rec loop t idx0 idx f dim shape =
    if dim = Array.length idx then
      if idx = idx0 then () else set_exn t idx (f idx)
    else
      for j = 0 to pred shape.(dim) do
        idx.(dim) <- j ;
        loop t idx0 idx f (succ dim) shape
      done

  let create shape f =
    let stride = 0 in
    let rank = Array.length shape in
    let size = prod shape in
    if size = 0 then
      let data = [||] in
      {data; rank; shape; stride; size}
    else
      let idx = Array.make rank 0 in
      let x0 = f idx in
      let data = Array.make size x0 in
      let t = {data; rank; shape; stride; size} in
      if rank = 0 then t
      else (
        loop t (Array.copy idx) idx f 0 shape ;
        t )

  let copy t =
    let data = Array.init t.size (fun i -> t.data.(i + t.stride)) in
    let shape = t.shape in
    let rank = t.rank in
    let stride = 0 in
    let size = t.size in
    {data; shape; rank; stride; size}

  let transpose_exn t dim0 dim1 = transpose create shape get_exn t dim0 dim1
end

module Barray : BARRAY = struct
  open Bigarray

  type ('a, 'b) t = ('a, 'b, c_layout) Genarray.t

  let get_exn = Genarray.get

  let set_exn = Genarray.set

  let rank = Genarray.num_dims

  let shape = Genarray.dims

  let size t = prod (shape t)

  let blit_exn = Genarray.blit

  let copy t =
    let t' = Genarray.create (Genarray.kind t) c_layout (shape t) in
    blit_exn t t' ; t'

  let reshape_exn = reshape

  let slice_exn = Genarray.slice_left

  let sub_exn = Genarray.sub_left

  let create (type a b) (kind : (a, b) Bigarray.kind) shape (f : int array -> a)
      : (a, b) t =
    if Array.length shape = 0 then (
      let t = Genarray.create kind c_layout shape in
      Genarray.set t shape (f shape) ;
      t )
    else Genarray.init kind c_layout shape f

  let create_int = create Bigarray.int

  let create_float = create Bigarray.float64

  let transpose_exn t dim0 dim1 =
    transpose (create (Genarray.kind t)) shape get_exn t dim0 dim1

  let to_genarray_clayout t = t

  let of_genarray_clayout t = t
end

module Uop (T : TENSOR) : UOP with type ('a, 'b) t = ('a, 'b) T.t = struct
  type ('a, 'b) t = ('a, 'b) T.t

  let iter_slice f t =
    if T.rank t = 0 then f 0 t
    else
      let n = (T.shape t).(0) in
      for i = 0 to n - 1 do
        f i (T.slice_exn t [|i|])
      done

  let to_data_array t =
    let n = T.size t in
    let t' = T.reshape_exn t [|n|] in
    Array.init n (fun i -> T.get_exn t' [|i|])

  let to_ustring el2str =
    let rec recur indent t =
      let rank = T.rank t in
      if rank = 0 then el2str (T.get_exn t [||])
      else if rank = 1 then (
        let elems = ref (us "") in
        let n = (T.shape t).(0) in
        for i = 0 to n - 1 do
          let e = if i < n - 1 then us ", " else us "" in
          elems := !elems ^. recur (us "") (T.slice_exn t [|i|]) ^. e
        done ;
        us "[" ^. !elems ^. us "]" )
      else
        let n = (T.shape t).(0) in
        let newindent = indent ^. us "\t" in
        let elems = ref (us "") in
        for i = 0 to n - 1 do
          let e = if i < n - 1 then us ",\n" ^. newindent else us "" in
          elems := !elems ^. recur newindent (T.slice_exn t [|i|]) ^. e
        done ;
        us "\n[\n" ^. newindent ^. !elems ^. us "\n" ^. indent ^. us "]\n"
    in
    recur (us "")
end

module Bop (T1 : TENSOR) (T2 : TENSOR) :
  BOP
    with type ('a, 'b) t1 = ('a, 'b) T1.t
     and type ('c, 'd) t2 = ('c, 'd) T2.t = struct
  type ('a, 'b) t1 = ('a, 'b) T1.t

  type ('c, 'd) t2 = ('c, 'd) T2.t

  let equal eq t1 t2 =
    if T1.shape t1 = T2.shape t2 then (
      let n = T1.size t1 in
      let v1 = T1.reshape_exn t1 [|n|] in
      let v2 = T2.reshape_exn t2 [|n|] in
      let tmp = ref true in
      let i = ref 0 in
      while !tmp && !i < n do
        tmp := eq (T1.get_exn v1 [|!i|]) (T2.get_exn v2 [|!i|]) ;
        incr i
      done ;
      !tmp )
    else false
end

module Uop_generic = Uop (Generic)
module Uop_barray = Uop (Barray)
module Bop_generic_generic = Bop (Generic) (Generic)
module Bop_barray_barray = Bop (Barray) (Barray)
module Bop_generic_barray = Bop (Generic) (Barray)
module Bop_barray_generic = Bop (Barray) (Generic)
end
module Intrinsics = struct
open Ustring.Op

module Mseq = struct
  type 'a t = List of 'a List.t | Rope of 'a Rope.t

  let create_rope n f = Rope (Rope.create_array n f)

  let create_list n f = List (List.init n f)

  let empty_rope = Rope Rope.empty_array

  let empty_list = List []

  let create = create_rope

  let empty = empty_rope

  let length = function
    | Rope s ->
        Rope.length_array s
    | List s ->
        List.length s

  let concat s1 s2 =
    match (s1, s2) with
    | Rope s1, Rope s2 ->
        Rope (Rope.concat_array s1 s2)
    | List s1, List s2 ->
        List (s1 @ s2)
    | _ ->
        raise (Invalid_argument "Mseq.concat")

  let get = function Rope s -> Rope.get_array s | List s -> List.nth s

  let set s i v =
    match s with
    | Rope s ->
        Rope (Rope.set_array s i v)
    | List s ->
        let rec set i v s acc =
          match (i, s) with
          | _, [] ->
              failwith "Out of bounds access in sequence"
          | 0, _ :: xs ->
              List.rev acc @ (v :: xs)
          | i, x :: xs ->
              set (i - 1) v xs (x :: acc)
        in
        List (set i v s [])

  let cons v = function
    | Rope s ->
        Rope (Rope.cons_array v s)
    | List s ->
        List (v :: s)

  let snoc s v =
    match s with
    | Rope s ->
        Rope (Rope.snoc_array s v)
    | List s ->
        List (s @ [v])

  let reverse = function
    | Rope s ->
        Rope (Rope.reverse_array s)
    | List s ->
        List (List.rev s)

  let head = function Rope s -> Rope.get_array s 0 | List s -> List.hd s

  let tail = function
    | Rope s ->
        Rope (Rope.sub_array s 1 (Rope.length_array s))
    | List s ->
        List (List.tl s)

  let null = function
    | Rope s ->
        Rope.length_array s == 0
    | List s -> (
      match s with [] -> true | _ -> false )

  let iter f = function
    | Rope s ->
        Rope.iter_array f s
    | List s ->
        List.iter f s

  let iteri f = function
    | Rope s ->
        Rope.iteri_array f s
    | List s ->
        List.iteri f s

  let split_at s i =
    match s with
    | Rope s ->
        let s1, s2 = Rope.split_at_array s i in
        (Rope s1, Rope s2)
    | List s ->
        let rec split_at_rev l r = function
          | 0 ->
              (l, r)
          | i ->
              split_at_rev (List.hd r :: l) (List.tl r) (i - 1)
        in
        let l, r = split_at_rev [] s i in
        (List (List.rev l), List r)

  let subsequence s a n =
    match s with
    | Rope s ->
        Rope (Rope.sub_array s a n)
    | List s ->
        let rec subsequence_rev acc s i j =
          match s with
          | _ :: xs when i < a ->
              subsequence_rev acc xs (i + 1) j
          | x :: xs when j < n ->
              subsequence_rev (x :: acc) xs (i + 1) (j + 1)
          | _ ->
              acc
        in
        List (subsequence_rev [] s 0 0 |> List.rev)

  let map f = function
    | Rope s ->
        Rope (Rope.map_array_array f s)
    | List s ->
        List (List.map f s)

  let mapi f = function
    | Rope s ->
        Rope (Rope.mapi_array_array f s)
    | List s ->
        List (List.mapi f s)

  module Helpers = struct
    let of_list_rope l = Rope (Rope.Convert.of_list_array l)

    let of_list_list l = List l

    let to_list = function
      | Rope s ->
          Rope.Convert.to_list_array s
      | List s ->
          s

    let of_array_rope a = Rope (Rope.Convert.of_array_array a)

    let of_array_list a = List (Array.to_list a)

    let to_array = function
      | Rope s ->
          Rope.Convert.to_array_array s
      | List s ->
          Array.of_list s

    let to_array_copy = function
      | Rope s ->
          Rope.Convert.to_array_array s |> Array.copy
      | List s ->
          Array.of_list s

    let of_ustring_rope u = Rope (Rope.Convert.of_ustring_array u)

    let of_ustring_list u = List (ustring2list u)

    let to_ustring = function
      | Rope s ->
          Rope.Convert.to_ustring_array s
      | List s ->
          list2ustring s

    let to_utf8 s = to_ustring s |> Ustring.to_utf8

    let equal f s1 s2 =
      match (s1, s2) with
      | Rope s1, Rope s2 ->
          Rope.equal_array f s1 s2
      | List s1, List s2 ->
          List.equal f s1 s2
      | _ ->
          raise (Invalid_argument "Mseq.equal")

    let fold_left f a = function
      | Rope s ->
          Rope.foldl_array f a s
      | List s ->
          List.fold_left f a s

    let fold_right f a = function
      | Rope s ->
          Rope.foldr_array f s a
      | List s ->
          List.fold_right f s a

    let combine s1 s2 =
      match (s1, s2) with
      | Rope s1, Rope s2 ->
          Rope (Rope.combine_array_array s1 s2)
      | List s1, List s2 ->
          List (List.combine s1 s2)
      | _ ->
          raise (Invalid_argument "Mseq.combine")

    let fold_right2 f s1 s2 a =
      match (s1, s2) with
      | Rope s1, Rope s2 ->
          Rope.foldr2_array f s1 s2 a
      | List s1, List s2 ->
          List.fold_right2 f s1 s2 a
      | _ ->
          raise (Invalid_argument "Mseq.fold_right2")

    let of_list = of_list_rope

    let of_array = of_array_rope

    let of_array_copy a = Array.copy a |> of_array

    let of_ustring = of_ustring_rope

    let of_utf8 s = Ustring.from_utf8 s |> of_ustring
  end
end

module T = struct
  open Bigarray

  type 'a t =
    | TBootInt of (int, int_elt) Tensor.Barray.t
    | TBootFloat of (float, float64_elt) Tensor.Barray.t
    | TBootGen of ('a, 'a) Tensor.Generic.t

  type ('a, 'b) u =
    | TInt : (int, int_elt) Tensor.Barray.t -> (int, int_elt) u
    | TFloat : (float, float64_elt) Tensor.Barray.t -> (float, float64_elt) u
    | TGen : ('a, 'b) Tensor.Generic.t -> ('a, 'b) u

  module type OP_MSEQ = sig
    type ('a, 'b) t

    val get_exn : ('a, 'b) t -> int Mseq.t -> 'a

    val set_exn : ('a, 'b) t -> int Mseq.t -> 'a -> unit

    val shape : ('a, 'b) t -> int Mseq.t

    val reshape_exn : ('a, 'b) t -> int Mseq.t -> ('a, 'b) t

    val slice_exn : ('a, 'b) t -> int Mseq.t -> ('a, 'b) t
  end

  let to_arr = Mseq.Helpers.to_array

  let of_arr = Mseq.Helpers.of_array

  module Op_mseq (T : Tensor.TENSOR) :
    OP_MSEQ with type ('a, 'b) t = ('a, 'b) T.t = struct
    type ('a, 'b) t = ('a, 'b) T.t

    let get_exn t idx = T.get_exn t (to_arr idx)

    let set_exn t idx = T.set_exn t (to_arr idx)

    let shape t = of_arr (T.shape t)

    let reshape_exn t shape = T.reshape_exn t (to_arr shape)

    let slice_exn t idx = T.slice_exn t (to_arr idx)
  end

  module Op_mseq_generic = Op_mseq (Tensor.Generic)
  module Op_mseq_barray = Op_mseq (Tensor.Barray)

  let create_int shape f =
    Tensor.Barray.create_int (to_arr shape) (fun idx ->
        f (of_arr (Array.copy idx)) )

  let create_float shape f =
    Tensor.Barray.create_float (to_arr shape) (fun idx ->
        f (of_arr (Array.copy idx)) )

  let create_generic shape f =
    Tensor.Generic.create (to_arr shape) (fun idx ->
        f (of_arr (Array.copy idx)) )

  let create_int_packed shape f = TInt (create_int shape f)

  let create_float_packed shape f = TFloat (create_float shape f)

  let create_generic_packed shape f = TGen (create_generic shape f)

  let get_exn (type a b) (t : (a, b) u) idx : a =
    match t with
    | TInt t' ->
        Op_mseq_barray.get_exn t' idx
    | TFloat t' ->
        Op_mseq_barray.get_exn t' idx
    | TGen t' ->
        Op_mseq_generic.get_exn t' idx

  let set_exn (type a b) (t : (a, b) u) idx (v : a) : unit =
    match t with
    | TInt t' ->
        Op_mseq_barray.set_exn t' idx v
    | TFloat t' ->
        Op_mseq_barray.set_exn t' idx v
    | TGen t' ->
        Op_mseq_generic.set_exn t' idx v

  let shape (type a b) (t : (a, b) u) : int Mseq.t =
    match t with
    | TInt t' ->
        Op_mseq_barray.shape t'
    | TFloat t' ->
        Op_mseq_barray.shape t'
    | TGen t' ->
        Op_mseq_generic.shape t'

  let slice_exn (type a b) (t : (a, b) u) idx : (a, b) u =
    match t with
    | TInt t' ->
        TInt (Op_mseq_barray.slice_exn t' idx)
    | TFloat t' ->
        TFloat (Op_mseq_barray.slice_exn t' idx)
    | TGen t' ->
        TGen (Op_mseq_generic.slice_exn t' idx)

  let reshape_exn (type a b) (t : (a, b) u) idx : (a, b) u =
    match t with
    | TInt t' ->
        TInt (Op_mseq_barray.reshape_exn t' idx)
    | TFloat t' ->
        TFloat (Op_mseq_barray.reshape_exn t' idx)
    | TGen t' ->
        TGen (Op_mseq_generic.reshape_exn t' idx)

  let sub_exn (type a b) (t : (a, b) u) start len : (a, b) u =
    match t with
    | TInt t' ->
        TInt (Tensor.Barray.sub_exn t' start len)
    | TFloat t' ->
        TFloat (Tensor.Barray.sub_exn t' start len)
    | TGen t' ->
        TGen (Tensor.Generic.sub_exn t' start len)

  let copy (type a b) (t : (a, b) u) : (a, b) u =
    match t with
    | TInt t' ->
        TInt (Tensor.Barray.copy t')
    | TFloat t' ->
        TFloat (Tensor.Barray.copy t')
    | TGen t' ->
        TGen (Tensor.Generic.copy t')

  let transpose_exn (type a b) (t : (a, b) u) dim0 dim1 : (a, b) u =
    match t with
    | TInt t' ->
        TInt (Tensor.Barray.transpose_exn t' dim0 dim1)
    | TFloat t' ->
        TFloat (Tensor.Barray.transpose_exn t' dim0 dim1)
    | TGen t' ->
        TGen (Tensor.Generic.transpose_exn t' dim0 dim1)

  let iter_slice (type a b) (f : int -> (a, b) u -> unit) (t : (a, b) u) : unit
      =
    match t with
    | TInt t' ->
        Tensor.Uop_barray.iter_slice (fun i t -> f i (TInt t)) t'
    | TFloat t' ->
        Tensor.Uop_barray.iter_slice (fun i t -> f i (TFloat t)) t'
    | TGen t' ->
        Tensor.Uop_generic.iter_slice (fun i t -> f i (TGen t)) t'

  let rank (type a b) (t : (a, b) u) : int =
    match t with
    | TInt t' ->
        Tensor.Barray.rank t'
    | TFloat t' ->
        Tensor.Barray.rank t'
    | TGen t' ->
        Tensor.Generic.rank t'

  let equal (type a b c d) (eq : a -> b -> bool) (t1 : (a, c) u) (t2 : (b, d) u)
      : bool =
    match (t1, t2) with
    | TInt t1', TInt t2' ->
        Tensor.Bop_barray_barray.equal eq t1' t2'
    | TFloat t1', TInt t2' ->
        Tensor.Bop_barray_barray.equal eq t1' t2'
    | TGen t1', TInt t2' ->
        Tensor.Bop_generic_barray.equal eq t1' t2'
    | _, TFloat t2' -> (
      match t1 with
      | TInt t1' ->
          Tensor.Bop_barray_barray.equal eq t1' t2'
      | TFloat t1' ->
          Tensor.Bop_barray_barray.equal eq t1' t2'
      | TGen t1' ->
          Tensor.Bop_generic_barray.equal eq t1' t2' )
    | _, TGen t2' -> (
      match t1 with
      | TInt t1' ->
          Tensor.Bop_barray_generic.equal eq t1' t2'
      | TFloat t1' ->
          Tensor.Bop_barray_generic.equal eq t1' t2'
      | TGen t1' ->
          Tensor.Bop_generic_generic.equal eq t1' t2' )

  let to_string (type a b) (el2str : a -> int Mseq.t) (t : (a, b) u) :
      int Mseq.t =
    let el2str x = Mseq.Helpers.to_ustring (el2str x) in
    ( match t with
    | TInt t' ->
        Tensor.Uop_barray.to_ustring el2str t'
    | TFloat t' ->
        Tensor.Uop_barray.to_ustring el2str t'
    | TGen t' ->
        Tensor.Uop_generic.to_ustring el2str t' )
    |> Mseq.Helpers.of_ustring

  module Helpers = struct
    let to_genarray_clayout (type a b) (t : (a, b) u) :
        (a, b, c_layout) Genarray.t =
      match t with
      | TInt t' ->
          Tensor.Barray.to_genarray_clayout t'
      | TFloat t' ->
          Tensor.Barray.to_genarray_clayout t'
      | TGen _ ->
          raise
            (Invalid_argument "Intrinsics.T.Helpers.to_genarray_clayout_int")

    let to_array1_clayout t = to_genarray_clayout t |> array1_of_genarray

    let to_array2_clayout t = to_genarray_clayout t |> array2_of_genarray

    let of_genarray_clayout (type a b) (a : (a, b, c_layout) Genarray.t) :
        (a, b) u =
      match Genarray.kind a with
      | Bigarray.Int ->
          TInt (Tensor.Barray.of_genarray_clayout a)
      | Bigarray.Float64 ->
          TFloat (Tensor.Barray.of_genarray_clayout a)
      | _ ->
          raise (Invalid_argument "Intrinsics.T.Helpers.of_genarray_clayout")

    let of_array1_clayout t = genarray_of_array1 t |> of_genarray_clayout

    let of_array2_clayout t = genarray_of_array2 t |> of_genarray_clayout
  end
end

module Symb = struct
  type t = int

  let symid = ref 0

  let gensym _ = incr symid ; !symid

  let eqsym l r = l = r

  let hash s = s

  let compare = Stdlib.compare

  module Helpers = struct
    let nosym = -1

    let ustring_of_sym = ustring_of_int

    let string_of_sym s = Ustring.to_utf8 (ustring_of_sym s)
  end
end

module File = struct
  let read f =
    f |> Mseq.Helpers.to_ustring |> Ustring.to_utf8 |> Ustring.read_file
    |> Mseq.Helpers.of_ustring

  let write f d =
    let f = f |> Mseq.Helpers.to_ustring |> Ustring.to_utf8 in
    let d = d |> Mseq.Helpers.to_ustring in
    Ustring.write_file f d

  let exists f =
    f |> Mseq.Helpers.to_ustring |> Ustring.to_utf8 |> Sys.file_exists

  let delete f = f |> Mseq.Helpers.to_ustring |> Ustring.to_utf8 |> Sys.remove
end

module FloatConversion = struct
  let floorfi f = f |> Float.floor |> int_of_float

  let ceilfi f = f |> Float.ceil |> int_of_float

  let roundfi f = f |> Float.round |> int_of_float

  let string2float s = s |> Mseq.Helpers.to_ustring |> float_of_ustring

  let float2string r = r |> ustring_of_float |> Mseq.Helpers.of_ustring
end

module IO = struct
  let print s = s |> Mseq.Helpers.to_ustring |> uprint_string

  let dprint v =
    let v = Obj.repr v in
    let string_of_tag t =
      let res = ref (string_of_int t) in
      if t = Obj.lazy_tag then res := !res ^ " (lazy)" ;
      if t = Obj.closure_tag then res := !res ^ " (closure)" ;
      if t = Obj.object_tag then res := !res ^ " (object)" ;
      if t = Obj.infix_tag then res := !res ^ " (infix)" ;
      if t = Obj.forward_tag then res := !res ^ " (forward)" ;
      if t = Obj.no_scan_tag then res := !res ^ " (no_scan)" ;
      if t = Obj.abstract_tag then res := !res ^ " (abstract)" ;
      if t = Obj.string_tag then res := !res ^ " (string)" ;
      if t = Obj.double_tag then res := !res ^ " (double)" ;
      if t = Obj.double_array_tag then res := !res ^ " (double_array)" ;
      if t = Obj.custom_tag then res := !res ^ " (custom)" ;
      if t = Obj.int_tag then res := !res ^ " (int)" ;
      if t = Obj.out_of_heap_tag then res := !res ^ " (out_of_heap)" ;
      if t = Obj.unaligned_tag then res := !res ^ " (unaligned)" ;
      !res
    in
    let rec work indent v =
      if Obj.is_int v then string_of_int (Obj.obj v) ^ "\n"
      else if Obj.tag v = Obj.double_tag then
        string_of_float (Obj.obj v) ^ "\n"
      else if Obj.tag v = Obj.closure_tag then "<closure>\n"
      else
        let istr = String.make indent ' ' in
        let children =
          List.init (Obj.size v) (fun i ->
              istr ^ ", " ^ work (indent + 2) (Obj.field v i) )
        in
        "{ tag: "
        ^ string_of_tag (Obj.tag v)
        ^ ", size: "
        ^ string_of_int (Obj.size v)
        ^ "\n" ^ String.concat "" children ^ istr ^ "}\n"
    in
    print_string (work 0 v)

  let flush_stdout () = flush stdout

  let read_line _ =
    let line = try read_line () with End_of_file -> "" in
    line |> Ustring.from_utf8 |> Ustring.to_uchars |> Mseq.Helpers.of_array
end

module RNG = struct
  let is_seeded = ref false

  let set_seed seed =
    Random.init seed ;
    is_seeded := true

  let int_u lower upper =
    if !is_seeded then ()
    else (
      Random.self_init () ;
      is_seeded := true ) ;
    lower + Random.int (upper - lower)
end

module MSys = struct
  let exit = exit

  let error m =
    Printf.eprintf "ERROR: %s\n"
      (m |> Mseq.Helpers.to_ustring |> Ustring.to_utf8) ;
    exit 1

  let argv =
    Sys.argv |> Mseq.Helpers.of_array
    |> Mseq.map (fun a ->
           a |> Ustring.from_utf8 |> Ustring.to_uchars |> Mseq.Helpers.of_array )

  let command s = Sys.command (s |> Mseq.Helpers.to_ustring |> Ustring.to_utf8)
end

module ConTag = struct
  let constructor_tag obj =
    if Obj.is_int obj then Obj.obj obj + Obj.custom_tag else Obj.tag obj
end

module Mmap = struct
  let empty cmp =
    let cmp x y = cmp (Obj.obj x) (Obj.obj y) in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.empty, cmp)

  let insert k v mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.add (Obj.repr k) v m, cmp)

  let remove k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.remove (Obj.repr k) m, cmp)

  let find k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.find (Obj.repr k) m

  let find_or_else f k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    match MapModule.find_opt (Obj.repr k) m with Some v -> v | None -> f ()

  let find_apply_or_else f felse k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    match MapModule.find_opt (Obj.repr k) m with
    | Some v ->
        f v
    | None ->
        felse ()

  let bindings mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    let binds = MapModule.bindings m in
    Mseq.Helpers.of_list (List.map (fun (k, v) -> (Obj.obj k, v)) binds)

  let size mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.cardinal m

  let mem k mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.mem (Obj.repr k) m

  let any p mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.exists (fun k v -> p (Obj.obj k) v) m

  let map f mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.map f m, cmp)

  let map_with_key f mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    Obj.repr (MapModule.mapi (fun k v -> f (Obj.obj k) v) m, cmp)

  let fold_with_key f z mCmpPair =
    let m, cmp = Obj.obj mCmpPair in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.fold (fun k v acc -> f acc (Obj.obj k) v) m z

  let eq veq m1 m2 =
    let m1, cmp = Obj.obj m1 in
    let m2, _ = Obj.obj m2 in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.equal veq m1 m2

  let cmp vcmp m1 m2 =
    let m1, cmp = Obj.obj m1 in
    let m2, _ = Obj.obj m2 in
    let module Ord = struct
      type t = Obj.t

      let compare = cmp
    end in
    let module MapModule = Map.Make (Ord) in
    MapModule.compare vcmp m1 m2

  let key_cmp mCmpPair k1 k2 =
    let _, cmp = Obj.obj mCmpPair in
    (cmp : Obj.t -> Obj.t -> int) (Obj.repr k1) (Obj.repr k2)
end
end
end [@ocaml.warning "-27-26-37-32-34-60-11"]
module Breakable_impl = struct
type v_record'2341 =
  | CRec'2340 of {l0: Obj.t;l1: Obj.t;l2: Obj.t;l3: Obj.t;l4: Obj.t;l5: Obj.t;l6: Obj.t;l7: Obj.t;l8: Obj.t;l9: Obj.t;l10: Obj.t;l11: Obj.t;l12: Obj.t;l13: Obj.t;l14: Obj.t;l15: Obj.t;l16: Obj.t;l17: Obj.t;l18: Obj.t;l19: Obj.t;l20: Obj.t;l21: Obj.t;l22: Obj.t;l23: Obj.t;l24: Obj.t;l25: Obj.t;l26: Obj.t;l27: Obj.t};;
type v_record'2342 =
  | CRec'2339 of {l0: Obj.t;l1: Obj.t};;
type v_record'2343 =
  | CRec'2338 of {lproductions: Obj.t;lprecedences: Obj.t;ltopAllowed: Obj.t};;
type v_record'2344 =
  | CRec'2337 of {lfirst: Obj.t;llast: Obj.t;lpartialResolutions: Obj.t};;
type v_record'2345 =
  | CRec'2336 of {lfirst: Obj.t;llast: Obj.t};;
type v_BreakableError'2075 =
  | CAmbiguities'2076 of Obj.t;;
type v_record'2346 =
  | CRec'2334 of {lparents: Obj.t;lnode: Obj.t};;
type v_record'2347 =
  | CRec'2333 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t};;
type v_record'2348 =
  | CRec'2332 of {lparents: Obj.t;laddedNodesLeftChildren: Obj.t;laddedNodesRightChildren: Obj.t;ltentativeData: Obj.t;lmaxDistanceFromRoot: Obj.t};;
type v_record'2349 =
  | CRec'2331 of {lidx: Obj.t;linput: Obj.t;lself: Obj.t};;
type v_record'2350 =
  | CRec'2329 of {l0: Obj.t;l1: Obj.t;l2: Obj.t;l3: Obj.t};;
type v_record'2351 =
  | CRec'2325 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t};;
type v_record'2352 =
  | CRec'2323 of {lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t};;
type v_record'2353 =
  | CRec'2322 of {laddedNodesLeftChildren: Obj.t;laddedNodesRightChildren: Obj.t;lallowedChildren: Obj.t};;
type v_record'2354 =
  | CRec'2319 of {ltopAllowed: Obj.t;latoms: Obj.t;lprefixes: Obj.t;linfixes: Obj.t;lpostfixes: Obj.t};;
type v_record'2355 =
  | CRec'2318 of {lconstruct: Obj.t;lleftAllow: Obj.t;lid: Obj.t;lprecWhenThisIsRight: Obj.t};;
type v_record'2356 =
  | CRec'2317 of {lconstruct: Obj.t;lleftAllow: Obj.t;lrightAllow: Obj.t;lid: Obj.t;lprecWhenThisIsRight: Obj.t};;
type v_record'2357 =
  | CRec'2316 of {lconstruct: Obj.t;lrightAllow: Obj.t;lid: Obj.t};;
type v_record'2358 =
  | CRec'2314 of {lconstruct: Obj.t;lid: Obj.t};;
type v_record'2359 =
  | CRec'2311 of {ltimestep: Obj.t;lnextIdx: Obj.t;lfrontier: Obj.t};;
type v_TentativeNode'1725 =
  | CTentativeLeaf'1726 of {lparents: Obj.t;lnode: Obj.t}
  | CTentativeMid'1727 of {lparents: Obj.t;laddedNodesLeftChildren: Obj.t;laddedNodesRightChildren: Obj.t;ltentativeData: Obj.t;lmaxDistanceFromRoot: Obj.t}
  | CTentativeRoot'1728 of {laddedNodesLeftChildren: Obj.t;laddedNodesRightChildren: Obj.t;lallowedChildren: Obj.t};;
type v_TentativeData'1721 =
  | CInfixT'1722 of {lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t}
  | CPrefixT'1723 of {lidx: Obj.t;linput: Obj.t;lself: Obj.t};;
type v_record'2360 =
  | CRec'2304 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lrightChildAlts: Obj.t};;
type v_record'2361 =
  | CRec'2303 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t;lrightChildAlts: Obj.t};;
type v_PermanentNode'1716 =
  | CAtomP'1717 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t}
  | CInfixP'1718 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t;lrightChildAlts: Obj.t}
  | CPrefixP'1719 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lrightChildAlts: Obj.t}
  | CPostfixP'1720 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t};;
type v_BreakableInput'1710 =
  | CAtomI'1711 of {lconstruct: Obj.t;lid: Obj.t}
  | CInfixI'1712 of {lconstruct: Obj.t;lleftAllow: Obj.t;lrightAllow: Obj.t;lid: Obj.t;lprecWhenThisIsRight: Obj.t}
  | CPrefixI'1713 of {lconstruct: Obj.t;lrightAllow: Obj.t;lid: Obj.t}
  | CPostfixI'1714 of {lconstruct: Obj.t;lleftAllow: Obj.t;lid: Obj.t;lprecWhenThisIsRight: Obj.t};;
type v_record'2362 =
  | CRec'2294 of {lmayGroupLeft: Obj.t;lmayGroupRight: Obj.t};;
type v_record'2363 =
  | CRec'2293 of {llabel: Obj.t;lconstruct: Obj.t;lleftAllow: Obj.t};;
type v_record'2364 =
  | CRec'2292 of {llabel: Obj.t;lconstruct: Obj.t;lrightAllow: Obj.t};;
type v_record'2365 =
  | CRec'2291 of {llabel: Obj.t;lconstruct: Obj.t;lleftAllow: Obj.t;lrightAllow: Obj.t};;
type v_record'2366 =
  | CRec'2290 of {llabel: Obj.t;lconstruct: Obj.t};;
type v_BreakableProduction'1697 =
  | CBreakableAtom'1698 of {llabel: Obj.t;lconstruct: Obj.t}
  | CBreakableInfix'1699 of {llabel: Obj.t;lconstruct: Obj.t;lleftAllow: Obj.t;lrightAllow: Obj.t}
  | CBreakablePrefix'1700 of {llabel: Obj.t;lconstruct: Obj.t;lrightAllow: Obj.t}
  | CBreakablePostfix'1701 of {llabel: Obj.t;lconstruct: Obj.t;lleftAllow: Obj.t};;
type v_AllowSet'1694 =
  | CAllowSet'1695 of Obj.t
  | CDisallowSet'1696 of Obj.t;;
type v_Either'1685 =
  | CLeft'1686 of Obj.t
  | CRight'1687 of Obj.t;;
type v_Option'1619 =
  | CSome'1620 of Obj.t
  | CNone'1621;;
let v_not =
  fun v_a'1617 ->
    if
      Obj.magic
        v_a'1617
    then
      false
    else
      Obj.magic
        true;;
let v_optionMap =
  fun v_f'1622 ->
    fun v_o'1623 ->
      match
        Obj.magic
          (let v__target'2367 =
             v_o'1623
           in
           match
             Obj.magic
               Obj.magic
               v__target'2367
           with
           | CSome'1620 v__n'2368 ->
               (Option.Some (v__n'2368))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_t'1624) ->
          (CSome'1620 (Obj.repr
              (Obj.magic
                 v_f'1622
                 v_t'1624)))
      | Option.None ->
          (Obj.magic
             CNone'1621);;
let v_optionZipWith =
  fun v_f'1626 ->
    fun v_o1'1627 ->
      fun v_o2'1628 ->
        match
          Obj.magic
            (let v__target'2369 =
               CRec'2339 { l0 =
                   (Obj.repr
                     v_o1'1627);
                 l1 =
                   (Obj.repr
                     v_o2'1628) }
             in
             let
               CRec'2339 ({l0 = v_0'2370;l1 = v_1'2371})
             =
               Obj.magic
                 Obj.magic
                 v__target'2369
             in
             match
               Obj.magic
                 Obj.magic
                 v_0'2370
             with
             | CSome'1620 v__n'2372 ->
                 (match
                    Obj.magic
                      Obj.magic
                      v_1'2371
                  with
                  | CSome'1620 v__n'2373 ->
                      (Option.Some (v__n'2372, v__n'2373))
                  | _ ->
                      (Obj.magic
                         Obj.magic
                         (Option.None)))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None)))
        with
        | Option.Some (v_v1'1629, v_v2'1630) ->
            (CSome'1620 (Obj.repr
                (Obj.magic
                   v_f'1626
                   v_v1'1629
                   v_v2'1630)))
        | Option.None ->
            (Obj.magic
               CNone'1621);;
let v_optionGetOrElse =
  fun v_d'1632 ->
    fun v_o'1633 ->
      match
        Obj.magic
          (let v__target'2374 =
             v_o'1633
           in
           match
             Obj.magic
               Obj.magic
               v__target'2374
           with
           | CSome'1620 v__n'2375 ->
               (Option.Some (v__n'2375))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_t'1634) ->
          v_t'1634
      | Option.None ->
          (Obj.magic
             (Obj.magic
                v_d'1632
                ()));;
let v_mapOption =
  fun v_f'1636 ->
    let rec v_work'1637 =
        fun v_as'1638 ->
          match
            Obj.magic
              (let v__target'2376 =
                 v_as'1638
               in
               if
                 Obj.magic
                   ((<) : int -> int -> bool)
                   (Obj.magic
                      Boot.Intrinsics.Mseq.length
                      v__target'2376)
                   1
               then
                 Option.None
               else
                 Obj.magic
                   Obj.magic
                   (let
                      (v__prefix'2377, v__splitTemp'2378)
                    =
                      Obj.magic
                        Boot.Intrinsics.Mseq.split_at
                        v__target'2376
                        1
                    in
                    let
                      (v__middle'2379, v__postfix'2380)
                    =
                      Obj.magic
                        Boot.Intrinsics.Mseq.split_at
                        v__splitTemp'2378
                        (Obj.magic
                           Int.sub
                           (Obj.magic
                              Boot.Intrinsics.Mseq.length
                              v__splitTemp'2378)
                           0)
                    in
                    let v__seqElem'2381 =
                      Obj.magic
                        Boot.Intrinsics.Mseq.get
                        v__prefix'2377
                        0
                    in
                    Option.Some (v__seqElem'2381, v__middle'2379)))
          with
          | Option.Some (v_a'1639, v_as'1640) ->
              (match
                 Obj.magic
                   (let v__target'2382 =
                      Obj.magic
                        v_f'1636
                        v_a'1639
                    in
                    match
                      Obj.magic
                        Obj.magic
                        v__target'2382
                    with
                    | CSome'1620 v__n'2383 ->
                        (Option.Some (v__n'2383))
                    | _ ->
                        (Obj.magic
                           Obj.magic
                           (Option.None)))
               with
               | Option.Some (v_b'1641) ->
                   (Obj.magic
                      Boot.Intrinsics.Mseq.cons
                      v_b'1641
                      (Obj.magic
                         v_work'1637
                         v_as'1640))
               | Option.None ->
                   (Obj.magic
                      (Obj.magic
                         v_work'1637
                         v_as'1640)))
          | Option.None ->
              (Obj.magic
                 (Obj.magic
                    Boot.Intrinsics.Mseq.Helpers.of_array
                    [|  |]))
    in v_work'1637;;
let v_for_ =
  fun v_xs'1643 ->
    fun v_f'1644 ->
      Obj.magic
        Boot.Intrinsics.Mseq.iter
        v_f'1644
        v_xs'1643;;
let v_join =
  fun v_seqs'1646 ->
    Obj.magic
      Boot.Intrinsics.Mseq.Helpers.fold_left
      Boot.Intrinsics.Mseq.concat
      (Obj.magic
         Boot.Intrinsics.Mseq.Helpers.of_array
         [|  |])
      v_seqs'1646;;
let v_seqLiftA2 =
  fun v_f'1648 ->
    fun v_as'1649 ->
      fun v_bs'1650 ->
        Obj.magic
          v_join
          (Obj.magic
             Boot.Intrinsics.Mseq.map
             (fun v_a'1651 ->
                Obj.magic
                  Boot.Intrinsics.Mseq.map
                  (Obj.magic
                     v_f'1648
                     v_a'1651)
                  v_bs'1650)
             v_as'1649);;
let rec v_filter =
    fun v_p'1654 ->
      fun v_seq'1655 ->
        if
          Obj.magic
            (Obj.magic
               Boot.Intrinsics.Mseq.null
               v_seq'1655)
        then
          Obj.magic
            Boot.Intrinsics.Mseq.Helpers.of_array
            [|  |]
        else
          Obj.magic
            (if
               Obj.magic
                 (Obj.magic
                    v_p'1654
                    (Obj.magic
                       Boot.Intrinsics.Mseq.head
                       v_seq'1655))
             then
               Obj.magic
                 Boot.Intrinsics.Mseq.cons
                 (Obj.magic
                    Boot.Intrinsics.Mseq.head
                    v_seq'1655)
                 (Obj.magic
                    v_filter
                    v_p'1654
                    (Obj.magic
                       Boot.Intrinsics.Mseq.tail
                       v_seq'1655))
             else
               Obj.magic
                 (Obj.magic
                    v_filter
                    v_p'1654
                    (Obj.magic
                       Boot.Intrinsics.Mseq.tail
                       v_seq'1655)));;
let v_min =
  fun v_cmp'1656 ->
    fun v_seq'1657 ->
      let rec v_work'1658 =
          fun v_e'1659 ->
            fun v_seq'1660 ->
              if
                Obj.magic
                  (Obj.magic
                     Boot.Intrinsics.Mseq.null
                     v_seq'1660)
              then
                CSome'1620 (Obj.repr
                   v_e'1659)
              else
                Obj.magic
                  (let v_h'1661 =
                     Obj.magic
                       Boot.Intrinsics.Mseq.head
                       v_seq'1660
                   in
                   let v_t'1662 =
                     Obj.magic
                       Boot.Intrinsics.Mseq.tail
                       v_seq'1660
                   in
                   if
                     Obj.magic
                       (Obj.magic
                          ((<) : int -> int -> bool)
                          (Obj.magic
                             v_cmp'1656
                             v_e'1659
                             v_h'1661)
                          0)
                   then
                     Obj.magic
                       v_work'1658
                       v_e'1659
                       v_t'1662
                   else
                     Obj.magic
                       (Obj.magic
                          v_work'1658
                          v_h'1661
                          v_t'1662))
      in if
        Obj.magic
          (Obj.magic
             Boot.Intrinsics.Mseq.null
             v_seq'1657)
      then
        CNone'1621
      else
        Obj.magic
          (Obj.magic
             v_work'1658
             (Obj.magic
                Boot.Intrinsics.Mseq.head
                v_seq'1657)
             (Obj.magic
                Boot.Intrinsics.Mseq.tail
                v_seq'1657));;
let v_minOrElse =
  fun v_d'1664 ->
    fun v_cmp'1665 ->
      fun v_seq'1666 ->
        Obj.magic
          v_optionGetOrElse
          v_d'1664
          (Obj.magic
             v_min
             v_cmp'1665
             v_seq'1666);;
let v_maxOrElse =
  fun v_d'1668 ->
    fun v_cmp'1669 ->
      Obj.magic
        v_minOrElse
        v_d'1668
        (fun v_l'1670 ->
           fun v_r'1671 ->
             Obj.magic
               v_cmp'1669
               v_r'1671
               v_l'1670);;
let v_mapLookup =
  fun v_k'1673 ->
    fun v_m'1674 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find_apply_or_else
        (fun v_v'1675 ->
           CSome'1620 (Obj.repr
              v_v'1675))
        (fun v_'1676 ->
           CNone'1621)
        v_k'1673
        v_m'1674;;
let v_mapFromSeq =
  fun v_cmp'1678 ->
    fun v_bindings'1679 ->
      Obj.magic
        Boot.Intrinsics.Mseq.Helpers.fold_left
        (fun v_acc'1680 ->
           fun v_binding'1681 ->
             Obj.magic
               Boot.Intrinsics.Mmap.insert
               (let
                  CRec'2339 ({l0 = v_X'1682})
                =
                  Obj.magic
                    v_binding'1681
                in
                Obj.magic
                  v_X'1682)
               (let
                  CRec'2339 ({l1 = v_X'1683})
                =
                  Obj.magic
                    v_binding'1681
                in
                Obj.magic
                  v_X'1683)
               v_acc'1680)
        (Obj.magic
           Boot.Intrinsics.Mmap.empty
           v_cmp'1678)
        v_bindings'1679;;
let v_printLn =
  fun v_s'1688 ->
    let v_'1689 =
      Obj.magic
        Boot.Intrinsics.IO.print
        (Obj.magic
           Boot.Intrinsics.Mseq.concat
           v_s'1688
           (Obj.magic
              Boot.Intrinsics.Mseq.Helpers.of_array
              [| (10) |]))
    in
    Obj.magic
      Boot.Intrinsics.IO.flush_stdout
      ();;
let v_dprintLn =
  fun v_x'1691 ->
    let v_'1692 =
      Obj.magic
        Boot.Intrinsics.IO.dprint
        v_x'1691
    in
    Obj.magic
      v_printLn
      (Obj.magic
         Boot.Intrinsics.Mseq.Helpers.of_array
         [|  |]);;
let v__firstTimeStep =
  0;;
let v__isBefore =
  ((<) : int -> int -> bool);;
let v__eqOpId =
  Int.equal;;
let v__cmpOpId =
  Int.sub;;
let v__rootID =
  Obj.magic
    Int.neg
    1;;
let v__firstOpId =
  0;;
let v__nextOpId =
  Obj.magic
    Int.add
    1;;
let v__uniqueID =
  Boot.Intrinsics.Symb.gensym;;
let v__getParents =
  fun v_n'1738 ->
    match
      Obj.magic
        (let v__target'2384 =
           v_n'1738
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2384
             with
             | CTentativeLeaf'1726 v__n'2385 ->
                 (let
                    CRec'2334 ({lparents = v_parents'2386})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2384
                  in
                  Option.Some (v_parents'2386))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2389 ->
               (Option.Some v__x'2389)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     Obj.magic
                       Obj.magic
                       v__target'2384
                   with
                   | CTentativeMid'1727 v__n'2387 ->
                       (let
                          CRec'2332 ({lparents = v_parents'2388})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2384
                        in
                        Option.Some (v_parents'2388))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_ps'1739) ->
             (Option.Some (v_ps'1739))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_ps'1739) ->
        (CSome'1620 (Obj.repr
            v_ps'1739))
    | Option.None ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2390 =
                   v_n'1738
                 in
                 match
                   Obj.magic
                     Obj.magic
                     v__target'2390
                 with
                 | CTentativeRoot'1728 v__n'2391 ->
                     (Option.Some ())
                 | _ ->
                     (Obj.magic
                        Obj.magic
                        (Option.None)))
            with
            | Option.Some () ->
                CNone'1621
            | Option.None ->
                (Obj.magic
                   (failwith
                      "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 276:4-276:9 ERROR: Reached a never term, which should be impossible in a well-typed program."))));;
let v__opIdI =
  fun v_input'1741 ->
    match
      Obj.magic
        (let v__target'2392 =
           v_input'1741
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2392
             with
             | CAtomI'1711 v__n'2393 ->
                 (let
                    CRec'2314 ({lid = v_id'2394})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2392
                  in
                  Option.Some (v_id'2394))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2403 ->
               (Option.Some v__x'2403)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     match
                       match
                         Obj.magic
                           Obj.magic
                           v__target'2392
                       with
                       | CInfixI'1712 v__n'2395 ->
                           (let
                              CRec'2317 ({lid = v_id'2396})
                            =
                              Obj.magic
                                Obj.magic
                                v__target'2392
                            in
                            Option.Some (v_id'2396))
                       | _ ->
                           (Obj.magic
                              Obj.magic
                              (Option.None))
                     with
                     | Option.Some v__x'2402 ->
                         (Option.Some v__x'2402)
                     | Option.None ->
                         (Obj.magic
                            Obj.magic
                            (match
                               match
                                 match
                                   Obj.magic
                                     Obj.magic
                                     v__target'2392
                                 with
                                 | CPrefixI'1713 v__n'2397 ->
                                     (let
                                        CRec'2316 ({lid = v_id'2398})
                                      =
                                        Obj.magic
                                          Obj.magic
                                          v__target'2392
                                      in
                                      Option.Some (v_id'2398))
                                 | _ ->
                                     (Obj.magic
                                        Obj.magic
                                        (Option.None))
                               with
                               | Option.Some v__x'2401 ->
                                   (Option.Some v__x'2401)
                               | Option.None ->
                                   (Obj.magic
                                      Obj.magic
                                      (match
                                         Obj.magic
                                           Obj.magic
                                           v__target'2392
                                       with
                                       | CPostfixI'1714 v__n'2399 ->
                                           (let
                                              CRec'2318 ({lid = v_id'2400})
                                            =
                                              Obj.magic
                                                Obj.magic
                                                v__target'2392
                                            in
                                            Option.Some (v_id'2400))
                                       | _ ->
                                           (Obj.magic
                                              Obj.magic
                                              (Option.None))))
                             with
                             | Option.Some (v_id'1742) ->
                                 (Option.Some (v_id'1742))
                             | Option.None ->
                                 (Obj.magic
                                    Obj.magic
                                    (Option.None))))
                   with
                   | Option.Some (v_id'1742) ->
                       (Option.Some (v_id'1742))
                   | Option.None ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_id'1742) ->
             (Option.Some (v_id'1742))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_id'1742) ->
        v_id'1742
    | Option.None ->
        (Obj.magic
           (failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 287:9-287:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__opIdP =
  fun v_node'1744 ->
    let v_defaultCase'2404 =
      fun nv_ ->
        failwith
          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 296:4-296:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
    in
    match
      Obj.magic
        v_node'1744
    with
    | CAtomP'1717 v_x'2405 ->
        (match
           Obj.magic
             (let v__target'2406 =
                Obj.magic
                  Obj.magic
                  v_node'1744
              in
              let
                CRec'2333 ({linput = v_input'2407})
              =
                Obj.magic
                  Obj.magic
                  v__target'2406
              in
              Option.Some (v_input'2407))
         with
         | Option.Some (v_input'1745) ->
             (Obj.magic
                v__opIdI
                v_input'1745)
         | Option.None ->
             (Obj.magic
                (Obj.magic
                   v_defaultCase'2404
                   ())))
    | CInfixP'1718 v_x'2408 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2409 =
                   Obj.magic
                     Obj.magic
                     v_node'1744
                 in
                 let
                   CRec'2303 ({linput = v_input'2410})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2409
                 in
                 Option.Some (v_input'2410))
            with
            | Option.Some (v_input'1746) ->
                (Obj.magic
                   v__opIdI
                   v_input'1746)
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2404
                      ()))))
    | CPrefixP'1719 v_x'2411 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2412 =
                   Obj.magic
                     Obj.magic
                     v_node'1744
                 in
                 let
                   CRec'2304 ({linput = v_input'2413})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2412
                 in
                 Option.Some (v_input'2413))
            with
            | Option.Some (v_input'1747) ->
                (Obj.magic
                   v__opIdI
                   v_input'1747)
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2404
                      ()))))
    | CPostfixP'1720 v_x'2414 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2415 =
                   Obj.magic
                     Obj.magic
                     v_node'1744
                 in
                 let
                   CRec'2325 ({linput = v_input'2416})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2415
                 in
                 Option.Some (v_input'2416))
            with
            | Option.Some (v_input'1748) ->
                (Obj.magic
                   v__opIdI
                   v_input'1748)
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2404
                      ()))))
    | _ ->
        (Obj.magic
           (v_defaultCase'2404
              ()));;
let v__opIdxP =
  fun v_node'1750 ->
    let v_defaultCase'2417 =
      fun nv_ ->
        failwith
          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 305:4-305:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
    in
    match
      Obj.magic
        v_node'1750
    with
    | CAtomP'1717 v_x'2418 ->
        (match
           Obj.magic
             (let v__target'2419 =
                Obj.magic
                  Obj.magic
                  v_node'1750
              in
              let
                CRec'2333 ({lidx = v_idx'2420})
              =
                Obj.magic
                  Obj.magic
                  v__target'2419
              in
              Option.Some (v_idx'2420))
         with
         | Option.Some (v_idx'1751) ->
             v_idx'1751
         | Option.None ->
             (Obj.magic
                (Obj.magic
                   v_defaultCase'2417
                   ())))
    | CInfixP'1718 v_x'2421 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2422 =
                   Obj.magic
                     Obj.magic
                     v_node'1750
                 in
                 let
                   CRec'2303 ({lidx = v_idx'2423})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2422
                 in
                 Option.Some (v_idx'2423))
            with
            | Option.Some (v_idx'1752) ->
                v_idx'1752
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2417
                      ()))))
    | CPrefixP'1719 v_x'2424 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2425 =
                   Obj.magic
                     Obj.magic
                     v_node'1750
                 in
                 let
                   CRec'2304 ({lidx = v_idx'2426})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2425
                 in
                 Option.Some (v_idx'2426))
            with
            | Option.Some (v_idx'1753) ->
                v_idx'1753
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2417
                      ()))))
    | CPostfixP'1720 v_x'2427 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2428 =
                   Obj.magic
                     Obj.magic
                     v_node'1750
                 in
                 let
                   CRec'2325 ({lidx = v_idx'2429})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2428
                 in
                 Option.Some (v_idx'2429))
            with
            | Option.Some (v_idx'1754) ->
                v_idx'1754
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2417
                      ()))))
    | _ ->
        (Obj.magic
           (v_defaultCase'2417
              ()));;
let v__opIdTD =
  fun v_data'1756 ->
    match
      Obj.magic
        (let v__target'2430 =
           v_data'1756
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2430
             with
             | CInfixT'1722 v__n'2431 ->
                 (let
                    CRec'2323 ({linput = v_input'2432})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2430
                  in
                  Option.Some (v_input'2432))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2435 ->
               (Option.Some v__x'2435)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     Obj.magic
                       Obj.magic
                       v__target'2430
                   with
                   | CPrefixT'1723 v__n'2433 ->
                       (let
                          CRec'2331 ({linput = v_input'2434})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2430
                        in
                        Option.Some (v_input'2434))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_input'1757) ->
             (Option.Some (v_input'1757))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_input'1757) ->
        (Obj.magic
           v__opIdI
           v_input'1757)
    | Option.None ->
        (Obj.magic
           (failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 311:4-311:9 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__opIdT =
  fun v_node'1759 ->
    let v_defaultCase'2436 =
      fun nv_ ->
        failwith
          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 319:4-319:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
    in
    match
      Obj.magic
        v_node'1759
    with
    | CTentativeLeaf'1726 v_x'2437 ->
        (match
           Obj.magic
             (let v__target'2438 =
                Obj.magic
                  Obj.magic
                  v_node'1759
              in
              let
                CRec'2334 ({lnode = v_node'2439})
              =
                Obj.magic
                  Obj.magic
                  v__target'2438
              in
              Option.Some (v_node'2439))
         with
         | Option.Some (v_node'1760) ->
             (Obj.magic
                v__opIdP
                v_node'1760)
         | Option.None ->
             (Obj.magic
                (Obj.magic
                   v_defaultCase'2436
                   ())))
    | CTentativeMid'1727 v_x'2440 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2441 =
                   Obj.magic
                     Obj.magic
                     v_node'1759
                 in
                 let
                   CRec'2332 ({ltentativeData = v_tentativeData'2442})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2441
                 in
                 Option.Some (v_tentativeData'2442))
            with
            | Option.Some (v_data'1761) ->
                (Obj.magic
                   v__opIdTD
                   v_data'1761)
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2436
                      ()))))
    | CTentativeRoot'1728 v_x'2443 ->
        (Obj.magic
           v__rootID)
    | _ ->
        (Obj.magic
           (v_defaultCase'2436
              ()));;
let v__addedNodesLeftChildren =
  fun v_node'1763 ->
    match
      Obj.magic
        (let v__target'2444 =
           v_node'1763
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2444
             with
             | CTentativeRoot'1728 v__n'2445 ->
                 (let
                    CRec'2322 ({laddedNodesLeftChildren = v_addedNodesLeftChildren'2446})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2444
                  in
                  Option.Some (v_addedNodesLeftChildren'2446))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2449 ->
               (Option.Some v__x'2449)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     Obj.magic
                       Obj.magic
                       v__target'2444
                   with
                   | CTentativeMid'1727 v__n'2447 ->
                       (let
                          CRec'2332 ({laddedNodesLeftChildren = v_addedNodesLeftChildren'2448})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2444
                        in
                        Option.Some (v_addedNodesLeftChildren'2448))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_x'1764) ->
             (Option.Some (v_x'1764))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_x'1764) ->
        v_x'1764
    | Option.None ->
        (Obj.magic
           (failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 326:9-326:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__addedNodesRightChildren =
  fun v_node'1766 ->
    match
      Obj.magic
        (let v__target'2450 =
           v_node'1766
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2450
             with
             | CTentativeRoot'1728 v__n'2451 ->
                 (let
                    CRec'2322 ({laddedNodesRightChildren = v_addedNodesRightChildren'2452})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2450
                  in
                  Option.Some (v_addedNodesRightChildren'2452))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2455 ->
               (Option.Some v__x'2455)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     Obj.magic
                       Obj.magic
                       v__target'2450
                   with
                   | CTentativeMid'1727 v__n'2453 ->
                       (let
                          CRec'2332 ({laddedNodesRightChildren = v_addedNodesRightChildren'2454})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2450
                        in
                        Option.Some (v_addedNodesRightChildren'2454))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_x'1767) ->
             (Option.Some (v_x'1767))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_x'1767) ->
        v_x'1767
    | Option.None ->
        (Obj.magic
           (failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 333:9-333:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v_breakableInAllowSet =
  fun v_id'1769 ->
    fun v_set'1770 ->
      let v_defaultCase'2456 =
        fun nv_ ->
          failwith
            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 342:4-342:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
      in
      match
        Obj.magic
          v_set'1770
      with
      | CAllowSet'1695 v_x'2457 ->
          (let v_s'1771 =
             Obj.magic
               Obj.magic
               v_x'2457
           in
           Obj.magic
             Boot.Intrinsics.Mmap.mem
             v_id'1769
             v_s'1771)
      | CDisallowSet'1696 v_x'2458 ->
          (Obj.magic
             (let v_s'1772 =
                Obj.magic
                  Obj.magic
                  v_x'2458
              in
              Obj.magic
                v_not
                (Obj.magic
                   Boot.Intrinsics.Mmap.mem
                   v_id'1769
                   v_s'1772)))
      | _ ->
          (Obj.magic
             (v_defaultCase'2456
                ()));;
let v_breakableInsertAllowSet =
  fun v_id'1774 ->
    fun v_set'1775 ->
      let v_defaultCase'2459 =
        fun nv_ ->
          failwith
            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 351:4-351:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
      in
      match
        Obj.magic
          v_set'1775
      with
      | CAllowSet'1695 v_x'2460 ->
          (let v_s'1776 =
             Obj.magic
               Obj.magic
               v_x'2460
           in
           CAllowSet'1695 (Obj.repr
              (Obj.magic
                 Boot.Intrinsics.Mmap.insert
                 v_id'1774
                 ()
                 v_s'1776)))
      | CDisallowSet'1696 v_x'2461 ->
          (Obj.magic
             (let v_s'1777 =
                Obj.magic
                  Obj.magic
                  v_x'2461
              in
              CDisallowSet'1696 (Obj.repr
                 (Obj.magic
                    Boot.Intrinsics.Mmap.remove
                    v_id'1774
                    v_s'1777))))
      | _ ->
          (Obj.magic
             (v_defaultCase'2459
                ()));;
let v_breakableRemoveAllowSet =
  fun v_id'1779 ->
    fun v_set'1780 ->
      let v_defaultCase'2462 =
        fun nv_ ->
          failwith
            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 360:4-360:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
      in
      match
        Obj.magic
          v_set'1780
      with
      | CAllowSet'1695 v_x'2463 ->
          (let v_s'1781 =
             Obj.magic
               Obj.magic
               v_x'2463
           in
           CAllowSet'1695 (Obj.repr
              (Obj.magic
                 Boot.Intrinsics.Mmap.remove
                 v_id'1779
                 v_s'1781)))
      | CDisallowSet'1696 v_x'2464 ->
          (Obj.magic
             (let v_s'1782 =
                Obj.magic
                  Obj.magic
                  v_x'2464
              in
              CDisallowSet'1696 (Obj.repr
                 (Obj.magic
                    Boot.Intrinsics.Mmap.insert
                    v_id'1779
                    ()
                    v_s'1782))))
      | _ ->
          (Obj.magic
             (v_defaultCase'2462
                ()));;
let v_breakableMapAllowSet =
  fun v_f'1784 ->
    fun v_newCmp'1785 ->
      fun v_s'1786 ->
        let v_convert'1790 =
          fun v_s'1787 ->
            Obj.magic
              v_mapFromSeq
              v_newCmp'1785
              (Obj.magic
                 Boot.Intrinsics.Mseq.map
                 (fun v_x'1788 ->
                    CRec'2339 { l0 =
                        (Obj.repr
                          (Obj.magic
                             v_f'1784
                             (let
                                CRec'2339 ({l0 = v_X'1789})
                              =
                                Obj.magic
                                  v_x'1788
                              in
                              Obj.magic
                                v_X'1789)));
                      l1 =
                        (Obj.repr
                          ()) })
                 (Obj.magic
                    Boot.Intrinsics.Mmap.bindings
                    v_s'1787))
        in
        let v_defaultCase'2465 =
          fun nv_ ->
            failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 371:4-371:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
        in
        match
          Obj.magic
            v_s'1786
        with
        | CAllowSet'1695 v_x'2466 ->
            (let v_s'1791 =
               Obj.magic
                 Obj.magic
                 v_x'2466
             in
             CAllowSet'1695 (Obj.repr
                (Obj.magic
                   v_convert'1790
                   v_s'1791)))
        | CDisallowSet'1696 v_x'2467 ->
            (Obj.magic
               (let v_s'1792 =
                  Obj.magic
                    Obj.magic
                    v_x'2467
                in
                CDisallowSet'1696 (Obj.repr
                   (Obj.magic
                      v_convert'1790
                      v_s'1792))))
        | _ ->
            (Obj.magic
               (v_defaultCase'2465
                  ()));;
let v_breakableGenGrammar =
  fun v_cmp'1794 ->
    fun v_grammar'1795 ->
      let v_nOpId'1796 =
        Obj.magic
          ref
          v__firstOpId
      in
      let v_newOpId'1800 =
        fun v_'1797 ->
          let v_res'1798 =
            Obj.magic
              (!)
              v_nOpId'1796
          in
          let v_'1799 =
            Obj.magic
              (:=)
              v_nOpId'1796
              (Obj.magic
                 v__nextOpId
                 v_res'1798)
          in
          v_res'1798
      in
      let v_label'1806 =
        fun v_prod'1801 ->
          let v_defaultCase'2468 =
            fun nv_ ->
              failwith
                "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 392:8-392:13 ERROR: Reached a never term, which should be impossible in a well-typed program."
          in
          match
            Obj.magic
              v_prod'1801
          with
          | CBreakableAtom'1698 v_x'2469 ->
              (match
                 Obj.magic
                   (let v__target'2470 =
                      Obj.magic
                        Obj.magic
                        v_prod'1801
                    in
                    let
                      CRec'2290 ({llabel = v_label'2471})
                    =
                      Obj.magic
                        Obj.magic
                        v__target'2470
                    in
                    Option.Some (v_label'2471))
               with
               | Option.Some (v_label'1802) ->
                   v_label'1802
               | Option.None ->
                   (Obj.magic
                      (Obj.magic
                         v_defaultCase'2468
                         ())))
          | CBreakableInfix'1699 v_x'2472 ->
              (Obj.magic
                 (match
                    Obj.magic
                      (let v__target'2473 =
                         Obj.magic
                           Obj.magic
                           v_prod'1801
                       in
                       let
                         CRec'2291 ({llabel = v_label'2474})
                       =
                         Obj.magic
                           Obj.magic
                           v__target'2473
                       in
                       Option.Some (v_label'2474))
                  with
                  | Option.Some (v_label'1804) ->
                      v_label'1804
                  | Option.None ->
                      (Obj.magic
                         (Obj.magic
                            v_defaultCase'2468
                            ()))))
          | CBreakablePrefix'1700 v_x'2475 ->
              (Obj.magic
                 (match
                    Obj.magic
                      (let v__target'2476 =
                         Obj.magic
                           Obj.magic
                           v_prod'1801
                       in
                       let
                         CRec'2292 ({llabel = v_label'2477})
                       =
                         Obj.magic
                           Obj.magic
                           v__target'2476
                       in
                       Option.Some (v_label'2477))
                  with
                  | Option.Some (v_label'1803) ->
                      v_label'1803
                  | Option.None ->
                      (Obj.magic
                         (Obj.magic
                            v_defaultCase'2468
                            ()))))
          | CBreakablePostfix'1701 v_x'2478 ->
              (Obj.magic
                 (match
                    Obj.magic
                      (let v__target'2479 =
                         Obj.magic
                           Obj.magic
                           v_prod'1801
                       in
                       let
                         CRec'2293 ({llabel = v_label'2480})
                       =
                         Obj.magic
                           Obj.magic
                           v__target'2479
                       in
                       Option.Some (v_label'2480))
                  with
                  | Option.Some (v_label'1805) ->
                      v_label'1805
                  | Option.None ->
                      (Obj.magic
                         (Obj.magic
                            v_defaultCase'2468
                            ()))))
          | _ ->
              (Obj.magic
                 (v_defaultCase'2468
                    ()))
      in
      let v_prodLabelToOpId'1809 =
        Obj.magic
          v_mapFromSeq
          v_cmp'1794
          (Obj.magic
             Boot.Intrinsics.Mseq.map
             (fun v_prod'1807 ->
                CRec'2339 { l0 =
                    (Obj.repr
                      (Obj.magic
                         v_label'1806
                         v_prod'1807));
                  l1 =
                    (Obj.repr
                      (Obj.magic
                         v_newOpId'1800
                         ())) })
             (let
                CRec'2338 ({lproductions = v_X'1808})
              =
                Obj.magic
                  v_grammar'1795
              in
              Obj.magic
                v_X'1808))
      in
      let v_toOpId'1811 =
        fun v_label'1810 ->
          Obj.magic
            Boot.Intrinsics.Mmap.find
            v_label'1810
            v_prodLabelToOpId'1809
      in
      let v_groupingByRightOp'1822 =
        Obj.magic
          Boot.Intrinsics.Mseq.Helpers.fold_left
          (fun v_acc'1812 ->
             fun v_grouping'1813 ->
               match
                 Obj.magic
                   (let v__target'2481 =
                      v_grouping'1813
                    in
                    let
                      CRec'2339 ({l0 = v_0'2482;l1 = v_1'2483})
                    =
                      Obj.magic
                        Obj.magic
                        v__target'2481
                    in
                    let
                      CRec'2339 ({l0 = v_0'2484;l1 = v_1'2485})
                    =
                      Obj.magic
                        Obj.magic
                        v_0'2482
                    in
                    Option.Some (v_0'2484, v_1'2485, v_1'2483))
               with
               | Option.Some (v_lplab'1814, v_rplab'1815, v_grouping'1816) ->
                   (let v_lid'1817 =
                      Obj.magic
                        v_toOpId'1811
                        v_lplab'1814
                    in
                    let v_rid'1818 =
                      Obj.magic
                        v_toOpId'1811
                        v_rplab'1815
                    in
                    let v_prev'1820 =
                      match
                        Obj.magic
                          (let v__target'2486 =
                             Obj.magic
                               v_mapLookup
                               v_rid'1818
                               v_acc'1812
                           in
                           match
                             Obj.magic
                               Obj.magic
                               v__target'2486
                           with
                           | CSome'1620 v__n'2487 ->
                               (Option.Some (v__n'2487))
                           | _ ->
                               (Obj.magic
                                  Obj.magic
                                  (Option.None)))
                      with
                      | Option.Some (v_prev'1819) ->
                          v_prev'1819
                      | Option.None ->
                          (Obj.magic
                             (Obj.magic
                                Boot.Intrinsics.Mmap.empty
                                v__cmpOpId))
                    in
                    Obj.magic
                      Boot.Intrinsics.Mmap.insert
                      v_rid'1818
                      (Obj.magic
                         Boot.Intrinsics.Mmap.insert
                         v_lid'1817
                         v_grouping'1816
                         v_prev'1820)
                      v_acc'1812)
               | Option.None ->
                   (Obj.magic
                      (failwith
                         "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 414:15-414:20 ERROR: Reached a never term, which should be impossible in a well-typed program.")))
          (Obj.magic
             Boot.Intrinsics.Mmap.empty
             v__cmpOpId)
          (let
             CRec'2338 ({lprecedences = v_X'1821})
           =
             Obj.magic
               v_grammar'1795
           in
           Obj.magic
             v_X'1821)
      in
      let v_getGroupingByRight'1825 =
        fun v_opid'1823 ->
          match
            Obj.magic
              (let v__target'2488 =
                 Obj.magic
                   v_mapLookup
                   v_opid'1823
                   v_groupingByRightOp'1822
               in
               match
                 Obj.magic
                   Obj.magic
                   v__target'2488
               with
               | CSome'1620 v__n'2489 ->
                   (Option.Some (v__n'2489))
               | _ ->
                   (Obj.magic
                      Obj.magic
                      (Option.None)))
          with
          | Option.Some (v_res'1824) ->
              v_res'1824
          | Option.None ->
              (Obj.magic
                 (Obj.magic
                    Boot.Intrinsics.Mmap.empty
                    v__cmpOpId))
      in
      let v_atoms'1826 =
        Obj.magic
          ref
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |])
      in
      let v_prefixes'1827 =
        Obj.magic
          ref
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |])
      in
      let v_infixes'1828 =
        Obj.magic
          ref
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |])
      in
      let v_postfixes'1829 =
        Obj.magic
          ref
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |])
      in
      let v_updateRef'1832 =
        fun v_ref'1830 ->
          fun v_f'1831 ->
            Obj.magic
              (:=)
              v_ref'1830
              (Obj.magic
                 v_f'1831
                 (Obj.magic
                    (!)
                    v_ref'1830))
      in
      let v_'1851 =
        Obj.magic
          v_for_
          (let
             CRec'2338 ({lproductions = v_X'1833})
           =
             Obj.magic
               v_grammar'1795
           in
           Obj.magic
             v_X'1833)
          (fun v_prod'1834 ->
             let v_label'1835 =
               Obj.magic
                 v_label'1806
                 v_prod'1834
             in
             let v_id'1836 =
               Obj.magic
                 v_toOpId'1811
                 v_label'1835
             in
             let v_defaultCase'2490 =
               fun nv_ ->
                 failwith
                   "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 448:13-448:18 ERROR: Reached a never term, which should be impossible in a well-typed program."
             in
             match
               Obj.magic
                 v_prod'1834
             with
             | CBreakableAtom'1698 v_x'2491 ->
                 (match
                    Obj.magic
                      (let v__target'2492 =
                         Obj.magic
                           Obj.magic
                           v_prod'1834
                       in
                       let
                         CRec'2290 ({lconstruct = v_construct'2493})
                       =
                         Obj.magic
                           Obj.magic
                           v__target'2492
                       in
                       Option.Some (v_construct'2493))
                  with
                  | Option.Some (v_construct'1837) ->
                      (Obj.magic
                         v_updateRef'1832
                         v_atoms'1826
                         (Obj.magic
                            Boot.Intrinsics.Mseq.cons
                            (CRec'2339 { l0 =
                                 (Obj.repr
                                   v_label'1835);
                               l1 =
                                 (Obj.repr
                                   (CAtomI'1711 { lconstruct =
                                        (Obj.repr
                                          v_construct'1837);
                                      lid =
                                        (Obj.repr
                                          v_id'1836) })) })))
                  | Option.None ->
                      (Obj.magic
                         (Obj.magic
                            v_defaultCase'2490
                            ())))
             | CBreakableInfix'1699 v_x'2494 ->
                 (Obj.magic
                    (match
                       Obj.magic
                         (let v__target'2495 =
                            Obj.magic
                              Obj.magic
                              v_prod'1834
                          in
                          let
                            CRec'2291 ({lconstruct = v_construct'2496;lleftAllow = v_leftAllow'2497;lrightAllow = v_rightAllow'2498})
                          =
                            Obj.magic
                              Obj.magic
                              v__target'2495
                          in
                          Option.Some (v_construct'2496, v_leftAllow'2497, v_rightAllow'2498))
                     with
                     | Option.Some (v_c'1841, v_l'1842, v_r'1843) ->
                         (let v_l'1844 =
                            Obj.magic
                              v_breakableMapAllowSet
                              v_toOpId'1811
                              v__cmpOpId
                              v_l'1842
                          in
                          let v_r'1845 =
                            Obj.magic
                              v_breakableMapAllowSet
                              v_toOpId'1811
                              v__cmpOpId
                              v_r'1843
                          in
                          let v_p'1846 =
                            Obj.magic
                              v_getGroupingByRight'1825
                              v_id'1836
                          in
                          Obj.magic
                            v_updateRef'1832
                            v_infixes'1828
                            (Obj.magic
                               Boot.Intrinsics.Mseq.cons
                               (CRec'2339 { l0 =
                                    (Obj.repr
                                      v_label'1835);
                                  l1 =
                                    (Obj.repr
                                      (CInfixI'1712 { lconstruct =
                                           (Obj.repr
                                             v_c'1841);
                                         lleftAllow =
                                           (Obj.repr
                                             v_l'1844);
                                         lrightAllow =
                                           (Obj.repr
                                             v_r'1845);
                                         lid =
                                           (Obj.repr
                                             v_id'1836);
                                         lprecWhenThisIsRight =
                                           (Obj.repr
                                             v_p'1846) })) })))
                     | Option.None ->
                         (Obj.magic
                            (Obj.magic
                               v_defaultCase'2490
                               ()))))
             | CBreakablePrefix'1700 v_x'2499 ->
                 (Obj.magic
                    (match
                       Obj.magic
                         (let v__target'2500 =
                            Obj.magic
                              Obj.magic
                              v_prod'1834
                          in
                          let
                            CRec'2292 ({lconstruct = v_construct'2501;lrightAllow = v_rightAllow'2502})
                          =
                            Obj.magic
                              Obj.magic
                              v__target'2500
                          in
                          Option.Some (v_construct'2501, v_rightAllow'2502))
                     with
                     | Option.Some (v_c'1838, v_r'1839) ->
                         (let v_r'1840 =
                            Obj.magic
                              v_breakableMapAllowSet
                              v_toOpId'1811
                              v__cmpOpId
                              v_r'1839
                          in
                          Obj.magic
                            v_updateRef'1832
                            v_prefixes'1827
                            (Obj.magic
                               Boot.Intrinsics.Mseq.cons
                               (CRec'2339 { l0 =
                                    (Obj.repr
                                      v_label'1835);
                                  l1 =
                                    (Obj.repr
                                      (CPrefixI'1713 { lconstruct =
                                           (Obj.repr
                                             v_c'1838);
                                         lrightAllow =
                                           (Obj.repr
                                             v_r'1840);
                                         lid =
                                           (Obj.repr
                                             v_id'1836) })) })))
                     | Option.None ->
                         (Obj.magic
                            (Obj.magic
                               v_defaultCase'2490
                               ()))))
             | CBreakablePostfix'1701 v_x'2503 ->
                 (Obj.magic
                    (match
                       Obj.magic
                         (let v__target'2504 =
                            Obj.magic
                              Obj.magic
                              v_prod'1834
                          in
                          let
                            CRec'2293 ({lconstruct = v_construct'2505;lleftAllow = v_leftAllow'2506})
                          =
                            Obj.magic
                              Obj.magic
                              v__target'2504
                          in
                          Option.Some (v_construct'2505, v_leftAllow'2506))
                     with
                     | Option.Some (v_c'1847, v_l'1848) ->
                         (let v_l'1849 =
                            Obj.magic
                              v_breakableMapAllowSet
                              v_toOpId'1811
                              v__cmpOpId
                              v_l'1848
                          in
                          let v_p'1850 =
                            Obj.magic
                              v_getGroupingByRight'1825
                              v_id'1836
                          in
                          Obj.magic
                            v_updateRef'1832
                            v_postfixes'1829
                            (Obj.magic
                               Boot.Intrinsics.Mseq.cons
                               (CRec'2339 { l0 =
                                    (Obj.repr
                                      v_label'1835);
                                  l1 =
                                    (Obj.repr
                                      (CPostfixI'1714 { lconstruct =
                                           (Obj.repr
                                             v_c'1847);
                                         lleftAllow =
                                           (Obj.repr
                                             v_l'1849);
                                         lid =
                                           (Obj.repr
                                             v_id'1836);
                                         lprecWhenThisIsRight =
                                           (Obj.repr
                                             v_p'1850) })) })))
                     | Option.None ->
                         (Obj.magic
                            (Obj.magic
                               v_defaultCase'2490
                               ()))))
             | _ ->
                 (Obj.magic
                    (v_defaultCase'2490
                       ())))
      in
      CRec'2319 { ltopAllowed =
          (Obj.repr
            (Obj.magic
               v_breakableMapAllowSet
               v_toOpId'1811
               v__cmpOpId
               (let
                  CRec'2338 ({ltopAllowed = v_X'1852})
                =
                  Obj.magic
                    v_grammar'1795
                in
                Obj.magic
                  v_X'1852)));
        latoms =
          (Obj.repr
            (Obj.magic
               v_mapFromSeq
               v_cmp'1794
               (Obj.magic
                  (!)
                  v_atoms'1826)));
        lprefixes =
          (Obj.repr
            (Obj.magic
               v_mapFromSeq
               v_cmp'1794
               (Obj.magic
                  (!)
                  v_prefixes'1827)));
        linfixes =
          (Obj.repr
            (Obj.magic
               v_mapFromSeq
               v_cmp'1794
               (Obj.magic
                  (!)
                  v_infixes'1828)));
        lpostfixes =
          (Obj.repr
            (Obj.magic
               v_mapFromSeq
               v_cmp'1794
               (Obj.magic
                  (!)
                  v_postfixes'1829))) };;
let v_breakableInitState =
  fun v_grammar'1854 ->
    fun v_'1855 ->
      let v_timestep'1856 =
        Obj.magic
          ref
          v__firstTimeStep
      in
      let v_nextIdx'1857 =
        Obj.magic
          ref
          0
      in
      let v_addedLeft'1858 =
        Obj.magic
          ref
          (CRec'2339 { l0 =
               (Obj.repr
                 v__firstTimeStep);
             l1 =
               (Obj.repr
                 (Obj.magic
                    ref
                    (Obj.magic
                       Boot.Intrinsics.Mseq.Helpers.of_array
                       [|  |]))) })
      in
      let v_addedRight'1859 =
        Obj.magic
          ref
          (CRec'2339 { l0 =
               (Obj.repr
                 v__firstTimeStep);
             l1 =
               (Obj.repr
                 (Obj.magic
                    Boot.Intrinsics.Mseq.Helpers.of_array
                    [|  |])) })
      in
      CRec'2311 { ltimestep =
          (Obj.repr
            v_timestep'1856);
        lnextIdx =
          (Obj.repr
            v_nextIdx'1857);
        lfrontier =
          (Obj.repr
            (Obj.magic
               Boot.Intrinsics.Mseq.Helpers.of_array
               [| (Obj.magic
                   (CTentativeRoot'1728 { laddedNodesLeftChildren =
                        (Obj.repr
                          v_addedLeft'1858);
                      laddedNodesRightChildren =
                        (Obj.repr
                          v_addedRight'1859);
                      lallowedChildren =
                        (Obj.repr
                          (let
                             CRec'2319 ({ltopAllowed = v_X'1860})
                           =
                             Obj.magic
                               v_grammar'1854
                           in
                           Obj.magic
                             v_X'1860)) })) |])) };;
let rec v__maxDistanceFromRoot =
    fun v_n'1863 ->
      let v_defaultCase'2507 =
        fun nv_ ->
          let v_'1867 =
            Obj.magic
              v_dprintLn
              v_n'1863
          in
          failwith
            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 477:4-477:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
      in
      match
        Obj.magic
          v_n'1863
      with
      | CTentativeLeaf'1726 v_x'2508 ->
          (match
             Obj.magic
               (let v__target'2509 =
                  Obj.magic
                    Obj.magic
                    v_n'1863
                in
                let
                  CRec'2334 ({lparents = v_parents'2510})
                =
                  Obj.magic
                    Obj.magic
                    v__target'2509
                in
                Option.Some (v_parents'2510))
           with
           | Option.Some (v_parents'1865) ->
               (Obj.magic
                  v_maxOrElse
                  (fun v_'1866 ->
                     0)
                  Int.sub
                  (Obj.magic
                     Boot.Intrinsics.Mseq.map
                     v__maxDistanceFromRoot
                     v_parents'1865))
           | Option.None ->
               (Obj.magic
                  (Obj.magic
                     v_defaultCase'2507
                     ())))
      | CTentativeMid'1727 v_x'2511 ->
          (Obj.magic
             (match
                Obj.magic
                  (let v__target'2512 =
                     Obj.magic
                       Obj.magic
                       v_n'1863
                   in
                   let
                     CRec'2332 ({lmaxDistanceFromRoot = v_maxDistanceFromRoot'2513})
                   =
                     Obj.magic
                       Obj.magic
                       v__target'2512
                   in
                   Option.Some (v_maxDistanceFromRoot'2513))
              with
              | Option.Some (v_r'1864) ->
                  v_r'1864
              | Option.None ->
                  (Obj.magic
                     (Obj.magic
                        v_defaultCase'2507
                        ()))))
      | CTentativeRoot'1728 v_x'2514 ->
          (Obj.magic
             0)
      | _ ->
          (Obj.magic
             (v_defaultCase'2507
                ()));;
let v__shallowAllowedLeft =
  fun v_parent'1868 ->
    fun v_child'1869 ->
      match
        Obj.magic
          (let v__target'2515 =
             v_child'1869
           in
           match
             Obj.magic
               Obj.magic
               v__target'2515
           with
           | CTentativeLeaf'1726 v__n'2516 ->
               (let
                  CRec'2334 ({lnode = v_node'2517})
                =
                  Obj.magic
                    Obj.magic
                    v__target'2515
                in
                Option.Some (v_node'2517))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_node'1870) ->
          (match
             Obj.magic
               (let v__target'2518 =
                  v_parent'1868
                in
                match
                  match
                    match
                      Obj.magic
                        Obj.magic
                        v__target'2518
                    with
                    | CInfixI'1712 v__n'2519 ->
                        (let
                           CRec'2317 ({lleftAllow = v_leftAllow'2520})
                         =
                           Obj.magic
                             Obj.magic
                             v__target'2518
                         in
                         Option.Some (v_leftAllow'2520))
                    | _ ->
                        (Obj.magic
                           Obj.magic
                           (Option.None))
                  with
                  | Option.Some v__x'2523 ->
                      (Option.Some v__x'2523)
                  | Option.None ->
                      (Obj.magic
                         Obj.magic
                         (match
                            Obj.magic
                              Obj.magic
                              v__target'2518
                          with
                          | CPostfixI'1714 v__n'2521 ->
                              (let
                                 CRec'2318 ({lleftAllow = v_leftAllow'2522})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2518
                               in
                               Option.Some (v_leftAllow'2522))
                          | _ ->
                              (Obj.magic
                                 Obj.magic
                                 (Option.None))))
                with
                | Option.Some (v_s'1871) ->
                    (Option.Some (v_s'1871))
                | Option.None ->
                    (Obj.magic
                       Obj.magic
                       (Option.None)))
           with
           | Option.Some (v_s'1871) ->
               (if
                  Obj.magic
                    (Obj.magic
                       v_breakableInAllowSet
                       (Obj.magic
                          v__opIdP
                          v_node'1870)
                       v_s'1871)
                then
                  CSome'1620 (Obj.repr
                     v_node'1870)
                else
                  Obj.magic
                    CNone'1621)
           | Option.None ->
               (Obj.magic
                  (failwith
                     "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 488:11-488:16 ERROR: Reached a never term, which should be impossible in a well-typed program.")))
      | Option.None ->
          (Obj.magic
             (failwith
                "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 489:9-489:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__shallowAllowedRight =
  fun v_parent'1873 ->
    fun v_child'1874 ->
      match
        Obj.magic
          (let v__target'2524 =
             v_child'1874
           in
           match
             Obj.magic
               Obj.magic
               v__target'2524
           with
           | CTentativeLeaf'1726 v__n'2525 ->
               (let
                  CRec'2334 ({lnode = v_node'2526})
                =
                  Obj.magic
                    Obj.magic
                    v__target'2524
                in
                Option.Some (v_node'2526))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_node'1875) ->
          (match
             Obj.magic
               (let v__target'2527 =
                  v_parent'1873
                in
                match
                  match
                    match
                      Obj.magic
                        Obj.magic
                        v__target'2527
                    with
                    | CTentativeRoot'1728 v__n'2528 ->
                        (let
                           CRec'2322 ({lallowedChildren = v_allowedChildren'2529})
                         =
                           Obj.magic
                             Obj.magic
                             v__target'2527
                         in
                         Option.Some (v_allowedChildren'2529))
                    | _ ->
                        (Obj.magic
                           Obj.magic
                           (Option.None))
                  with
                  | Option.Some v__x'2541 ->
                      (Option.Some v__x'2541)
                  | Option.None ->
                      (Obj.magic
                         Obj.magic
                         (match
                            Obj.magic
                              Obj.magic
                              v__target'2527
                          with
                          | CTentativeMid'1727 v__n'2530 ->
                              (let
                                 CRec'2332 ({ltentativeData = v_tentativeData'2531})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2527
                               in
                               match
                                 match
                                   match
                                     Obj.magic
                                       Obj.magic
                                       v_tentativeData'2531
                                   with
                                   | CInfixT'1722 v__n'2532 ->
                                       (let
                                          CRec'2323 ({linput = v_input'2533})
                                        =
                                          Obj.magic
                                            Obj.magic
                                            v_tentativeData'2531
                                        in
                                        match
                                          Obj.magic
                                            Obj.magic
                                            v_input'2533
                                        with
                                        | CInfixI'1712 v__n'2534 ->
                                            (let
                                               CRec'2317 ({lrightAllow = v_rightAllow'2535})
                                             =
                                               Obj.magic
                                                 Obj.magic
                                                 v_input'2533
                                             in
                                             Option.Some (v_rightAllow'2535))
                                        | _ ->
                                            (Obj.magic
                                               Obj.magic
                                               (Option.None)))
                                   | _ ->
                                       (Obj.magic
                                          Obj.magic
                                          (Option.None))
                                 with
                                 | Option.Some v__x'2540 ->
                                     (Option.Some v__x'2540)
                                 | Option.None ->
                                     (Obj.magic
                                        Obj.magic
                                        (match
                                           Obj.magic
                                             Obj.magic
                                             v_tentativeData'2531
                                         with
                                         | CPrefixT'1723 v__n'2536 ->
                                             (let
                                                CRec'2331 ({linput = v_input'2537})
                                              =
                                                Obj.magic
                                                  Obj.magic
                                                  v_tentativeData'2531
                                              in
                                              match
                                                Obj.magic
                                                  Obj.magic
                                                  v_input'2537
                                              with
                                              | CPrefixI'1713 v__n'2538 ->
                                                  (let
                                                     CRec'2316 ({lrightAllow = v_rightAllow'2539})
                                                   =
                                                     Obj.magic
                                                       Obj.magic
                                                       v_input'2537
                                                   in
                                                   Option.Some (v_rightAllow'2539))
                                              | _ ->
                                                  (Obj.magic
                                                     Obj.magic
                                                     (Option.None)))
                                         | _ ->
                                             (Obj.magic
                                                Obj.magic
                                                (Option.None))))
                               with
                               | Option.Some (v_s'1876) ->
                                   (Option.Some (v_s'1876))
                               | Option.None ->
                                   (Obj.magic
                                      Obj.magic
                                      (Option.None)))
                          | _ ->
                              (Obj.magic
                                 Obj.magic
                                 (Option.None))))
                with
                | Option.Some (v_s'1876) ->
                    (Option.Some (v_s'1876))
                | Option.None ->
                    (Obj.magic
                       Obj.magic
                       (Option.None)))
           with
           | Option.Some (v_s'1876) ->
               (if
                  Obj.magic
                    (Obj.magic
                       v_breakableInAllowSet
                       (Obj.magic
                          v__opIdP
                          v_node'1875)
                       v_s'1876)
                then
                  CSome'1620 (Obj.repr
                     v_node'1875)
                else
                  Obj.magic
                    CNone'1621)
           | Option.None ->
               (Obj.magic
                  (let v_'1877 =
                     Obj.magic
                       v_dprintLn
                       v_parent'1873
                   in
                   failwith
                     "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 502:28-502:33 ERROR: Reached a never term, which should be impossible in a well-typed program.")))
      | Option.None ->
          (Obj.magic
             (failwith
                "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 503:9-503:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__addRightChildren =
  fun v_st'1879 ->
    fun v_parent'1880 ->
      fun v_children'1881 ->
        let v_defaultCase'2542 =
          fun nv_ ->
            failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 522:9-522:14 ERROR: Reached a never term, which should be impossible in a well-typed program."
        in
        match
          Obj.magic
            v_parent'1880
        with
        | CTentativeMid'1727 v_x'2543 ->
            (match
               Obj.magic
                 (let v__target'2544 =
                    Obj.magic
                      Obj.magic
                      v_parent'1880
                  in
                  let
                    CRec'2332 ({lparents = v_parents'2545;ltentativeData = v_tentativeData'2546})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2544
                  in
                  Option.Some (v_parents'2545, v_tentativeData'2546))
             with
             | Option.Some (v_parents'1882, v_data'1883) ->
                 (let v_id'1884 =
                    Obj.magic
                      v__uniqueID
                      ()
                  in
                  let v_node'1892 =
                    let v_defaultCase'2547 =
                      fun nv_ ->
                        failwith
                          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 518:13-518:18 ERROR: Reached a never term, which should be impossible in a well-typed program."
                    in
                    match
                      Obj.magic
                        v_data'1883
                    with
                    | CInfixT'1722 v_x'2548 ->
                        (match
                           Obj.magic
                             (let v__target'2549 =
                                Obj.magic
                                  Obj.magic
                                  v_data'1883
                              in
                              let
                                CRec'2323 ({lidx = v_idx'2550;linput = v_input'2551;lself = v_self'2552;lleftChildAlts = v_leftChildAlts'2553})
                              =
                                Obj.magic
                                  Obj.magic
                                  v__target'2549
                              in
                              Option.Some (v_idx'2550, v_input'2551, v_self'2552, v_leftChildAlts'2553))
                         with
                         | Option.Some (v_idx'1885, v_input'1886, v_self'1887, v_l'1888) ->
                             (CInfixP'1718 { lid =
                                  (Obj.repr
                                    v_id'1884);
                                lidx =
                                  (Obj.repr
                                    v_idx'1885);
                                linput =
                                  (Obj.repr
                                    v_input'1886);
                                lself =
                                  (Obj.repr
                                    v_self'1887);
                                lleftChildAlts =
                                  (Obj.repr
                                    v_l'1888);
                                lrightChildAlts =
                                  (Obj.repr
                                    v_children'1881) })
                         | Option.None ->
                             (Obj.magic
                                (Obj.magic
                                   v_defaultCase'2547
                                   ())))
                    | CPrefixT'1723 v_x'2554 ->
                        (Obj.magic
                           (match
                              Obj.magic
                                (let v__target'2555 =
                                   Obj.magic
                                     Obj.magic
                                     v_data'1883
                                 in
                                 let
                                   CRec'2331 ({lidx = v_idx'2556;linput = v_input'2557;lself = v_self'2558})
                                 =
                                   Obj.magic
                                     Obj.magic
                                     v__target'2555
                                 in
                                 Option.Some (v_idx'2556, v_input'2557, v_self'2558))
                            with
                            | Option.Some (v_idx'1889, v_input'1890, v_self'1891) ->
                                (CPrefixP'1719 { lid =
                                     (Obj.repr
                                       v_id'1884);
                                   lidx =
                                     (Obj.repr
                                       v_idx'1889);
                                   linput =
                                     (Obj.repr
                                       v_input'1890);
                                   lself =
                                     (Obj.repr
                                       v_self'1891);
                                   lrightChildAlts =
                                     (Obj.repr
                                       v_children'1881) })
                            | Option.None ->
                                (Obj.magic
                                   (Obj.magic
                                      v_defaultCase'2547
                                      ()))))
                    | _ ->
                        (Obj.magic
                           (v_defaultCase'2547
                              ()))
                  in
                  CTentativeLeaf'1726 { lparents =
                      (Obj.repr
                        v_parents'1882);
                    lnode =
                      (Obj.repr
                        v_node'1892) })
             | Option.None ->
                 (Obj.magic
                    (Obj.magic
                       v_defaultCase'2542
                       ())))
        | CTentativeRoot'1728 v_x'2559 ->
            (Obj.magic
               (Obj.magic
                  Boot.Intrinsics.MSys.error
                  (Obj.magic
                     Boot.Intrinsics.Mseq.Helpers.of_array
                     [| (85);
                       (110);
                       (101);
                       (120);
                       (112);
                       (101);
                       (99);
                       (116);
                       (101);
                       (100);
                       (108);
                       (121);
                       (32);
                       (116);
                       (114);
                       (105);
                       (101);
                       (100);
                       (32);
                       (116);
                       (111);
                       (32);
                       (97);
                       (100);
                       (100);
                       (32);
                       (114);
                       (105);
                       (103);
                       (104);
                       (116);
                       (32);
                       (99);
                       (104);
                       (105);
                       (108);
                       (100);
                       (114);
                       (101);
                       (110);
                       (32);
                       (116);
                       (111);
                       (32);
                       (116);
                       (104);
                       (101);
                       (32);
                       (114);
                       (111);
                       (111);
                       (116) |])))
        | _ ->
            (Obj.magic
               (v_defaultCase'2542
                  ()));;
let v__addLeftChildren =
  fun v_st'1894 ->
    fun v_input'1895 ->
      fun v_self'1896 ->
        fun v_leftChildren'1897 ->
          fun v_parents'1898 ->
            let v_idx'1900 =
              Obj.magic
                (!)
                (let
                   CRec'2311 ({lnextIdx = v_X'1899})
                 =
                   Obj.magic
                     v_st'1894
                 in
                 Obj.magic
                   v_X'1899)
            in
            let v_defaultCase'2560 =
              fun nv_ ->
                failwith
                  "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 550:9-550:14 ERROR: Reached a never term, which should be impossible in a well-typed program."
            in
            match
              Obj.magic
                v_input'1895
            with
            | CInfixI'1712 v_x'2561 ->
                (let v_time'1902 =
                   Obj.magic
                     (!)
                     (let
                        CRec'2311 ({ltimestep = v_X'1901})
                      =
                        Obj.magic
                          v_st'1894
                      in
                      Obj.magic
                        v_X'1901)
                 in
                 let v_addedLeft'1903 =
                   Obj.magic
                     ref
                     (CRec'2339 { l0 =
                          (Obj.repr
                            v__firstTimeStep);
                        l1 =
                          (Obj.repr
                            (Obj.magic
                               ref
                               (Obj.magic
                                  Boot.Intrinsics.Mseq.Helpers.of_array
                                  [|  |]))) })
                 in
                 let v_addedRight'1904 =
                   Obj.magic
                     ref
                     (CRec'2339 { l0 =
                          (Obj.repr
                            v__firstTimeStep);
                        l1 =
                          (Obj.repr
                            (Obj.magic
                               Boot.Intrinsics.Mseq.Helpers.of_array
                               [|  |])) })
                 in
                 CTentativeMid'1727 { lparents =
                     (Obj.repr
                       v_parents'1898);
                   laddedNodesLeftChildren =
                     (Obj.repr
                       v_addedLeft'1903);
                   laddedNodesRightChildren =
                     (Obj.repr
                       v_addedRight'1904);
                   ltentativeData =
                     (Obj.repr
                       (CInfixT'1722 { lidx =
                            (Obj.repr
                              v_idx'1900);
                          linput =
                            (Obj.repr
                              v_input'1895);
                          lself =
                            (Obj.repr
                              v_self'1896);
                          lleftChildAlts =
                            (Obj.repr
                              v_leftChildren'1897) }));
                   lmaxDistanceFromRoot =
                     (Obj.repr
                       (Obj.magic
                          Int.add
                          1
                          (Obj.magic
                             v_maxOrElse
                             (fun v_'1905 ->
                                0)
                             Int.sub
                             (Obj.magic
                                Boot.Intrinsics.Mseq.map
                                v__maxDistanceFromRoot
                                v_parents'1898)))) })
            | CPostfixI'1714 v_x'2562 ->
                (Obj.magic
                   (let v_id'1906 =
                      Obj.magic
                        v__uniqueID
                        ()
                    in
                    CTentativeLeaf'1726 { lparents =
                        (Obj.repr
                          v_parents'1898);
                      lnode =
                        (Obj.repr
                          (CPostfixP'1720 { lid =
                               (Obj.repr
                                 v_id'1906);
                             lidx =
                               (Obj.repr
                                 v_idx'1900);
                             linput =
                               (Obj.repr
                                 v_input'1895);
                             lself =
                               (Obj.repr
                                 v_self'1896);
                             lleftChildAlts =
                               (Obj.repr
                                 v_leftChildren'1897) })) }))
            | _ ->
                (Obj.magic
                   (v_defaultCase'2560
                      ()));;
let v__addRightChildToParent =
  fun v_time'1908 ->
    fun v_child'1909 ->
      fun v_parent'1910 ->
        let v_target'1911 =
          Obj.magic
            v__addedNodesRightChildren
            v_parent'1910
        in
        match
          Obj.magic
            (let v__target'2563 =
               Obj.magic
                 (!)
                 v_target'1911
             in
             let
               CRec'2339 ({l0 = v_0'2564;l1 = v_1'2565})
             =
               Obj.magic
                 Obj.magic
                 v__target'2563
             in
             Option.Some (v_0'2564, v_1'2565))
        with
        | Option.Some (v_lastUpdate'1912, v_prev'1913) ->
            (if
               Obj.magic
                 (Obj.magic
                    v__isBefore
                    v_lastUpdate'1912
                    v_time'1908)
             then
               let v_'1914 =
                 Obj.magic
                   (:=)
                   v_target'1911
                   (CRec'2339 { l0 =
                        (Obj.repr
                          v_time'1908);
                      l1 =
                        (Obj.repr
                          (Obj.magic
                             Boot.Intrinsics.Mseq.Helpers.of_array
                             [| (Obj.magic
                                 v_child'1909) |])) })
               in
               CSome'1620 (Obj.repr
                  v_parent'1910)
             else
               Obj.magic
                 (let v_'1915 =
                    Obj.magic
                      (:=)
                      v_target'1911
                      (CRec'2339 { l0 =
                           (Obj.repr
                             v_time'1908);
                         l1 =
                           (Obj.repr
                             (Obj.magic
                                Boot.Intrinsics.Mseq.cons
                                v_child'1909
                                v_prev'1913)) })
                  in
                  CNone'1621))
        | Option.None ->
            (Obj.magic
               (failwith
                  "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 566:9-566:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__addLeftChildToParent =
  fun v_time'1917 ->
    fun v_child'1918 ->
      fun v_parents'1919 ->
        match
          Obj.magic
            (let v__target'2566 =
               v_parents'1919
             in
             if
               Obj.magic
                 ((<) : int -> int -> bool)
                 (Obj.magic
                    Boot.Intrinsics.Mseq.length
                    v__target'2566)
                 1
             then
               Option.None
             else
               Obj.magic
                 Obj.magic
                 (let
                    (v__prefix'2567, v__splitTemp'2568)
                  =
                    Obj.magic
                      Boot.Intrinsics.Mseq.split_at
                      v__target'2566
                      1
                  in
                  let
                    (v__middle'2569, v__postfix'2570)
                  =
                    Obj.magic
                      Boot.Intrinsics.Mseq.split_at
                      v__splitTemp'2568
                      (Obj.magic
                         Int.sub
                         (Obj.magic
                            Boot.Intrinsics.Mseq.length
                            v__splitTemp'2568)
                         0)
                  in
                  let v__seqElem'2571 =
                    Obj.magic
                      Boot.Intrinsics.Mseq.get
                      v__prefix'2567
                      0
                  in
                  Option.Some (v__seqElem'2571)))
        with
        | Option.Some (v_p'1920) ->
            (let v_target'1921 =
               Obj.magic
                 v__addedNodesLeftChildren
                 v_p'1920
             in
             match
               Obj.magic
                 (let v__target'2572 =
                    Obj.magic
                      (!)
                      v_target'1921
                  in
                  let
                    CRec'2339 ({l0 = v_0'2573;l1 = v_1'2574})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2572
                  in
                  Option.Some (v_0'2573, v_1'2574))
             with
             | Option.Some (v_lastUpdate'1922, v_prev'1923) ->
                 (if
                    Obj.magic
                      (Obj.magic
                         v__isBefore
                         v_lastUpdate'1922
                         v_time'1917)
                  then
                    let v_leftChildrenHere'1924 =
                      Obj.magic
                        ref
                        (Obj.magic
                           Boot.Intrinsics.Mseq.Helpers.of_array
                           [| (Obj.magic
                               v_child'1918) |])
                    in
                    let v_'1926 =
                      Obj.magic
                        v_for_
                        v_parents'1919
                        (fun v_p'1925 ->
                           Obj.magic
                             (:=)
                             (Obj.magic
                                v__addedNodesLeftChildren
                                v_p'1925)
                             (CRec'2339 { l0 =
                                  (Obj.repr
                                    v_time'1917);
                                l1 =
                                  (Obj.repr
                                    v_leftChildrenHere'1924) }))
                    in
                    CSome'1620 (Obj.repr
                       v_parents'1919)
                  else
                    Obj.magic
                      (let v_'1927 =
                         Obj.magic
                           (:=)
                           v_prev'1923
                           (Obj.magic
                              Boot.Intrinsics.Mseq.cons
                              v_child'1918
                              (Obj.magic
                                 (!)
                                 v_prev'1923))
                       in
                       CNone'1621))
             | Option.None ->
                 (Obj.magic
                    (failwith
                       "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 584:11-584:16 ERROR: Reached a never term, which should be impossible in a well-typed program.")))
        | Option.None ->
            (Obj.magic
               (failwith
                  "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 585:9-585:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__getOpGroup =
  fun v_input'1929 ->
    fun v_id'1930 ->
      if
        Obj.magic
          (Obj.magic
             v__eqOpId
             v_id'1930
             v__rootID)
      then
        CRec'2294 { lmayGroupLeft =
            (Obj.repr
              false);
          lmayGroupRight =
            (Obj.repr
              true) }
      else
        Obj.magic
          (match
             Obj.magic
               (let v__target'2575 =
                  v_input'1929
                in
                match
                  match
                    match
                      Obj.magic
                        Obj.magic
                        v__target'2575
                    with
                    | CInfixI'1712 v__n'2576 ->
                        (let
                           CRec'2317 ({lprecWhenThisIsRight = v_precWhenThisIsRight'2577})
                         =
                           Obj.magic
                             Obj.magic
                             v__target'2575
                         in
                         Option.Some (v_precWhenThisIsRight'2577))
                    | _ ->
                        (Obj.magic
                           Obj.magic
                           (Option.None))
                  with
                  | Option.Some v__x'2580 ->
                      (Option.Some v__x'2580)
                  | Option.None ->
                      (Obj.magic
                         Obj.magic
                         (match
                            Obj.magic
                              Obj.magic
                              v__target'2575
                          with
                          | CPostfixI'1714 v__n'2578 ->
                              (let
                                 CRec'2318 ({lprecWhenThisIsRight = v_precWhenThisIsRight'2579})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2575
                               in
                               Option.Some (v_precWhenThisIsRight'2579))
                          | _ ->
                              (Obj.magic
                                 Obj.magic
                                 (Option.None))))
                with
                | Option.Some (v_prec'1931) ->
                    (Option.Some (v_prec'1931))
                | Option.None ->
                    (Obj.magic
                       Obj.magic
                       (Option.None)))
           with
           | Option.Some (v_prec'1931) ->
               (match
                  Obj.magic
                    (let v__target'2581 =
                       Obj.magic
                         v_mapLookup
                         v_id'1930
                         v_prec'1931
                     in
                     match
                       Obj.magic
                         Obj.magic
                         v__target'2581
                     with
                     | CSome'1620 v__n'2582 ->
                         (Option.Some (v__n'2582))
                     | _ ->
                         (Obj.magic
                            Obj.magic
                            (Option.None)))
                with
                | Option.Some (v_res'1932) ->
                    v_res'1932
                | Option.None ->
                    (Obj.magic
                       (CRec'2294 { lmayGroupLeft =
                            (Obj.repr
                              true);
                          lmayGroupRight =
                            (Obj.repr
                              true) })))
           | Option.None ->
               (Obj.magic
                  (failwith
                     "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 597:9-597:14 ERROR: Reached a never term, which should be impossible in a well-typed program.")));;
let v__mayGroupRight =
  fun v_l'1934 ->
    fun v_r'1935 ->
      let
        CRec'2294 ({lmayGroupRight = v_X'1936})
      =
        Obj.magic
          (Obj.magic
             v__getOpGroup
             v_r'1935
             (Obj.magic
                v__opIdT
                v_l'1934))
      in
      Obj.magic
        v_X'1936;;
let v__mayGroupLeft =
  fun v_l'1938 ->
    fun v_r'1939 ->
      let
        CRec'2294 ({lmayGroupLeft = v_X'1940})
      =
        Obj.magic
          (Obj.magic
             v__getOpGroup
             v_r'1939
             (Obj.magic
                v__opIdT
                v_l'1938))
      in
      Obj.magic
        v_X'1940;;
let v__newQueueFromFrontier =
  fun v_frontier'1943 ->
    Obj.magic
      Boot.Intrinsics.Mseq.create
      (Obj.magic
         Int.add
         1
         (Obj.magic
            v_maxOrElse
            (fun v_'1944 ->
               0)
            Int.sub
            (Obj.magic
               Boot.Intrinsics.Mseq.map
               v__maxDistanceFromRoot
               v_frontier'1943)))
      (fun v_'1945 ->
         Obj.magic
           ref
           (Obj.magic
              Boot.Intrinsics.Mseq.Helpers.of_array
              [|  |]));;
let v__addToQueue =
  fun v_node'1947 ->
    fun v_queue'1948 ->
      let v_dist'1949 =
        Obj.magic
          v__maxDistanceFromRoot
          v_node'1947
      in
      let v_target'1950 =
        Obj.magic
          Boot.Intrinsics.Mseq.get
          v_queue'1948
          v_dist'1949
      in
      Obj.magic
        (:=)
        v_target'1950
        (Obj.magic
           Boot.Intrinsics.Mseq.snoc
           (Obj.magic
              (!)
              v_target'1950)
           v_node'1947);;
let rec v__popFromQueue =
    fun v_queue'1953 ->
      match
        Obj.magic
          (let v__target'2583 =
             v_queue'1953
           in
           if
             Obj.magic
               ((<) : int -> int -> bool)
               (Obj.magic
                  Boot.Intrinsics.Mseq.length
                  v__target'2583)
               1
           then
             Option.None
           else
             Obj.magic
               Obj.magic
               (let
                  (v__prefix'2584, v__splitTemp'2585)
                =
                  Obj.magic
                    Boot.Intrinsics.Mseq.split_at
                    v__target'2583
                    0
                in
                let
                  (v__middle'2586, v__postfix'2587)
                =
                  Obj.magic
                    Boot.Intrinsics.Mseq.split_at
                    v__splitTemp'2585
                    (Obj.magic
                       Int.sub
                       (Obj.magic
                          Boot.Intrinsics.Mseq.length
                          v__splitTemp'2585)
                       1)
                in
                let v__seqElem'2588 =
                  Obj.magic
                    Boot.Intrinsics.Mseq.get
                    v__postfix'2587
                    0
                in
                Option.Some (v__middle'2586, v__seqElem'2588)))
      with
      | Option.Some (v_queue'1954, v_target'1955) ->
          (let v_nodes'1956 =
             Obj.magic
               (!)
               v_target'1955
           in
           match
             Obj.magic
               (let v__target'2589 =
                  v_nodes'1956
                in
                if
                  Obj.magic
                    ((<) : int -> int -> bool)
                    (Obj.magic
                       Boot.Intrinsics.Mseq.length
                       v__target'2589)
                    1
                then
                  Option.None
                else
                  Obj.magic
                    Obj.magic
                    (let
                       (v__prefix'2590, v__splitTemp'2591)
                     =
                       Obj.magic
                         Boot.Intrinsics.Mseq.split_at
                         v__target'2589
                         1
                     in
                     let
                       (v__middle'2592, v__postfix'2593)
                     =
                       Obj.magic
                         Boot.Intrinsics.Mseq.split_at
                         v__splitTemp'2591
                         (Obj.magic
                            Int.sub
                            (Obj.magic
                               Boot.Intrinsics.Mseq.length
                               v__splitTemp'2591)
                            0)
                     in
                     let v__seqElem'2594 =
                       Obj.magic
                         Boot.Intrinsics.Mseq.get
                         v__prefix'2590
                         0
                     in
                     Option.Some (v__seqElem'2594, v__middle'2592)))
           with
           | Option.Some (v_node'1957, v_nodes'1958) ->
               (let v_'1959 =
                  Obj.magic
                    (:=)
                    v_target'1955
                    v_nodes'1958
                in
                CSome'1620 (Obj.repr
                   v_node'1957))
           | Option.None ->
               (Obj.magic
                  (Obj.magic
                     v__popFromQueue
                     v_queue'1954)))
      | Option.None ->
          (Obj.magic
             CNone'1621);;
let v__addLOpen =
  fun v_input'1960 ->
    fun v_self'1961 ->
      fun v_st'1962 ->
        let v_time'1964 =
          Obj.magic
            Int.add
            1
            (Obj.magic
               (!)
               (let
                  CRec'2311 ({ltimestep = v_X'1963})
                =
                  Obj.magic
                    v_st'1962
                in
                Obj.magic
                  v_X'1963))
        in
        let v_'1966 =
          Obj.magic
            (:=)
            (let
               CRec'2311 ({ltimestep = v_X'1965})
             =
               Obj.magic
                 v_st'1962
             in
             Obj.magic
               v_X'1965)
            v_time'1964
        in
        let v_makeNewParents'1973 =
          fun v_parents'1967 ->
            match
              Obj.magic
                (let v__target'2595 =
                   v_parents'1967
                 in
                 if
                   Obj.magic
                     ((<) : int -> int -> bool)
                     (Obj.magic
                        Boot.Intrinsics.Mseq.length
                        v__target'2595)
                     1
                 then
                   Option.None
                 else
                   Obj.magic
                     Obj.magic
                     (let
                        (v__prefix'2596, v__splitTemp'2597)
                      =
                        Obj.magic
                          Boot.Intrinsics.Mseq.split_at
                          v__target'2595
                          1
                      in
                      let
                        (v__middle'2598, v__postfix'2599)
                      =
                        Obj.magic
                          Boot.Intrinsics.Mseq.split_at
                          v__splitTemp'2597
                          (Obj.magic
                             Int.sub
                             (Obj.magic
                                Boot.Intrinsics.Mseq.length
                                v__splitTemp'2597)
                             0)
                      in
                      let v__seqElem'2600 =
                        Obj.magic
                          Boot.Intrinsics.Mseq.get
                          v__prefix'2596
                          0
                      in
                      Option.Some (v__seqElem'2600)))
            with
            | Option.Some (v_p'1968) ->
                (let v_snd'1971 =
                   fun v_x'1969 ->
                     let
                       CRec'2339 ({l1 = v_X'1970})
                     =
                       Obj.magic
                         v_x'1969
                     in
                     Obj.magic
                       v_X'1970
                 in
                 let v_cs'1972 =
                   Obj.magic
                     (!)
                     (Obj.magic
                        v_snd'1971
                        (Obj.magic
                           (!)
                           (Obj.magic
                              v__addedNodesLeftChildren
                              v_p'1968)))
                 in
                 match
                   Obj.magic
                     (let v__target'2601 =
                        v_cs'1972
                      in
                      if
                        Obj.magic
                          ((<) : int -> int -> bool)
                          (Obj.magic
                             Boot.Intrinsics.Mseq.length
                             v__target'2601)
                          1
                      then
                        Option.None
                      else
                        Obj.magic
                          Obj.magic
                          (let
                             (v__prefix'2602, v__splitTemp'2603)
                           =
                             Obj.magic
                               Boot.Intrinsics.Mseq.split_at
                               v__target'2601
                               1
                           in
                           let
                             (v__middle'2604, v__postfix'2605)
                           =
                             Obj.magic
                               Boot.Intrinsics.Mseq.split_at
                               v__splitTemp'2603
                               (Obj.magic
                                  Int.sub
                                  (Obj.magic
                                     Boot.Intrinsics.Mseq.length
                                     v__splitTemp'2603)
                                  0)
                           in
                           let v__seqElem'2606 =
                             Obj.magic
                               Boot.Intrinsics.Mseq.get
                               v__prefix'2602
                               0
                           in
                           Option.Some ()))
                 with
                 | Option.Some () ->
                     (Obj.magic
                        v__addLeftChildren
                        v_st'1962
                        v_input'1960
                        v_self'1961
                        v_cs'1972
                        v_parents'1967)
                 | Option.None ->
                     (Obj.magic
                        (Obj.magic
                           Boot.Intrinsics.MSys.error
                           (Obj.magic
                              Boot.Intrinsics.Mseq.Helpers.of_array
                              [| (83);
                                (111);
                                (109);
                                (101);
                                (104);
                                (111);
                                (119);
                                (32);
                                (116);
                                (104);
                                (111);
                                (117);
                                (103);
                                (104);
                                (116);
                                (32);
                                (116);
                                (104);
                                (97);
                                (116);
                                (32);
                                (97);
                                (32);
                                (110);
                                (111);
                                (100);
                                (101);
                                (32);
                                (119);
                                (111);
                                (117);
                                (108);
                                (100);
                                (32);
                                (98);
                                (101);
                                (32);
                                (97);
                                (32);
                                (110);
                                (101);
                                (119);
                                (32);
                                (112);
                                (97);
                                (114);
                                (101);
                                (110);
                                (116);
                                (44);
                                (32);
                                (98);
                                (117);
                                (116);
                                (32);
                                (105);
                                (116);
                                (32);
                                (104);
                                (97);
                                (100);
                                (32);
                                (110);
                                (111);
                                (32);
                                (97);
                                (100);
                                (100);
                                (101);
                                (100);
                                (32);
                                (99);
                                (104);
                                (105);
                                (108);
                                (100);
                                (114);
                                (101);
                                (110) |]))))
            | Option.None ->
                (Obj.magic
                   (failwith
                      "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 665:13-665:18 ERROR: Reached a never term, which should be impossible in a well-typed program."))
        in
        let v_handleLeaf'1991 =
          fun v_queue'1974 ->
            fun v_child'1975 ->
              match
                Obj.magic
                  (let v__target'2607 =
                     Obj.magic
                       v__getParents
                       v_child'1975
                   in
                   match
                     Obj.magic
                       Obj.magic
                       v__target'2607
                   with
                   | CSome'1620 v__n'2608 ->
                       (Option.Some (v__n'2608))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None)))
              with
              | Option.Some (v_parents'1976) ->
                  (let v_shallowRight'1977 =
                     Obj.magic
                       v__shallowAllowedLeft
                       v_input'1960
                       v_child'1975
                   in
                   let v_f'1987 =
                     fun v_parent'1978 ->
                       let v_shallowLeft'1979 =
                         Obj.magic
                           v__shallowAllowedRight
                           v_parent'1978
                           v_child'1975
                       in
                       let v_precLeft'1980 =
                         Obj.magic
                           v__mayGroupLeft
                           v_parent'1978
                           v_input'1960
                       in
                       let v_precRight'1981 =
                         Obj.magic
                           v__mayGroupRight
                           v_parent'1978
                           v_input'1960
                       in
                       let v_config'1982 =
                         CRec'2329 { l0 =
                             (Obj.repr
                               v_shallowLeft'1979);
                           l1 =
                             (Obj.repr
                               v_shallowRight'1977);
                           l2 =
                             (Obj.repr
                               v_precLeft'1980);
                           l3 =
                             (Obj.repr
                               v_precRight'1981) }
                       in
                       let v_'1985 =
                         match
                           Obj.magic
                             (let v__target'2609 =
                                v_config'1982
                              in
                              match
                                match
                                  let
                                    CRec'2329 ({l0 = v_0'2610;l1 = v_1'2611;l2 = v_2'2612;l3 = v_3'2613})
                                  =
                                    Obj.magic
                                      Obj.magic
                                      v__target'2609
                                  in
                                  match
                                    Obj.magic
                                      Obj.magic
                                      v_0'2610
                                  with
                                  | CSome'1620 v__n'2614 ->
                                      (match
                                         Obj.magic
                                           Obj.magic
                                           v_1'2611
                                       with
                                       | CNone'1621 ->
                                           (Option.Some (v__n'2614))
                                       | _ ->
                                           (Obj.magic
                                              Obj.magic
                                              (Option.None)))
                                  | _ ->
                                      (Obj.magic
                                         Obj.magic
                                         (Option.None))
                                with
                                | Option.Some v__x'2621 ->
                                    (Option.Some v__x'2621)
                                | Option.None ->
                                    (Obj.magic
                                       Obj.magic
                                       (let
                                          CRec'2329 ({l0 = v_0'2616;l1 = v_1'2617;l2 = v_2'2618;l3 = v_3'2619})
                                        =
                                          Obj.magic
                                            Obj.magic
                                            v__target'2609
                                        in
                                        match
                                          Obj.magic
                                            Obj.magic
                                            v_0'2616
                                        with
                                        | CSome'1620 v__n'2620 ->
                                            (if
                                               Obj.magic
                                                 Obj.magic
                                                 v_2'2618
                                             then
                                               Option.Some (v__n'2620)
                                             else
                                               Obj.magic
                                                 Obj.magic
                                                 (Option.None))
                                        | _ ->
                                            (Obj.magic
                                               Obj.magic
                                               (Option.None))))
                              with
                              | Option.Some (v_child'1983) ->
                                  (Option.Some (v_child'1983))
                              | Option.None ->
                                  (Obj.magic
                                     Obj.magic
                                     (Option.None)))
                         with
                         | Option.Some (v_child'1983) ->
                             (match
                                Obj.magic
                                  (let v__target'2622 =
                                     Obj.magic
                                       v__addRightChildToParent
                                       v_time'1964
                                       v_child'1983
                                       v_parent'1978
                                   in
                                   match
                                     Obj.magic
                                       Obj.magic
                                       v__target'2622
                                   with
                                   | CSome'1620 v__n'2623 ->
                                       (Option.Some (v__n'2623))
                                   | _ ->
                                       (Obj.magic
                                          Obj.magic
                                          (Option.None)))
                              with
                              | Option.Some (v_parent'1984) ->
                                  (Obj.magic
                                     v__addToQueue
                                     v_parent'1984
                                     v_queue'1974)
                              | Option.None ->
                                  (Obj.magic
                                     ()))
                         | Option.None ->
                             (Obj.magic
                                ())
                       in
                       match
                         Obj.magic
                           (let v__target'2624 =
                              v_config'1982
                            in
                            match
                              match
                                let
                                  CRec'2329 ({l0 = v_0'2625;l1 = v_1'2626;l2 = v_2'2627;l3 = v_3'2628})
                                =
                                  Obj.magic
                                    Obj.magic
                                    v__target'2624
                                in
                                match
                                  Obj.magic
                                    Obj.magic
                                    v_0'2625
                                with
                                | CNone'1621 ->
                                    (match
                                       Obj.magic
                                         Obj.magic
                                         v_1'2626
                                     with
                                     | CSome'1620 v__n'2630 ->
                                         (Option.Some (v__n'2630))
                                     | _ ->
                                         (Obj.magic
                                            Obj.magic
                                            (Option.None)))
                                | _ ->
                                    (Obj.magic
                                       Obj.magic
                                       (Option.None))
                              with
                              | Option.Some v__x'2636 ->
                                  (Option.Some v__x'2636)
                              | Option.None ->
                                  (Obj.magic
                                     Obj.magic
                                     (let
                                        CRec'2329 ({l0 = v_0'2631;l1 = v_1'2632;l2 = v_2'2633;l3 = v_3'2634})
                                      =
                                        Obj.magic
                                          Obj.magic
                                          v__target'2624
                                      in
                                      match
                                        Obj.magic
                                          Obj.magic
                                          v_1'2632
                                      with
                                      | CSome'1620 v__n'2635 ->
                                          (if
                                             Obj.magic
                                               Obj.magic
                                               v_3'2634
                                           then
                                             Option.Some (v__n'2635)
                                           else
                                             Obj.magic
                                               Obj.magic
                                               (Option.None))
                                      | _ ->
                                          (Obj.magic
                                             Obj.magic
                                             (Option.None))))
                            with
                            | Option.Some (v_child'1986) ->
                                (Option.Some (v_child'1986))
                            | Option.None ->
                                (Obj.magic
                                   Obj.magic
                                   (Option.None)))
                       with
                       | Option.Some (v_child'1986) ->
                           true
                       | Option.None ->
                           (Obj.magic
                              false)
                   in
                   let v_parentsThatAllowRight'1988 =
                     Obj.magic
                       v_filter
                       v_f'1987
                       v_parents'1976
                   in
                   match
                     Obj.magic
                       (let v__target'2637 =
                          CRec'2339 { l0 =
                              (Obj.repr
                                v_shallowRight'1977);
                            l1 =
                              (Obj.repr
                                v_parentsThatAllowRight'1988) }
                        in
                        let
                          CRec'2339 ({l0 = v_0'2638;l1 = v_1'2639})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2637
                        in
                        match
                          Obj.magic
                            Obj.magic
                            v_0'2638
                        with
                        | CSome'1620 v__n'2640 ->
                            (if
                               Obj.magic
                                 ((<) : int -> int -> bool)
                                 (Obj.magic
                                    Boot.Intrinsics.Mseq.length
                                    v_1'2639)
                                 1
                             then
                               Option.None
                             else
                               Obj.magic
                                 Obj.magic
                                 (let
                                    (v__prefix'2641, v__splitTemp'2642)
                                  =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.split_at
                                      v_1'2639
                                      1
                                  in
                                  let
                                    (v__middle'2643, v__postfix'2644)
                                  =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.split_at
                                      v__splitTemp'2642
                                      (Obj.magic
                                         Int.sub
                                         (Obj.magic
                                            Boot.Intrinsics.Mseq.length
                                            v__splitTemp'2642)
                                         0)
                                  in
                                  let v__seqElem'2645 =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.get
                                      v__prefix'2641
                                      0
                                  in
                                  Option.Some (v__n'2640, v_1'2639)))
                        | _ ->
                            (Obj.magic
                               Obj.magic
                               (Option.None)))
                   with
                   | Option.Some (v_child'1989, v_parents'1990) ->
                       (Obj.magic
                          v__addLeftChildToParent
                          v_time'1964
                          v_child'1989
                          v_parents'1990)
                   | Option.None ->
                       (Obj.magic
                          CNone'1621))
              | Option.None ->
                  (Obj.magic
                     (failwith
                        "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 693:13-693:18 ERROR: Reached a never term, which should be impossible in a well-typed program."))
        in
        let rec v_work'1992 =
            fun v_queue'1993 ->
              fun v_acc'1994 ->
                match
                  Obj.magic
                    (let v__target'2646 =
                       Obj.magic
                         v__popFromQueue
                         v_queue'1993
                     in
                     match
                       Obj.magic
                         Obj.magic
                         v__target'2646
                     with
                     | CSome'1620 v__n'2647 ->
                         (match
                            Obj.magic
                              Obj.magic
                              v__n'2647
                          with
                          | CTentativeMid'1727 v__n'2648 ->
                              (let
                                 CRec'2332 ({laddedNodesRightChildren = v_addedNodesRightChildren'2649})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__n'2647
                               in
                               Option.Some (v__n'2647, v_addedNodesRightChildren'2649))
                          | _ ->
                              (Obj.magic
                                 Obj.magic
                                 (Option.None)))
                     | _ ->
                         (Obj.magic
                            Obj.magic
                            (Option.None)))
                with
                | Option.Some (v_parent'1995, v_addedRight'1996) ->
                    (match
                       Obj.magic
                         (let v__target'2650 =
                            Obj.magic
                              (!)
                              v_addedRight'1996
                          in
                          let
                            CRec'2339 ({l0 = v_0'2651;l1 = v_1'2652})
                          =
                            Obj.magic
                              Obj.magic
                              v__target'2650
                          in
                          if
                            Obj.magic
                              ((<) : int -> int -> bool)
                              (Obj.magic
                                 Boot.Intrinsics.Mseq.length
                                 v_1'2652)
                              1
                          then
                            Option.None
                          else
                            Obj.magic
                              Obj.magic
                              (let
                                 (v__prefix'2653, v__splitTemp'2654)
                               =
                                 Obj.magic
                                   Boot.Intrinsics.Mseq.split_at
                                   v_1'2652
                                   1
                               in
                               let
                                 (v__middle'2655, v__postfix'2656)
                               =
                                 Obj.magic
                                   Boot.Intrinsics.Mseq.split_at
                                   v__splitTemp'2654
                                   (Obj.magic
                                      Int.sub
                                      (Obj.magic
                                         Boot.Intrinsics.Mseq.length
                                         v__splitTemp'2654)
                                      0)
                               in
                               let v__seqElem'2657 =
                                 Obj.magic
                                   Boot.Intrinsics.Mseq.get
                                   v__prefix'2653
                                   0
                               in
                               Option.Some (v_1'2652)))
                     with
                     | Option.Some (v_children'1997) ->
                         (let v_acc'1999 =
                            match
                              Obj.magic
                                (let v__target'2658 =
                                   Obj.magic
                                     v_handleLeaf'1991
                                     v_queue'1993
                                     (Obj.magic
                                        v__addRightChildren
                                        v_st'1962
                                        v_parent'1995
                                        v_children'1997)
                                 in
                                 match
                                   Obj.magic
                                     Obj.magic
                                     v__target'2658
                                 with
                                 | CSome'1620 v__n'2659 ->
                                     (Option.Some (v__n'2659))
                                 | _ ->
                                     (Obj.magic
                                        Obj.magic
                                        (Option.None)))
                            with
                            | Option.Some (v_n'1998) ->
                                (Obj.magic
                                   Boot.Intrinsics.Mseq.cons
                                   v_n'1998
                                   v_acc'1994)
                            | Option.None ->
                                (Obj.magic
                                   v_acc'1994)
                          in
                          Obj.magic
                            v_work'1992
                            v_queue'1993
                            v_acc'1999)
                     | Option.None ->
                         (Obj.magic
                            (Obj.magic
                               Boot.Intrinsics.MSys.error
                               (Obj.magic
                                  Boot.Intrinsics.Mseq.Helpers.of_array
                                  [| (83);
                                    (111);
                                    (109);
                                    (101);
                                    (104);
                                    (111);
                                    (119);
                                    (32);
                                    (114);
                                    (101);
                                    (97);
                                    (99);
                                    (104);
                                    (101);
                                    (100);
                                    (32);
                                    (97);
                                    (32);
                                    (112);
                                    (97);
                                    (114);
                                    (101);
                                    (110);
                                    (116);
                                    (32);
                                    (119);
                                    (105);
                                    (116);
                                    (104);
                                    (111);
                                    (117);
                                    (116);
                                    (32);
                                    (114);
                                    (105);
                                    (103);
                                    (104);
                                    (116);
                                    (32);
                                    (99);
                                    (104);
                                    (105);
                                    (108);
                                    (100);
                                    (114);
                                    (101);
                                    (110);
                                    (32);
                                    (116);
                                    (104);
                                    (97);
                                    (116);
                                    (32);
                                    (119);
                                    (97);
                                    (115);
                                    (32);
                                    (115);
                                    (116);
                                    (105);
                                    (108);
                                    (108);
                                    (32);
                                    (97);
                                    (100);
                                    (100);
                                    (101);
                                    (100);
                                    (32);
                                    (116);
                                    (111);
                                    (32);
                                    (116);
                                    (104);
                                    (101);
                                    (32);
                                    (113);
                                    (117);
                                    (101);
                                    (117);
                                    (101) |]))))
                | Option.None ->
                    (Obj.magic
                       v_acc'1994)
        in let v_frontier'2001 =
          let
            CRec'2311 ({lfrontier = v_X'2000})
          =
            Obj.magic
              v_st'1962
          in
          Obj.magic
            v_X'2000
        in
        let v_queue'2002 =
          Obj.magic
            v__newQueueFromFrontier
            v_frontier'2001
        in
        let v_newParents'2003 =
          Obj.magic
            v_mapOption
            (Obj.magic
               v_handleLeaf'1991
               v_queue'2002)
            v_frontier'2001
        in
        let v_newParents'2004 =
          Obj.magic
            v_work'1992
            v_queue'2002
            v_newParents'2003
        in
        match
          Obj.magic
            (let v__target'2660 =
               Obj.magic
                 Boot.Intrinsics.Mseq.map
                 v_makeNewParents'1973
                 v_newParents'2004
             in
             if
               Obj.magic
                 ((<) : int -> int -> bool)
                 (Obj.magic
                    Boot.Intrinsics.Mseq.length
                    v__target'2660)
                 1
             then
               Option.None
             else
               Obj.magic
                 Obj.magic
                 (let
                    (v__prefix'2661, v__splitTemp'2662)
                  =
                    Obj.magic
                      Boot.Intrinsics.Mseq.split_at
                      v__target'2660
                      1
                  in
                  let
                    (v__middle'2663, v__postfix'2664)
                  =
                    Obj.magic
                      Boot.Intrinsics.Mseq.split_at
                      v__splitTemp'2662
                      (Obj.magic
                         Int.sub
                         (Obj.magic
                            Boot.Intrinsics.Mseq.length
                            v__splitTemp'2662)
                         0)
                  in
                  let v__seqElem'2665 =
                    Obj.magic
                      Boot.Intrinsics.Mseq.get
                      v__prefix'2661
                      0
                  in
                  Option.Some (v__target'2660)))
        with
        | Option.Some (v_frontier'2005) ->
            (CSome'1620 (Obj.repr
                (let
                   CRec'2311 v_rec'2666
                 =
                   Obj.magic
                     v_st'1962
                 in
                 CRec'2311 { v_rec'2666
                   with
                   lfrontier =
                     Obj.repr
                       v_frontier'2005 })))
        | Option.None ->
            (Obj.magic
               CNone'1621);;
let v_breakableAddPrefix =
  fun v_input'2007 ->
    fun v_self'2008 ->
      fun v_st'2009 ->
        let v_frontier'2011 =
          let
            CRec'2311 ({lfrontier = v_X'2010})
          =
            Obj.magic
              v_st'2009
          in
          Obj.magic
            v_X'2010
        in
        let v_time'2013 =
          Obj.magic
            (!)
            (let
               CRec'2311 ({ltimestep = v_X'2012})
             =
               Obj.magic
                 v_st'2009
             in
             Obj.magic
               v_X'2012)
        in
        let v_idx'2015 =
          Obj.magic
            (!)
            (let
               CRec'2311 ({lnextIdx = v_X'2014})
             =
               Obj.magic
                 v_st'2009
             in
             Obj.magic
               v_X'2014)
        in
        let v_'2017 =
          Obj.magic
            (:=)
            (let
               CRec'2311 ({lnextIdx = v_X'2016})
             =
               Obj.magic
                 v_st'2009
             in
             Obj.magic
               v_X'2016)
            (Obj.magic
               Int.add
               1
               v_idx'2015)
        in
        let v_addedLeft'2018 =
          Obj.magic
            ref
            (CRec'2339 { l0 =
                 (Obj.repr
                   v__firstTimeStep);
               l1 =
                 (Obj.repr
                   (Obj.magic
                      ref
                      (Obj.magic
                         Boot.Intrinsics.Mseq.Helpers.of_array
                         [|  |]))) })
        in
        let v_addedRight'2019 =
          Obj.magic
            ref
            (CRec'2339 { l0 =
                 (Obj.repr
                   v__firstTimeStep);
               l1 =
                 (Obj.repr
                   (Obj.magic
                      Boot.Intrinsics.Mseq.Helpers.of_array
                      [|  |])) })
        in
        let
          CRec'2311 v_rec'2667
        =
          Obj.magic
            v_st'2009
        in
        CRec'2311 { v_rec'2667
          with
          lfrontier =
            Obj.repr
              (Obj.magic
                 Boot.Intrinsics.Mseq.Helpers.of_array
                 [| (Obj.magic
                     (CTentativeMid'1727 { lparents =
                          (Obj.repr
                            v_frontier'2011);
                        laddedNodesLeftChildren =
                          (Obj.repr
                            v_addedLeft'2018);
                        laddedNodesRightChildren =
                          (Obj.repr
                            v_addedRight'2019);
                        ltentativeData =
                          (Obj.repr
                            (CPrefixT'1723 { lidx =
                                 (Obj.repr
                                   v_idx'2015);
                               linput =
                                 (Obj.repr
                                   v_input'2007);
                               lself =
                                 (Obj.repr
                                   v_self'2008) }));
                        lmaxDistanceFromRoot =
                          (Obj.repr
                            (Obj.magic
                               Int.add
                               1
                               (Obj.magic
                                  v_maxOrElse
                                  (fun v_'2020 ->
                                     0)
                                  Int.sub
                                  (Obj.magic
                                     Boot.Intrinsics.Mseq.map
                                     v__maxDistanceFromRoot
                                     v_frontier'2011)))) })) |]) };;
let v_breakableAddInfix =
  fun v_input'2022 ->
    fun v_self'2023 ->
      fun v_st'2024 ->
        let v_res'2025 =
          Obj.magic
            v__addLOpen
            v_input'2022
            v_self'2023
            v_st'2024
        in
        let v_'2028 =
          Obj.magic
            (:=)
            (let
               CRec'2311 ({lnextIdx = v_X'2026})
             =
               Obj.magic
                 v_st'2024
             in
             Obj.magic
               v_X'2026)
            (Obj.magic
               Int.add
               1
               (Obj.magic
                  (!)
                  (let
                     CRec'2311 ({lnextIdx = v_X'2027})
                   =
                     Obj.magic
                       v_st'2024
                   in
                   Obj.magic
                     v_X'2027)))
        in
        v_res'2025;;
let v_breakableAddPostfix =
  fun v_input'2030 ->
    fun v_self'2031 ->
      fun v_st'2032 ->
        let v_res'2033 =
          Obj.magic
            v__addLOpen
            v_input'2030
            v_self'2031
            v_st'2032
        in
        let v_'2036 =
          Obj.magic
            (:=)
            (let
               CRec'2311 ({lnextIdx = v_X'2034})
             =
               Obj.magic
                 v_st'2032
             in
             Obj.magic
               v_X'2034)
            (Obj.magic
               Int.add
               1
               (Obj.magic
                  (!)
                  (let
                     CRec'2311 ({lnextIdx = v_X'2035})
                   =
                     Obj.magic
                       v_st'2032
                   in
                   Obj.magic
                     v_X'2035)))
        in
        v_res'2033;;
let v_breakableAddAtom =
  fun v_input'2038 ->
    fun v_self'2039 ->
      fun v_st'2040 ->
        let v_idx'2042 =
          Obj.magic
            (!)
            (let
               CRec'2311 ({lnextIdx = v_X'2041})
             =
               Obj.magic
                 v_st'2040
             in
             Obj.magic
               v_X'2041)
        in
        let v_'2044 =
          Obj.magic
            (:=)
            (let
               CRec'2311 ({lnextIdx = v_X'2043})
             =
               Obj.magic
                 v_st'2040
             in
             Obj.magic
               v_X'2043)
            (Obj.magic
               Int.add
               1
               v_idx'2042)
        in
        let v_id'2045 =
          Obj.magic
            v__uniqueID
            ()
        in
        let
          CRec'2311 v_rec'2668
        =
          Obj.magic
            v_st'2040
        in
        CRec'2311 { v_rec'2668
          with
          lfrontier =
            Obj.repr
              (Obj.magic
                 Boot.Intrinsics.Mseq.Helpers.of_array
                 [| (Obj.magic
                     (CTentativeLeaf'1726 { lparents =
                          (Obj.repr
                            (let
                               CRec'2311 ({lfrontier = v_X'2046})
                             =
                               Obj.magic
                                 v_st'2040
                             in
                             Obj.magic
                               v_X'2046));
                        lnode =
                          (Obj.repr
                            (CAtomP'1717 { lid =
                                 (Obj.repr
                                   v_id'2045);
                               lidx =
                                 (Obj.repr
                                   v_idx'2042);
                               linput =
                                 (Obj.repr
                                   v_input'2038);
                               lself =
                                 (Obj.repr
                                   v_self'2039) })) })) |]) };;
let v_breakableFinalizeParse =
  fun v_st'2048 ->
    let v_time'2050 =
      Obj.magic
        Int.add
        1
        (Obj.magic
           (!)
           (let
              CRec'2311 ({ltimestep = v_X'2049})
            =
              Obj.magic
                v_st'2048
            in
            Obj.magic
              v_X'2049))
    in
    let v_'2052 =
      Obj.magic
        (:=)
        (let
           CRec'2311 ({ltimestep = v_X'2051})
         =
           Obj.magic
             v_st'2048
         in
         Obj.magic
           v_X'2051)
        v_time'2050
    in
    let v_handleLeaf'2059 =
      fun v_queue'2053 ->
        fun v_child'2054 ->
          match
            Obj.magic
              (let v__target'2669 =
                 Obj.magic
                   v__getParents
                   v_child'2054
               in
               match
                 Obj.magic
                   Obj.magic
                   v__target'2669
               with
               | CSome'1620 v__n'2670 ->
                   (Option.Some (v__n'2670))
               | _ ->
                   (Obj.magic
                      Obj.magic
                      (Option.None)))
          with
          | Option.Some (v_parents'2055) ->
              (Obj.magic
                 v_for_
                 v_parents'2055
                 (fun v_parent'2056 ->
                    match
                      Obj.magic
                        (let v__target'2671 =
                           Obj.magic
                             v__shallowAllowedRight
                             v_parent'2056
                             v_child'2054
                         in
                         match
                           Obj.magic
                             Obj.magic
                             v__target'2671
                         with
                         | CSome'1620 v__n'2672 ->
                             (Option.Some (v__n'2672))
                         | _ ->
                             (Obj.magic
                                Obj.magic
                                (Option.None)))
                    with
                    | Option.Some (v_child'2057) ->
                        (match
                           Obj.magic
                             (let v__target'2673 =
                                Obj.magic
                                  v__addRightChildToParent
                                  v_time'2050
                                  v_child'2057
                                  v_parent'2056
                              in
                              match
                                Obj.magic
                                  Obj.magic
                                  v__target'2673
                              with
                              | CSome'1620 v__n'2674 ->
                                  (Option.Some (v__n'2674))
                              | _ ->
                                  (Obj.magic
                                     Obj.magic
                                     (Option.None)))
                         with
                         | Option.Some (v_parent'2058) ->
                             (Obj.magic
                                v__addToQueue
                                v_parent'2058
                                v_queue'2053)
                         | Option.None ->
                             (Obj.magic
                                ()))
                    | Option.None ->
                        (Obj.magic
                           ())))
          | Option.None ->
              (Obj.magic
                 (failwith
                    "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 809:13-809:18 ERROR: Reached a never term, which should be impossible in a well-typed program."))
    in
    let rec v_work'2060 =
        fun v_queue'2061 ->
          match
            Obj.magic
              (let v__target'2675 =
                 Obj.magic
                   v__popFromQueue
                   v_queue'2061
               in
               match
                 Obj.magic
                   Obj.magic
                   v__target'2675
               with
               | CSome'1620 v__n'2676 ->
                   (Option.Some (v__n'2676))
               | _ ->
                   (Obj.magic
                      Obj.magic
                      (Option.None)))
          with
          | Option.Some (v_p'2062) ->
              (let v_snd'2065 =
                 fun v_x'2063 ->
                   let
                     CRec'2339 ({l1 = v_X'2064})
                   =
                     Obj.magic
                       v_x'2063
                   in
                   Obj.magic
                     v_X'2064
               in
               let v_children'2066 =
                 Obj.magic
                   v_snd'2065
                   (Obj.magic
                      (!)
                      (Obj.magic
                         v__addedNodesRightChildren
                         v_p'2062))
               in
               let v_defaultCase'2677 =
                 fun nv_ ->
                   match
                     Obj.magic
                       (let v__target'2678 =
                          CRec'2339 { l0 =
                              (Obj.repr
                                v_p'2062);
                            l1 =
                              (Obj.repr
                                v_children'2066) }
                        in
                        let
                          CRec'2339 ({l0 = v_0'2679;l1 = v_1'2680})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2678
                        in
                        match
                          Obj.magic
                            Obj.magic
                            v_0'2679
                        with
                        | CTentativeMid'1727 v__n'2681 ->
                            (if
                               Obj.magic
                                 ((<) : int -> int -> bool)
                                 (Obj.magic
                                    Boot.Intrinsics.Mseq.length
                                    v_1'2680)
                                 1
                             then
                               Option.None
                             else
                               Obj.magic
                                 Obj.magic
                                 (let
                                    (v__prefix'2682, v__splitTemp'2683)
                                  =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.split_at
                                      v_1'2680
                                      1
                                  in
                                  let
                                    (v__middle'2684, v__postfix'2685)
                                  =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.split_at
                                      v__splitTemp'2683
                                      (Obj.magic
                                         Int.sub
                                         (Obj.magic
                                            Boot.Intrinsics.Mseq.length
                                            v__splitTemp'2683)
                                         0)
                                  in
                                  let v__seqElem'2686 =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.get
                                      v__prefix'2682
                                      0
                                  in
                                  Option.Some ()))
                        | _ ->
                            (Obj.magic
                               Obj.magic
                               (Option.None)))
                   with
                   | Option.Some () ->
                       (let v_'2067 =
                          Obj.magic
                            v_handleLeaf'2059
                            v_queue'2061
                            (Obj.magic
                               v__addRightChildren
                               v_st'2048
                               v_p'2062
                               v_children'2066)
                        in
                        Obj.magic
                          v_work'2060
                          v_queue'2061)
                   | Option.None ->
                       (Obj.magic
                          (match
                             Obj.magic
                               (let v__target'2687 =
                                  v_p'2062
                                in
                                match
                                  Obj.magic
                                    Obj.magic
                                    v__target'2687
                                with
                                | CTentativeMid'1727 v__n'2688 ->
                                    (Option.Some ())
                                | _ ->
                                    (Obj.magic
                                       Obj.magic
                                       (Option.None)))
                           with
                           | Option.Some () ->
                               (Obj.magic
                                  Boot.Intrinsics.MSys.error
                                  (Obj.magic
                                     Boot.Intrinsics.Mseq.Helpers.of_array
                                     [| (83);
                                       (111);
                                       (109);
                                       (101);
                                       (104);
                                       (111);
                                       (119);
                                       (32);
                                       (114);
                                       (101);
                                       (97);
                                       (99);
                                       (104);
                                       (101);
                                       (100);
                                       (32);
                                       (97);
                                       (32);
                                       (84);
                                       (101);
                                       (110);
                                       (116);
                                       (97);
                                       (116);
                                       (105);
                                       (118);
                                       (101);
                                       (77);
                                       (105);
                                       (100);
                                       (32);
                                       (119);
                                       (105);
                                       (116);
                                       (104);
                                       (111);
                                       (117);
                                       (116);
                                       (32);
                                       (114);
                                       (105);
                                       (103);
                                       (104);
                                       (116);
                                       (32);
                                       (99);
                                       (104);
                                       (105);
                                       (108);
                                       (100);
                                       (114);
                                       (101);
                                       (110);
                                       (44);
                                       (32);
                                       (116);
                                       (104);
                                       (97);
                                       (116);
                                       (32);
                                       (119);
                                       (97);
                                       (115);
                                       (32);
                                       (115);
                                       (116);
                                       (105);
                                       (108);
                                       (108);
                                       (32);
                                       (97);
                                       (100);
                                       (100);
                                       (101);
                                       (100);
                                       (32);
                                       (116);
                                       (111);
                                       (32);
                                       (116);
                                       (104);
                                       (101);
                                       (32);
                                       (113);
                                       (117);
                                       (101);
                                       (117);
                                       (101) |]))
                           | Option.None ->
                               (Obj.magic
                                  (failwith
                                     "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 825:15-825:20 ERROR: Reached a never term, which should be impossible in a well-typed program."))))
               in
               match
                 Obj.magic
                   v_p'2062
               with
               | CTentativeRoot'1728 v_x'2689 ->
                   v_children'2066
               | _ ->
                   (Obj.magic
                      (v_defaultCase'2677
                         ())))
          | Option.None ->
              (Obj.magic
                 (Obj.magic
                    Boot.Intrinsics.Mseq.Helpers.of_array
                    [|  |]))
    in let v_frontier'2069 =
      let
        CRec'2311 ({lfrontier = v_X'2068})
      =
        Obj.magic
          v_st'2048
      in
      Obj.magic
        v_X'2068
    in
    let v_queue'2070 =
      Obj.magic
        v__newQueueFromFrontier
        v_frontier'2069
    in
    let v_'2071 =
      Obj.magic
        Boot.Intrinsics.Mseq.iter
        (Obj.magic
           v_handleLeaf'2059
           v_queue'2070)
        v_frontier'2069
    in
    match
      Obj.magic
        (let v__target'2690 =
           Obj.magic
             v_work'2060
             v_queue'2070
         in
         if
           Obj.magic
             ((<) : int -> int -> bool)
             (Obj.magic
                Boot.Intrinsics.Mseq.length
                v__target'2690)
             1
         then
           Option.None
         else
           Obj.magic
             Obj.magic
             (let
                (v__prefix'2691, v__splitTemp'2692)
              =
                Obj.magic
                  Boot.Intrinsics.Mseq.split_at
                  v__target'2690
                  1
              in
              let
                (v__middle'2693, v__postfix'2694)
              =
                Obj.magic
                  Boot.Intrinsics.Mseq.split_at
                  v__splitTemp'2692
                  (Obj.magic
                     Int.sub
                     (Obj.magic
                        Boot.Intrinsics.Mseq.length
                        v__splitTemp'2692)
                     0)
              in
              let v__seqElem'2695 =
                Obj.magic
                  Boot.Intrinsics.Mseq.get
                  v__prefix'2691
                  0
              in
              Option.Some (v__target'2690)))
    with
    | Option.Some (v_res'2072) ->
        (CSome'1620 (Obj.repr
            v_res'2072))
    | Option.None ->
        (Obj.magic
           CNone'1621);;
let v_breakableConstructResult =
  fun v_selfToTok'2077 ->
    fun v_lpar'2078 ->
      fun v_rpar'2079 ->
        fun v_parInput'2080 ->
          fun v_nodes'2081 ->
            let v_parId'2082 =
              Obj.magic
                v__opIdI
                v_parInput'2080
            in
            let rec v_range'2083 =
                fun v_node'2084 ->
                  let v_defaultCase'2696 =
                    fun nv_ ->
                      failwith
                        "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 870:13-870:18 ERROR: Reached a never term, which should be impossible in a well-typed program."
                  in
                  match
                    Obj.magic
                      v_node'2084
                  with
                  | CAtomP'1717 v_x'2697 ->
                      (match
                         Obj.magic
                           (let v__target'2698 =
                              Obj.magic
                                Obj.magic
                                v_node'2084
                            in
                            let
                              CRec'2333 ({lself = v_self'2699})
                            =
                              Obj.magic
                                Obj.magic
                                v__target'2698
                            in
                            Option.Some (v_self'2699))
                       with
                       | Option.Some (v_self'2085) ->
                           (CRec'2336 { lfirst =
                                (Obj.repr
                                  v_self'2085);
                              llast =
                                (Obj.repr
                                  v_self'2085) })
                       | Option.None ->
                           (Obj.magic
                              (Obj.magic
                                 v_defaultCase'2696
                                 ())))
                  | CInfixP'1718 v_x'2700 ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2701 =
                                 Obj.magic
                                   Obj.magic
                                   v_node'2084
                               in
                               let
                                 CRec'2303 ({lleftChildAlts = v_leftChildAlts'2702;lrightChildAlts = v_rightChildAlts'2703})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2701
                               in
                               if
                                 Obj.magic
                                   ((<) : int -> int -> bool)
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.length
                                      v_leftChildAlts'2702)
                                   1
                               then
                                 Option.None
                               else
                                 Obj.magic
                                   Obj.magic
                                   (let
                                      (v__prefix'2704, v__splitTemp'2705)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v_leftChildAlts'2702
                                        1
                                    in
                                    let
                                      (v__middle'2706, v__postfix'2707)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v__splitTemp'2705
                                        (Obj.magic
                                           Int.sub
                                           (Obj.magic
                                              Boot.Intrinsics.Mseq.length
                                              v__splitTemp'2705)
                                           0)
                                    in
                                    let v__seqElem'2708 =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.get
                                        v__prefix'2704
                                        0
                                    in
                                    if
                                      Obj.magic
                                        ((<) : int -> int -> bool)
                                        (Obj.magic
                                           Boot.Intrinsics.Mseq.length
                                           v_rightChildAlts'2703)
                                        1
                                    then
                                      Option.None
                                    else
                                      Obj.magic
                                        Obj.magic
                                        (let
                                           (v__prefix'2709, v__splitTemp'2710)
                                         =
                                           Obj.magic
                                             Boot.Intrinsics.Mseq.split_at
                                             v_rightChildAlts'2703
                                             1
                                         in
                                         let
                                           (v__middle'2711, v__postfix'2712)
                                         =
                                           Obj.magic
                                             Boot.Intrinsics.Mseq.split_at
                                             v__splitTemp'2710
                                             (Obj.magic
                                                Int.sub
                                                (Obj.magic
                                                   Boot.Intrinsics.Mseq.length
                                                   v__splitTemp'2710)
                                                0)
                                         in
                                         let v__seqElem'2713 =
                                           Obj.magic
                                             Boot.Intrinsics.Mseq.get
                                             v__prefix'2709
                                             0
                                         in
                                         Option.Some (v__seqElem'2708, v__seqElem'2713))))
                          with
                          | Option.Some (v_l'2086, v_r'2087) ->
                              (CRec'2336 { lfirst =
                                   (Obj.repr
                                     (let
                                        CRec'2336 ({lfirst = v_X'2088})
                                      =
                                        Obj.magic
                                          (Obj.magic
                                             v_range'2083
                                             v_l'2086)
                                      in
                                      Obj.magic
                                        v_X'2088));
                                 llast =
                                   (Obj.repr
                                     (let
                                        CRec'2336 ({llast = v_X'2089})
                                      =
                                        Obj.magic
                                          (Obj.magic
                                             v_range'2083
                                             v_r'2087)
                                      in
                                      Obj.magic
                                        v_X'2089)) })
                          | Option.None ->
                              (Obj.magic
                                 (Obj.magic
                                    v_defaultCase'2696
                                    ()))))
                  | CPrefixP'1719 v_x'2714 ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2715 =
                                 Obj.magic
                                   Obj.magic
                                   v_node'2084
                               in
                               let
                                 CRec'2304 ({lself = v_self'2716;lrightChildAlts = v_rightChildAlts'2717})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2715
                               in
                               if
                                 Obj.magic
                                   ((<) : int -> int -> bool)
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.length
                                      v_rightChildAlts'2717)
                                   1
                               then
                                 Option.None
                               else
                                 Obj.magic
                                   Obj.magic
                                   (let
                                      (v__prefix'2718, v__splitTemp'2719)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v_rightChildAlts'2717
                                        1
                                    in
                                    let
                                      (v__middle'2720, v__postfix'2721)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v__splitTemp'2719
                                        (Obj.magic
                                           Int.sub
                                           (Obj.magic
                                              Boot.Intrinsics.Mseq.length
                                              v__splitTemp'2719)
                                           0)
                                    in
                                    let v__seqElem'2722 =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.get
                                        v__prefix'2718
                                        0
                                    in
                                    Option.Some (v_self'2716, v__seqElem'2722)))
                          with
                          | Option.Some (v_self'2090, v_r'2091) ->
                              (CRec'2336 { lfirst =
                                   (Obj.repr
                                     v_self'2090);
                                 llast =
                                   (Obj.repr
                                     (let
                                        CRec'2336 ({llast = v_X'2092})
                                      =
                                        Obj.magic
                                          (Obj.magic
                                             v_range'2083
                                             v_r'2091)
                                      in
                                      Obj.magic
                                        v_X'2092)) })
                          | Option.None ->
                              (Obj.magic
                                 (Obj.magic
                                    v_defaultCase'2696
                                    ()))))
                  | CPostfixP'1720 v_x'2723 ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2724 =
                                 Obj.magic
                                   Obj.magic
                                   v_node'2084
                               in
                               let
                                 CRec'2325 ({lself = v_self'2725;lleftChildAlts = v_leftChildAlts'2726})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2724
                               in
                               if
                                 Obj.magic
                                   ((<) : int -> int -> bool)
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.length
                                      v_leftChildAlts'2726)
                                   1
                               then
                                 Option.None
                               else
                                 Obj.magic
                                   Obj.magic
                                   (let
                                      (v__prefix'2727, v__splitTemp'2728)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v_leftChildAlts'2726
                                        1
                                    in
                                    let
                                      (v__middle'2729, v__postfix'2730)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v__splitTemp'2728
                                        (Obj.magic
                                           Int.sub
                                           (Obj.magic
                                              Boot.Intrinsics.Mseq.length
                                              v__splitTemp'2728)
                                           0)
                                    in
                                    let v__seqElem'2731 =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.get
                                        v__prefix'2727
                                        0
                                    in
                                    Option.Some (v_self'2725, v__seqElem'2731)))
                          with
                          | Option.Some (v_self'2093, v_l'2094) ->
                              (CRec'2336 { lfirst =
                                   (Obj.repr
                                     (let
                                        CRec'2336 ({lfirst = v_X'2095})
                                      =
                                        Obj.magic
                                          (Obj.magic
                                             v_range'2083
                                             v_l'2094)
                                      in
                                      Obj.magic
                                        v_X'2095));
                                 llast =
                                   (Obj.repr
                                     v_self'2093) })
                          | Option.None ->
                              (Obj.magic
                                 (Obj.magic
                                    v_defaultCase'2696
                                    ()))))
                  | _ ->
                      (Obj.magic
                         (v_defaultCase'2696
                            ()))
            in let rec v_flattenOne'2096 =
                fun v_node'2098 ->
                  let v_X'2099 =
                    v_node'2098
                  in
                  let v_defaultCase'2732 =
                    fun nv_ ->
                      failwith
                        "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 883:8-883:11 ERROR: Reached a never term, which should be impossible in a well-typed program."
                  in
                  match
                    Obj.magic
                      v_X'2099
                  with
                  | CAtomP'1717 v_x'2733 ->
                      (match
                         Obj.magic
                           (let v__target'2734 =
                              Obj.magic
                                Obj.magic
                                v_X'2099
                            in
                            let
                              CRec'2333 ({lself = v_self'2735})
                            =
                              Obj.magic
                                Obj.magic
                                v__target'2734
                            in
                            Option.Some (v_self'2735))
                       with
                       | Option.Some (v_self'2100) ->
                           (Obj.magic
                              Boot.Intrinsics.Mseq.Helpers.of_array
                              [| (Obj.magic
                                  (Obj.magic
                                     v_selfToTok'2077
                                     v_self'2100)) |])
                       | Option.None ->
                           (Obj.magic
                              (Obj.magic
                                 v_defaultCase'2732
                                 ())))
                  | CInfixP'1718 v_x'2736 ->
                      (Obj.magic
                         (let v_p'2101 =
                            Obj.magic
                              Obj.magic
                              v_X'2099
                          in
                          Obj.magic
                            v_join
                            (Obj.magic
                               Boot.Intrinsics.Mseq.Helpers.of_array
                               [| (Obj.magic
                                   (Obj.magic
                                      v_flattenMany'2097
                                      (let
                                         CRec'2303 ({lleftChildAlts = v_X'2102})
                                       =
                                         Obj.magic
                                           v_p'2101
                                       in
                                       Obj.magic
                                         v_X'2102)));
                                 (Obj.magic
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.Helpers.of_array
                                      [| (Obj.magic
                                          (Obj.magic
                                             v_selfToTok'2077
                                             (let
                                                CRec'2303 ({lself = v_X'2103})
                                              =
                                                Obj.magic
                                                  v_p'2101
                                              in
                                              Obj.magic
                                                v_X'2103))) |]));
                                 (Obj.magic
                                   (Obj.magic
                                      v_flattenMany'2097
                                      (let
                                         CRec'2303 ({lrightChildAlts = v_X'2104})
                                       =
                                         Obj.magic
                                           v_p'2101
                                       in
                                       Obj.magic
                                         v_X'2104))) |])))
                  | CPrefixP'1719 v_x'2737 ->
                      (Obj.magic
                         (let v_p'2105 =
                            Obj.magic
                              Obj.magic
                              v_X'2099
                          in
                          Obj.magic
                            Boot.Intrinsics.Mseq.cons
                            (Obj.magic
                               v_selfToTok'2077
                               (let
                                  CRec'2304 ({lself = v_X'2106})
                                =
                                  Obj.magic
                                    v_p'2105
                                in
                                Obj.magic
                                  v_X'2106))
                            (Obj.magic
                               v_flattenMany'2097
                               (let
                                  CRec'2304 ({lrightChildAlts = v_X'2107})
                                =
                                  Obj.magic
                                    v_p'2105
                                in
                                Obj.magic
                                  v_X'2107))))
                  | CPostfixP'1720 v_x'2738 ->
                      (Obj.magic
                         (let v_p'2108 =
                            Obj.magic
                              Obj.magic
                              v_X'2099
                          in
                          Obj.magic
                            Boot.Intrinsics.Mseq.snoc
                            (Obj.magic
                               v_flattenMany'2097
                               (let
                                  CRec'2325 ({lleftChildAlts = v_X'2109})
                                =
                                  Obj.magic
                                    v_p'2108
                                in
                                Obj.magic
                                  v_X'2109))
                            (Obj.magic
                               v_selfToTok'2077
                               (let
                                  CRec'2325 ({lself = v_X'2110})
                                =
                                  Obj.magic
                                    v_p'2108
                                in
                                Obj.magic
                                  v_X'2110))))
                  | _ ->
                      (Obj.magic
                         (v_defaultCase'2732
                            ()))
            and v_flattenMany'2097 =
                fun v_nodes'2111 ->
                  match
                    Obj.magic
                      (let v__target'2739 =
                         v_nodes'2111
                       in
                       if
                         Obj.magic
                           ((<) : int -> int -> bool)
                           (Obj.magic
                              Boot.Intrinsics.Mseq.length
                              v__target'2739)
                           1
                       then
                         Option.None
                       else
                         Obj.magic
                           Obj.magic
                           (let
                              (v__prefix'2740, v__splitTemp'2741)
                            =
                              Obj.magic
                                Boot.Intrinsics.Mseq.split_at
                                v__target'2739
                                1
                            in
                            let
                              (v__middle'2742, v__postfix'2743)
                            =
                              Obj.magic
                                Boot.Intrinsics.Mseq.split_at
                                v__splitTemp'2741
                                (Obj.magic
                                   Int.sub
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.length
                                      v__splitTemp'2741)
                                   0)
                            in
                            let v__seqElem'2744 =
                              Obj.magic
                                Boot.Intrinsics.Mseq.get
                                v__prefix'2740
                                0
                            in
                            Option.Some (v__seqElem'2744)))
                  with
                  | Option.Some (v_n'2112) ->
                      (Obj.magic
                         v_flattenOne'2096
                         v_n'2112)
                  | Option.None ->
                      (Obj.magic
                         (failwith
                            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 887:13-887:18 ERROR: Reached a never term, which should be impossible in a well-typed program."))
            in let v_resolveWith'2118 =
              fun v_tops'2113 ->
                fun v_allowSet'2114 ->
                  fun v_children'2115 ->
                    fun v_resolveDir'2116 ->
                      let v_needToWrap'2117 =
                        Obj.magic
                          v_not
                          (Obj.magic
                             Boot.Intrinsics.Mseq.null
                             v_tops'2113)
                      in
                      if
                        Obj.magic
                          v_needToWrap'2117
                      then
                        if
                          Obj.magic
                            (Obj.magic
                               v_breakableInAllowSet
                               v_parId'2082
                               v_allowSet'2114)
                        then
                          Obj.magic
                            Boot.Intrinsics.Mseq.Helpers.of_array
                            [| (Obj.magic
                                (Obj.magic
                                   Boot.Intrinsics.Mseq.cons
                                   v_lpar'2078
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.snoc
                                      (Obj.magic
                                         v_flattenMany'2097
                                         v_children'2115)
                                      v_rpar'2079))) |]
                        else
                          Obj.magic
                            (Obj.magic
                               v_join
                               (Obj.magic
                                  Boot.Intrinsics.Mseq.map
                                  (Obj.magic
                                     v_resolveDir'2116
                                     v_tops'2113)
                                  v_children'2115))
                      else
                        Obj.magic
                          (Obj.magic
                             Boot.Intrinsics.Mseq.Helpers.of_array
                             [| (Obj.magic
                                 (Obj.magic
                                    v_flattenMany'2097
                                    v_children'2115)) |])
            in
            let rec v_resolveDir'2119 =
                fun v_forceLeft'2120 ->
                  fun v_forceRight'2121 ->
                    fun v_tops'2122 ->
                      fun v_node'2123 ->
                        let v_X'2124 =
                          v_node'2123
                        in
                        let v_defaultCase'2745 =
                          fun nv_ ->
                            failwith
                              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 949:8-949:11 ERROR: Reached a never term, which should be impossible in a well-typed program."
                        in
                        match
                          Obj.magic
                            v_X'2124
                        with
                        | CAtomP'1717 v_x'2746 ->
                            (match
                               Obj.magic
                                 (let v__target'2747 =
                                    Obj.magic
                                      Obj.magic
                                      v_X'2124
                                  in
                                  let
                                    CRec'2333 ({lself = v_self'2748})
                                  =
                                    Obj.magic
                                      Obj.magic
                                      v__target'2747
                                  in
                                  Option.Some (v_self'2748))
                             with
                             | Option.Some (v_self'2125) ->
                                 (Obj.magic
                                    Boot.Intrinsics.Mseq.Helpers.of_array
                                    [| (Obj.magic
                                        (Obj.magic
                                           Boot.Intrinsics.Mseq.Helpers.of_array
                                           [| (Obj.magic
                                               (Obj.magic
                                                  v_selfToTok'2077
                                                  v_self'2125)) |])) |])
                             | Option.None ->
                                 (Obj.magic
                                    (Obj.magic
                                       v_defaultCase'2745
                                       ())))
                        | CInfixP'1718 v_x'2749 ->
                            (Obj.magic
                               (match
                                  Obj.magic
                                    (let v__target'2750 =
                                       Obj.magic
                                         Obj.magic
                                         v_X'2124
                                     in
                                     let
                                       CRec'2303 ({linput = v_input'2751})
                                     =
                                       Obj.magic
                                         Obj.magic
                                         v__target'2750
                                     in
                                     match
                                       Obj.magic
                                         Obj.magic
                                         v_input'2751
                                     with
                                     | CInfixI'1712 v__n'2752 ->
                                         (Option.Some (v__target'2750, v_input'2751))
                                     | _ ->
                                         (Obj.magic
                                            Obj.magic
                                            (Option.None)))
                                with
                                | Option.Some (v_node'2126, v_i'2127) ->
                                    (let v_left'2133 =
                                       if
                                         Obj.magic
                                           v_forceLeft'2120
                                       then
                                         Obj.magic
                                           Boot.Intrinsics.Mseq.Helpers.of_array
                                           [| (Obj.magic
                                               (Obj.magic
                                                  Boot.Intrinsics.Mseq.cons
                                                  v_lpar'2078
                                                  (Obj.magic
                                                     Boot.Intrinsics.Mseq.snoc
                                                     (Obj.magic
                                                        v_flattenMany'2097
                                                        (let
                                                           CRec'2303 ({lleftChildAlts = v_X'2128})
                                                         =
                                                           Obj.magic
                                                             v_node'2126
                                                         in
                                                         Obj.magic
                                                           v_X'2128))
                                                     v_rpar'2079))) |]
                                       else
                                         Obj.magic
                                           (let v_tops'2130 =
                                              Obj.magic
                                                v_filter
                                                (Obj.magic
                                                   ((>) : int -> int -> bool)
                                                   (let
                                                      CRec'2303 ({lidx = v_X'2129})
                                                    =
                                                      Obj.magic
                                                        v_node'2126
                                                    in
                                                    Obj.magic
                                                      v_X'2129))
                                                v_tops'2122
                                            in
                                            Obj.magic
                                              v_resolveWith'2118
                                              v_tops'2130
                                              (let
                                                 CRec'2317 ({lleftAllow = v_X'2131})
                                               =
                                                 Obj.magic
                                                   v_i'2127
                                               in
                                               Obj.magic
                                                 v_X'2131)
                                              (let
                                                 CRec'2303 ({lleftChildAlts = v_X'2132})
                                               =
                                                 Obj.magic
                                                   v_node'2126
                                               in
                                               Obj.magic
                                                 v_X'2132)
                                              (Obj.magic
                                                 v_resolveDir'2119
                                                 false
                                                 true))
                                     in
                                     let v_right'2139 =
                                       if
                                         Obj.magic
                                           v_forceRight'2121
                                       then
                                         Obj.magic
                                           Boot.Intrinsics.Mseq.Helpers.of_array
                                           [| (Obj.magic
                                               (Obj.magic
                                                  Boot.Intrinsics.Mseq.cons
                                                  v_lpar'2078
                                                  (Obj.magic
                                                     Boot.Intrinsics.Mseq.snoc
                                                     (Obj.magic
                                                        v_flattenMany'2097
                                                        (let
                                                           CRec'2303 ({lrightChildAlts = v_X'2134})
                                                         =
                                                           Obj.magic
                                                             v_node'2126
                                                         in
                                                         Obj.magic
                                                           v_X'2134))
                                                     v_rpar'2079))) |]
                                       else
                                         Obj.magic
                                           (let v_tops'2136 =
                                              Obj.magic
                                                v_filter
                                                (Obj.magic
                                                   ((<) : int -> int -> bool)
                                                   (let
                                                      CRec'2303 ({lidx = v_X'2135})
                                                    =
                                                      Obj.magic
                                                        v_node'2126
                                                    in
                                                    Obj.magic
                                                      v_X'2135))
                                                v_tops'2122
                                            in
                                            Obj.magic
                                              v_resolveWith'2118
                                              v_tops'2136
                                              (let
                                                 CRec'2317 ({lrightAllow = v_X'2137})
                                               =
                                                 Obj.magic
                                                   v_i'2127
                                               in
                                               Obj.magic
                                                 v_X'2137)
                                              (let
                                                 CRec'2303 ({lrightChildAlts = v_X'2138})
                                               =
                                                 Obj.magic
                                                   v_node'2126
                                               in
                                               Obj.magic
                                                 v_X'2138)
                                              (Obj.magic
                                                 v_resolveDir'2119
                                                 true
                                                 false))
                                     in
                                     let v_here'2141 =
                                       Obj.magic
                                         Boot.Intrinsics.Mseq.Helpers.of_array
                                         [| (Obj.magic
                                             (Obj.magic
                                                v_selfToTok'2077
                                                (let
                                                   CRec'2303 ({lself = v_X'2140})
                                                 =
                                                   Obj.magic
                                                     v_node'2126
                                                 in
                                                 Obj.magic
                                                   v_X'2140))) |]
                                     in
                                     Obj.magic
                                       v_seqLiftA2
                                       (fun v_l'2142 ->
                                          fun v_r'2143 ->
                                            Obj.magic
                                              v_join
                                              (Obj.magic
                                                 Boot.Intrinsics.Mseq.Helpers.of_array
                                                 [| (Obj.magic
                                                     v_l'2142);
                                                   (Obj.magic
                                                     v_here'2141);
                                                   (Obj.magic
                                                     v_r'2143) |]))
                                       v_left'2133
                                       v_right'2139)
                                | Option.None ->
                                    (Obj.magic
                                       (Obj.magic
                                          v_defaultCase'2745
                                          ()))))
                        | CPrefixP'1719 v_x'2753 ->
                            (Obj.magic
                               (match
                                  Obj.magic
                                    (let v__target'2754 =
                                       Obj.magic
                                         Obj.magic
                                         v_X'2124
                                     in
                                     let
                                       CRec'2304 ({linput = v_input'2755})
                                     =
                                       Obj.magic
                                         Obj.magic
                                         v__target'2754
                                     in
                                     match
                                       Obj.magic
                                         Obj.magic
                                         v_input'2755
                                     with
                                     | CPrefixI'1713 v__n'2756 ->
                                         (Option.Some (v__target'2754, v_input'2755))
                                     | _ ->
                                         (Obj.magic
                                            Obj.magic
                                            (Option.None)))
                                with
                                | Option.Some (v_node'2144, v_i'2145) ->
                                    (let v_left'2146 =
                                       Obj.magic
                                         Boot.Intrinsics.Mseq.Helpers.of_array
                                         [| (Obj.magic
                                             (Obj.magic
                                                Boot.Intrinsics.Mseq.Helpers.of_array
                                                [|  |])) |]
                                     in
                                     let v_right'2152 =
                                       if
                                         Obj.magic
                                           v_forceRight'2121
                                       then
                                         Obj.magic
                                           Boot.Intrinsics.Mseq.Helpers.of_array
                                           [| (Obj.magic
                                               (Obj.magic
                                                  Boot.Intrinsics.Mseq.cons
                                                  v_lpar'2078
                                                  (Obj.magic
                                                     Boot.Intrinsics.Mseq.snoc
                                                     (Obj.magic
                                                        v_flattenMany'2097
                                                        (let
                                                           CRec'2304 ({lrightChildAlts = v_X'2147})
                                                         =
                                                           Obj.magic
                                                             v_node'2144
                                                         in
                                                         Obj.magic
                                                           v_X'2147))
                                                     v_rpar'2079))) |]
                                       else
                                         Obj.magic
                                           (let v_tops'2149 =
                                              Obj.magic
                                                v_filter
                                                (Obj.magic
                                                   ((<) : int -> int -> bool)
                                                   (let
                                                      CRec'2304 ({lidx = v_X'2148})
                                                    =
                                                      Obj.magic
                                                        v_node'2144
                                                    in
                                                    Obj.magic
                                                      v_X'2148))
                                                v_tops'2122
                                            in
                                            Obj.magic
                                              v_resolveWith'2118
                                              v_tops'2149
                                              (let
                                                 CRec'2316 ({lrightAllow = v_X'2150})
                                               =
                                                 Obj.magic
                                                   v_i'2145
                                               in
                                               Obj.magic
                                                 v_X'2150)
                                              (let
                                                 CRec'2304 ({lrightChildAlts = v_X'2151})
                                               =
                                                 Obj.magic
                                                   v_node'2144
                                               in
                                               Obj.magic
                                                 v_X'2151)
                                              (Obj.magic
                                                 v_resolveDir'2119
                                                 true
                                                 false))
                                     in
                                     let v_here'2154 =
                                       Obj.magic
                                         Boot.Intrinsics.Mseq.Helpers.of_array
                                         [| (Obj.magic
                                             (Obj.magic
                                                v_selfToTok'2077
                                                (let
                                                   CRec'2304 ({lself = v_X'2153})
                                                 =
                                                   Obj.magic
                                                     v_node'2144
                                                 in
                                                 Obj.magic
                                                   v_X'2153))) |]
                                     in
                                     Obj.magic
                                       v_seqLiftA2
                                       (fun v_l'2155 ->
                                          fun v_r'2156 ->
                                            Obj.magic
                                              v_join
                                              (Obj.magic
                                                 Boot.Intrinsics.Mseq.Helpers.of_array
                                                 [| (Obj.magic
                                                     v_l'2155);
                                                   (Obj.magic
                                                     v_here'2154);
                                                   (Obj.magic
                                                     v_r'2156) |]))
                                       v_left'2146
                                       v_right'2152)
                                | Option.None ->
                                    (Obj.magic
                                       (Obj.magic
                                          v_defaultCase'2745
                                          ()))))
                        | CPostfixP'1720 v_x'2757 ->
                            (Obj.magic
                               (match
                                  Obj.magic
                                    (let v__target'2758 =
                                       Obj.magic
                                         Obj.magic
                                         v_X'2124
                                     in
                                     let
                                       CRec'2325 ({linput = v_input'2759})
                                     =
                                       Obj.magic
                                         Obj.magic
                                         v__target'2758
                                     in
                                     match
                                       Obj.magic
                                         Obj.magic
                                         v_input'2759
                                     with
                                     | CPostfixI'1714 v__n'2760 ->
                                         (Option.Some (v__target'2758, v_input'2759))
                                     | _ ->
                                         (Obj.magic
                                            Obj.magic
                                            (Option.None)))
                                with
                                | Option.Some (v_node'2157, v_i'2158) ->
                                    (let v_left'2164 =
                                       if
                                         Obj.magic
                                           v_forceLeft'2120
                                       then
                                         Obj.magic
                                           Boot.Intrinsics.Mseq.Helpers.of_array
                                           [| (Obj.magic
                                               (Obj.magic
                                                  Boot.Intrinsics.Mseq.cons
                                                  v_lpar'2078
                                                  (Obj.magic
                                                     Boot.Intrinsics.Mseq.snoc
                                                     (Obj.magic
                                                        v_flattenMany'2097
                                                        (let
                                                           CRec'2325 ({lleftChildAlts = v_X'2159})
                                                         =
                                                           Obj.magic
                                                             v_node'2157
                                                         in
                                                         Obj.magic
                                                           v_X'2159))
                                                     v_rpar'2079))) |]
                                       else
                                         Obj.magic
                                           (let v_tops'2161 =
                                              Obj.magic
                                                v_filter
                                                (Obj.magic
                                                   ((>) : int -> int -> bool)
                                                   (let
                                                      CRec'2325 ({lidx = v_X'2160})
                                                    =
                                                      Obj.magic
                                                        v_node'2157
                                                    in
                                                    Obj.magic
                                                      v_X'2160))
                                                v_tops'2122
                                            in
                                            Obj.magic
                                              v_resolveWith'2118
                                              v_tops'2161
                                              (let
                                                 CRec'2318 ({lleftAllow = v_X'2162})
                                               =
                                                 Obj.magic
                                                   v_i'2158
                                               in
                                               Obj.magic
                                                 v_X'2162)
                                              (let
                                                 CRec'2325 ({lleftChildAlts = v_X'2163})
                                               =
                                                 Obj.magic
                                                   v_node'2157
                                               in
                                               Obj.magic
                                                 v_X'2163)
                                              (Obj.magic
                                                 v_resolveDir'2119
                                                 false
                                                 true))
                                     in
                                     let v_right'2165 =
                                       Obj.magic
                                         Boot.Intrinsics.Mseq.Helpers.of_array
                                         [| (Obj.magic
                                             (Obj.magic
                                                Boot.Intrinsics.Mseq.Helpers.of_array
                                                [|  |])) |]
                                     in
                                     let v_here'2167 =
                                       Obj.magic
                                         Boot.Intrinsics.Mseq.Helpers.of_array
                                         [| (Obj.magic
                                             (Obj.magic
                                                v_selfToTok'2077
                                                (let
                                                   CRec'2325 ({lself = v_X'2166})
                                                 =
                                                   Obj.magic
                                                     v_node'2157
                                                 in
                                                 Obj.magic
                                                   v_X'2166))) |]
                                     in
                                     Obj.magic
                                       v_seqLiftA2
                                       (fun v_l'2168 ->
                                          fun v_r'2169 ->
                                            Obj.magic
                                              v_join
                                              (Obj.magic
                                                 Boot.Intrinsics.Mseq.Helpers.of_array
                                                 [| (Obj.magic
                                                     v_l'2168);
                                                   (Obj.magic
                                                     v_here'2167);
                                                   (Obj.magic
                                                     v_r'2169) |]))
                                       v_left'2164
                                       v_right'2165)
                                | Option.None ->
                                    (Obj.magic
                                       (Obj.magic
                                          v_defaultCase'2745
                                          ()))))
                        | _ ->
                            (Obj.magic
                               (v_defaultCase'2745
                                  ()))
            in let v_ambiguities'2170 =
              Obj.magic
                ref
                (Obj.magic
                   Boot.Intrinsics.Mseq.Helpers.of_array
                   [|  |])
            in
            let rec v_workMany'2171 =
                fun v_tops'2173 ->
                  match
                    Obj.magic
                      (let v__target'2761 =
                         v_tops'2173
                       in
                       if
                         Obj.magic
                           Int.equal
                           (Obj.magic
                              Boot.Intrinsics.Mseq.length
                              v__target'2761)
                           1
                       then
                         let v__seqElem'2762 =
                           Obj.magic
                             Boot.Intrinsics.Mseq.get
                             v__target'2761
                             0
                         in
                         Option.Some (v__seqElem'2762)
                       else
                         Obj.magic
                           Obj.magic
                           (Option.None))
                  with
                  | Option.Some (v_n'2174) ->
                      (Obj.magic
                         v_workOne'2172
                         v_n'2174)
                  | Option.None ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2763 =
                                 v_tops'2173
                               in
                               if
                                 Obj.magic
                                   ((<) : int -> int -> bool)
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.length
                                      v__target'2763)
                                   1
                               then
                                 Option.None
                               else
                                 Obj.magic
                                   Obj.magic
                                   (let
                                      (v__prefix'2764, v__splitTemp'2765)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v__target'2763
                                        1
                                    in
                                    let
                                      (v__middle'2766, v__postfix'2767)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v__splitTemp'2765
                                        (Obj.magic
                                           Int.sub
                                           (Obj.magic
                                              Boot.Intrinsics.Mseq.length
                                              v__splitTemp'2765)
                                           0)
                                    in
                                    let v__seqElem'2768 =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.get
                                        v__prefix'2764
                                        0
                                    in
                                    Option.Some (v__seqElem'2768)))
                          with
                          | Option.Some (v_n'2175) ->
                              (let v_topIdxs'2176 =
                                 Obj.magic
                                   Boot.Intrinsics.Mseq.map
                                   v__opIdxP
                                   v_tops'2173
                               in
                               let v_range'2177 =
                                 Obj.magic
                                   v_range'2083
                                   v_n'2175
                               in
                               let v_resolutions'2178 =
                                 Obj.magic
                                   v_join
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.map
                                      (Obj.magic
                                         v_resolveDir'2119
                                         false
                                         false
                                         v_topIdxs'2176)
                                      v_tops'2173)
                               in
                               let v_err'2181 =
                                 CRec'2337 { lfirst =
                                     (Obj.repr
                                       (let
                                          CRec'2336 ({lfirst = v_X'2179})
                                        =
                                          Obj.magic
                                            v_range'2177
                                        in
                                        Obj.magic
                                          v_X'2179));
                                   llast =
                                     (Obj.repr
                                       (let
                                          CRec'2336 ({llast = v_X'2180})
                                        =
                                          Obj.magic
                                            v_range'2177
                                        in
                                        Obj.magic
                                          v_X'2180));
                                   lpartialResolutions =
                                     (Obj.repr
                                       v_resolutions'2178) }
                               in
                               let v_'2182 =
                                 Obj.magic
                                   (:=)
                                   v_ambiguities'2170
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.cons
                                      v_err'2181
                                      (Obj.magic
                                         (!)
                                         v_ambiguities'2170))
                               in
                               CNone'1621)
                          | Option.None ->
                              (Obj.magic
                                 (let v_'2183 =
                                    Obj.magic
                                      v_dprintLn
                                      v_tops'2173
                                  in
                                  failwith
                                    "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 970:30-970:35 ERROR: Reached a never term, which should be impossible in a well-typed program."))))
            and v_workOne'2172 =
                fun v_node'2184 ->
                  let v_defaultCase'2769 =
                    fun nv_ ->
                      failwith
                        "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 985:15-985:20 ERROR: Reached a never term, which should be impossible in a well-typed program."
                  in
                  match
                    Obj.magic
                      v_node'2184
                  with
                  | CAtomP'1717 v_x'2770 ->
                      (match
                         Obj.magic
                           (let v__target'2771 =
                              Obj.magic
                                Obj.magic
                                v_node'2184
                            in
                            let
                              CRec'2333 ({linput = v_input'2772;lself = v_self'2773})
                            =
                              Obj.magic
                                Obj.magic
                                v__target'2771
                            in
                            match
                              Obj.magic
                                Obj.magic
                                v_input'2772
                            with
                            | CAtomI'1711 v__n'2774 ->
                                (let
                                   CRec'2314 ({lconstruct = v_construct'2775})
                                 =
                                   Obj.magic
                                     Obj.magic
                                     v_input'2772
                                 in
                                 Option.Some (v_construct'2775, v_self'2773))
                            | _ ->
                                (Obj.magic
                                   Obj.magic
                                   (Option.None)))
                       with
                       | Option.Some (v_c'2185, v_self'2186) ->
                           (CSome'1620 (Obj.repr
                               (Obj.magic
                                  v_c'2185
                                  v_self'2186)))
                       | Option.None ->
                           (Obj.magic
                              (Obj.magic
                                 v_defaultCase'2769
                                 ())))
                  | CInfixP'1718 v_x'2776 ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2777 =
                                 Obj.magic
                                   Obj.magic
                                   v_node'2184
                               in
                               let
                                 CRec'2303 ({linput = v_input'2778;lself = v_self'2779;lleftChildAlts = v_leftChildAlts'2780;lrightChildAlts = v_rightChildAlts'2781})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2777
                               in
                               match
                                 Obj.magic
                                   Obj.magic
                                   v_input'2778
                               with
                               | CInfixI'1712 v__n'2782 ->
                                   (let
                                      CRec'2317 ({lconstruct = v_construct'2783})
                                    =
                                      Obj.magic
                                        Obj.magic
                                        v_input'2778
                                    in
                                    Option.Some (v_construct'2783, v_self'2779, v_leftChildAlts'2780, v_rightChildAlts'2781))
                               | _ ->
                                   (Obj.magic
                                      Obj.magic
                                      (Option.None)))
                          with
                          | Option.Some (v_c'2190, v_self'2191, v_ls'2192, v_rs'2193) ->
                              (let v_l'2194 =
                                 Obj.magic
                                   v_workMany'2171
                                   v_ls'2192
                               in
                               let v_r'2195 =
                                 Obj.magic
                                   v_workMany'2171
                                   v_rs'2193
                               in
                               Obj.magic
                                 v_optionZipWith
                                 (Obj.magic
                                    v_c'2190
                                    v_self'2191)
                                 v_l'2194
                                 v_r'2195)
                          | Option.None ->
                              (Obj.magic
                                 (Obj.magic
                                    v_defaultCase'2769
                                    ()))))
                  | CPrefixP'1719 v_x'2784 ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2785 =
                                 Obj.magic
                                   Obj.magic
                                   v_node'2184
                               in
                               let
                                 CRec'2304 ({linput = v_input'2786;lself = v_self'2787;lrightChildAlts = v_rightChildAlts'2788})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2785
                               in
                               match
                                 Obj.magic
                                   Obj.magic
                                   v_input'2786
                               with
                               | CPrefixI'1713 v__n'2789 ->
                                   (let
                                      CRec'2316 ({lconstruct = v_construct'2790})
                                    =
                                      Obj.magic
                                        Obj.magic
                                        v_input'2786
                                    in
                                    Option.Some (v_construct'2790, v_self'2787, v_rightChildAlts'2788))
                               | _ ->
                                   (Obj.magic
                                      Obj.magic
                                      (Option.None)))
                          with
                          | Option.Some (v_c'2187, v_self'2188, v_rs'2189) ->
                              (Obj.magic
                                 v_optionMap
                                 (Obj.magic
                                    v_c'2187
                                    v_self'2188)
                                 (Obj.magic
                                    v_workMany'2171
                                    v_rs'2189))
                          | Option.None ->
                              (Obj.magic
                                 (Obj.magic
                                    v_defaultCase'2769
                                    ()))))
                  | CPostfixP'1720 v_x'2791 ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2792 =
                                 Obj.magic
                                   Obj.magic
                                   v_node'2184
                               in
                               let
                                 CRec'2325 ({linput = v_input'2793;lself = v_self'2794;lleftChildAlts = v_leftChildAlts'2795})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2792
                               in
                               match
                                 Obj.magic
                                   Obj.magic
                                   v_input'2793
                               with
                               | CPostfixI'1714 v__n'2796 ->
                                   (let
                                      CRec'2318 ({lconstruct = v_construct'2797})
                                    =
                                      Obj.magic
                                        Obj.magic
                                        v_input'2793
                                    in
                                    Option.Some (v_construct'2797, v_self'2794, v_leftChildAlts'2795))
                               | _ ->
                                   (Obj.magic
                                      Obj.magic
                                      (Option.None)))
                          with
                          | Option.Some (v_c'2196, v_self'2197, v_ls'2198) ->
                              (Obj.magic
                                 v_optionMap
                                 (Obj.magic
                                    v_c'2196
                                    v_self'2197)
                                 (Obj.magic
                                    v_workMany'2171
                                    v_ls'2198))
                          | Option.None ->
                              (Obj.magic
                                 (Obj.magic
                                    v_defaultCase'2769
                                    ()))))
                  | _ ->
                      (Obj.magic
                         (v_defaultCase'2769
                            ()))
            in match
              Obj.magic
                (let v__target'2798 =
                   Obj.magic
                     v_workMany'2171
                     v_nodes'2081
                 in
                 match
                   Obj.magic
                     Obj.magic
                     v__target'2798
                 with
                 | CSome'1620 v__n'2799 ->
                     (Option.Some (v__n'2799))
                 | _ ->
                     (Obj.magic
                        Obj.magic
                        (Option.None)))
            with
            | Option.Some (v_res'2199) ->
                (CRight'1687 (Obj.repr
                    v_res'2199))
            | Option.None ->
                (Obj.magic
                   (CLeft'1686 (Obj.repr
                       (CAmbiguities'2076 (Obj.repr
                           (Obj.magic
                              (!)
                              v_ambiguities'2170))))));;
let v_allowAll =
  fun v_cmp'2201 ->
    CDisallowSet'1696 (Obj.repr
       (Obj.magic
          Boot.Intrinsics.Mmap.empty
          v_cmp'2201));;
let v_allowNone =
  fun v_cmp'2203 ->
    CAllowSet'1695 (Obj.repr
       (Obj.magic
          Boot.Intrinsics.Mmap.empty
          v_cmp'2203));;
let v_allowOneMore =
  fun v_label'2205 ->
    fun v_set'2206 ->
      Obj.magic
        v_breakableInsertAllowSet
        v_label'2205
        v_set'2206;;
let v_allowOneLess =
  fun v_label'2208 ->
    fun v_set'2209 ->
      Obj.magic
        v_breakableRemoveAllowSet
        v_label'2208
        v_set'2209;;
let v_atom =
  fun v_label'2211 ->
    fun v_construct'2212 ->
      CBreakableAtom'1698 { llabel =
          (Obj.repr
            v_label'2211);
        lconstruct =
          (Obj.repr
            v_construct'2212) };;
let v_prefix =
  fun v_label'2214 ->
    fun v_construct'2215 ->
      fun v_rightAllow'2216 ->
        CBreakablePrefix'1700 { llabel =
            (Obj.repr
              v_label'2214);
          lconstruct =
            (Obj.repr
              v_construct'2215);
          lrightAllow =
            (Obj.repr
              v_rightAllow'2216) };;
let v_postfix =
  fun v_label'2218 ->
    fun v_construct'2219 ->
      fun v_leftAllow'2220 ->
        CBreakablePostfix'1701 { llabel =
            (Obj.repr
              v_label'2218);
          lconstruct =
            (Obj.repr
              v_construct'2219);
          lleftAllow =
            (Obj.repr
              v_leftAllow'2220) };;
let v_infix =
  fun v_label'2222 ->
    fun v_construct'2223 ->
      fun v_leftAllow'2224 ->
        fun v_rightAllow'2225 ->
          CBreakableInfix'1699 { llabel =
              (Obj.repr
                v_label'2222);
            lconstruct =
              (Obj.repr
                v_construct'2223);
            lleftAllow =
              (Obj.repr
                v_leftAllow'2224);
            lrightAllow =
              (Obj.repr
                v_rightAllow'2225) };;
let v_emptyGrammar =
  fun v_topAllowed'2227 ->
    CRec'2338 { lproductions =
        (Obj.repr
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |]));
      lprecedences =
        (Obj.repr
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |]));
      ltopAllowed =
        (Obj.repr
          v_topAllowed'2227) };;
let v_addProd =
  fun v_prod'2229 ->
    fun v_gram'2230 ->
      let
        CRec'2338 v_rec'2800
      =
        Obj.magic
          v_gram'2230
      in
      CRec'2338 { v_rec'2800
        with
        lproductions =
          Obj.repr
            (Obj.magic
               Boot.Intrinsics.Mseq.snoc
               (let
                  CRec'2338 ({lproductions = v_X'2231})
                =
                  Obj.magic
                    v_gram'2230
                in
                Obj.magic
                  v_X'2231)
               v_prod'2229) };;
let v_addPrec =
  fun v_l'2233 ->
    fun v_r'2234 ->
      fun v_mayL'2235 ->
        fun v_mayR'2236 ->
          fun v_gram'2237 ->
            let
              CRec'2338 v_rec'2801
            =
              Obj.magic
                v_gram'2237
            in
            CRec'2338 { v_rec'2801
              with
              lprecedences =
                Obj.repr
                  (Obj.magic
                     Boot.Intrinsics.Mseq.snoc
                     (let
                        CRec'2338 ({lprecedences = v_X'2238})
                      =
                        Obj.magic
                          v_gram'2237
                      in
                      Obj.magic
                        v_X'2238)
                     (CRec'2339 { l0 =
                          (Obj.repr
                            (CRec'2339 { l0 =
                                 (Obj.repr
                                   v_l'2233);
                               l1 =
                                 (Obj.repr
                                   v_r'2234) }));
                        l1 =
                          (Obj.repr
                            (CRec'2294 { lmayGroupLeft =
                                 (Obj.repr
                                   v_mayL'2235);
                               lmayGroupRight =
                                 (Obj.repr
                                   v_mayR'2236) })) })) };;
let v_finalize =
  v_breakableGenGrammar;;
let v_getAtom =
  fun v_gram'2241 ->
    fun v_label'2242 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find
        v_label'2242
        (let
           CRec'2319 ({latoms = v_X'2243})
         =
           Obj.magic
             v_gram'2241
         in
         Obj.magic
           v_X'2243);;
let v_getPrefix =
  fun v_gram'2245 ->
    fun v_label'2246 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find
        v_label'2246
        (let
           CRec'2319 ({lprefixes = v_X'2247})
         =
           Obj.magic
             v_gram'2245
         in
         Obj.magic
           v_X'2247);;
let v_getPostfix =
  fun v_gram'2249 ->
    fun v_label'2250 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find
        v_label'2250
        (let
           CRec'2319 ({lpostfixes = v_X'2251})
         =
           Obj.magic
             v_gram'2249
         in
         Obj.magic
           v_X'2251);;
let v_getInfix =
  fun v_gram'2253 ->
    fun v_label'2254 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find
        v_label'2254
        (let
           CRec'2319 ({linfixes = v_X'2255})
         =
           Obj.magic
             v_gram'2253
         in
         Obj.magic
           v_X'2255);;
let v_init =
  v_breakableInitState;;
let v_addAtom =
  v_breakableAddAtom;;
let v_addPrefix =
  v_breakableAddPrefix;;
let v_addPostfix =
  v_breakableAddPostfix;;
let v_addInfix =
  v_breakableAddInfix;;
let v_finalizeParse =
  v_breakableFinalizeParse;;
let v_maybe =
  fun v_none'2263 ->
    fun v_some'2264 ->
      fun v_opt'2265 ->
        match
          Obj.magic
            (let v__target'2802 =
               v_opt'2265
             in
             match
               Obj.magic
                 Obj.magic
                 v__target'2802
             with
             | CSome'1620 v__n'2803 ->
                 (Option.Some (v__n'2803))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None)))
        with
        | Option.Some (v_a'2266) ->
            (Obj.magic
               v_some'2264
               v_a'2266)
        | Option.None ->
            (Obj.magic
               (Obj.magic
                  v_none'2263
                  ()));;
let v_constructResult =
  v_breakableConstructResult;;
let v_either =
  fun v_left'2269 ->
    fun v_right'2270 ->
      fun v_either'2271 ->
        let v_X'2272 =
          v_either'2271
        in
        let v_defaultCase'2804 =
          fun nv_ ->
            failwith
              "FILE \"/home/vipa/Projects/static-resolvable/breakable-ml/breakable_impl.mc\" 165:4-165:7 ERROR: Reached a never term, which should be impossible in a well-typed program."
        in
        match
          Obj.magic
            v_X'2272
        with
        | CLeft'1686 v_x'2805 ->
            (let v_a'2273 =
               Obj.magic
                 Obj.magic
                 v_x'2805
             in
             Obj.magic
               v_left'2269
               v_a'2273)
        | CRight'1687 v_x'2806 ->
            (Obj.magic
               (let v_b'2274 =
                  Obj.magic
                    Obj.magic
                    v_x'2806
                in
                Obj.magic
                  v_right'2270
                  v_b'2274))
        | _ ->
            (Obj.magic
               (v_defaultCase'2804
                  ()));;
let v_foldError =
  fun v_amb'2276 ->
    fun v_err'2277 ->
      let v_X'2278 =
        v_err'2277
      in
      match
        Obj.magic
          (let v__target'2807 =
             v_X'2278
           in
           match
             Obj.magic
               Obj.magic
               v__target'2807
           with
           | CAmbiguities'2076 v__n'2808 ->
               (Option.Some (v__n'2808))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_ambs'2279) ->
          (Obj.magic
             v_amb'2276
             v_ambs'2279)
      | Option.None ->
          (Obj.magic
             (failwith
                "FILE \"/home/vipa/Projects/static-resolvable/breakable-ml/breakable_impl.mc\" 174:4-174:7 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v_seqFoldl =
  Boot.Intrinsics.Mseq.Helpers.fold_left;;
let v_ambiguity =
  fun v_f'2282 ->
    fun v_amb'2283 ->
      Obj.magic
        v_f'2282
        (let
           CRec'2337 ({lfirst = v_X'2284})
         =
           Obj.magic
             v_amb'2283
         in
         Obj.magic
           v_X'2284)
        (let
           CRec'2337 ({llast = v_X'2285})
         =
           Obj.magic
             v_amb'2283
         in
         Obj.magic
           v_X'2285)
        (let
           CRec'2337 ({lpartialResolutions = v_X'2286})
         =
           Obj.magic
             v_amb'2283
         in
         Obj.magic
           v_X'2286);;
CRec'2340 { l0 =
    (Obj.repr
      v_allowAll);
  l1 =
    (Obj.repr
      v_allowNone);
  l2 =
    (Obj.repr
      v_allowOneMore);
  l3 =
    (Obj.repr
      v_allowOneLess);
  l4 =
    (Obj.repr
      v_atom);
  l5 =
    (Obj.repr
      v_prefix);
  l6 =
    (Obj.repr
      v_postfix);
  l7 =
    (Obj.repr
      v_infix);
  l8 =
    (Obj.repr
      v_emptyGrammar);
  l9 =
    (Obj.repr
      v_addProd);
  l10 =
    (Obj.repr
      v_addPrec);
  l11 =
    (Obj.repr
      v_finalize);
  l12 =
    (Obj.repr
      v_getAtom);
  l13 =
    (Obj.repr
      v_getPrefix);
  l14 =
    (Obj.repr
      v_getPostfix);
  l15 =
    (Obj.repr
      v_getInfix);
  l16 =
    (Obj.repr
      v_init);
  l17 =
    (Obj.repr
      v_addAtom);
  l18 =
    (Obj.repr
      v_addPrefix);
  l19 =
    (Obj.repr
      v_addPostfix);
  l20 =
    (Obj.repr
      v_addInfix);
  l21 =
    (Obj.repr
      v_finalizeParse);
  l22 =
    (Obj.repr
      v_maybe);
  l23 =
    (Obj.repr
      v_constructResult);
  l24 =
    (Obj.repr
      v_either);
  l25 =
    (Obj.repr
      v_foldError);
  l26 =
    (Obj.repr
      v_seqFoldl);
  l27 =
    (Obj.repr
      v_ambiguity) };;
end [@ocaml.warning "-27-26-37-32-34-60-11"]
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
  val emptyGrammar : allow_set -> grammar
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

  val init : gen_grammar -> unit -> ropen state

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

module Make (S : Self) = struct
  include S
  open Breakable_impl

  type res =
    | Atom of atom_self
    | Infix of res * infix_self * res
    | Prefix of prefix_self * res
    | Postfix of res * postfix_self

  type tagged_self =
    | AtomSelf of atom_self
    | InfixSelf of infix_self
    | PrefixSelf of prefix_self
    | PostfixSelf of postfix_self

  let mk_atom (s : tagged_self) : res = match s with
    | AtomSelf s -> Atom s
    | _ -> assert false
  let mk_infix (s : tagged_self) (l : res) (r : res) : res = match s with
    | InfixSelf s -> Infix (l, s, r)
    | _ -> assert false
  let mk_prefix (s : tagged_self) (r : res) : res = match s with
    | PrefixSelf s -> Prefix (s, r)
    | _ -> assert false
  let mk_postfix (s : tagged_self) (l : res)  : res = match s with
    | PostfixSelf s -> Postfix (l, s)
    | _ -> assert false

  let selfToStr = function
    | AtomSelf s -> atom_to_str s
    | InfixSelf s -> infix_to_str s
    | PrefixSelf s -> prefix_to_str s
    | PostfixSelf s -> postfix_to_str s

  type allow_set = Obj.t
  type production = Obj.t
  type grammar = Obj.t
  type gen_grammar = Obj.t
  type lclosed = unit
  type lopen = unit
  type rclosed = unit
  type ropen = unit
  type ('l, 'r) input = Obj.t
  type 'r state = Obj.t
  type permanent_node = Obj.t
  type 'a sequence = Obj.t
  type error = Obj.t
  type ambiguity = Obj.t

  let allowAll = Obj.magic v_allowAll compareLabel
  let allowNone = Obj.magic v_allowNone compareLabel
  let allowOneMore = Obj.magic v_allowOneMore
  let allowOneLess = Obj.magic v_allowOneLess

  let atom label = Obj.magic v_atom label mk_atom
  let infix label lallow rallow = Obj.magic v_infix label mk_infix lallow rallow
  let prefix label rallow = Obj.magic v_prefix label mk_prefix rallow
  let postfix label lallow = Obj.magic v_postfix label mk_postfix lallow

  let emptyGrammar topAllowed = Obj.magic v_emptyGrammar topAllowed
  let addProd prod gram = Obj.magic v_addProd prod gram
  let addPrec l r ml mr gram = Obj.magic v_addPrec l r ml mr gram

  let finalize gram = Obj.magic v_finalize compareLabel gram

  let getAtom gen label = Obj.magic v_getAtom gen label
  let getInfix gen label = Obj.magic v_getInfix gen label
  let getPrefix gen label = Obj.magic v_getPrefix gen label
  let getPostfix gen label = Obj.magic v_getPostfix gen label

  let init grammar () = Obj.magic v_init grammar ()

  let addAtom input self st = Obj.magic v_addAtom input (AtomSelf self) st
  let addPrefix input self st = Obj.magic v_addPrefix input (PrefixSelf self) st
  let addPostfix input self st =
    Obj.magic v_addPostfix input (PostfixSelf self) st
    |> v_maybe (fun _ -> None) (fun x -> Some x)
  let addInfix input self st =
    Obj.magic v_addInfix input (InfixSelf self) st
    |> v_maybe (fun _ -> None) (fun x -> Some x)

  let finalizeParse st =
    Obj.magic v_finalizeParse st
    |> v_maybe (fun _ -> None) (fun x -> Some x)

  let constructResult parInput roots =
    Obj.magic v_constructResult selfToStr lpar_tok rpar_tok parInput roots
    |> v_either Result.error Result.ok

  let foldError deconAmbiguities error = Obj.magic v_foldError deconAmbiguities error

  let seqFoldl = Obj.magic v_seqFoldl

  let ambiguity deconAmbiguity ambiguity =
    let decon selfl selfr resolutions =
      let l = match selfl with
        | AtomSelf s -> Either.left s
        | PrefixSelf s -> Either.right s
        | _ -> assert false in
      let r = match selfr with
        | AtomSelf s -> Either.left s
        | PostfixSelf s -> Either.right s
        | _ -> assert false in
      deconAmbiguity l r resolutions
    in Obj.magic v_ambiguity decon ambiguity
end
