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
type v_record'2317 =
  | CRec'2316 of {l0: Obj.t;l1: Obj.t;l2: Obj.t;l3: Obj.t;l4: Obj.t;l5: Obj.t;l6: Obj.t;l7: Obj.t;l8: Obj.t;l9: Obj.t;l10: Obj.t;l11: Obj.t;l12: Obj.t;l13: Obj.t;l14: Obj.t;l15: Obj.t;l16: Obj.t;l17: Obj.t;l18: Obj.t;l19: Obj.t;l20: Obj.t;l21: Obj.t;l22: Obj.t;l23: Obj.t;l24: Obj.t;l25: Obj.t;l26: Obj.t;l27: Obj.t};;
type v_record'2318 =
  | CRec'2315 of {l0: Obj.t;l1: Obj.t};;
type v_record'2319 =
  | CRec'2314 of {lfirst: Obj.t;llast: Obj.t;lpartialResolutions: Obj.t};;
type v_record'2320 =
  | CRec'2313 of {lfirst: Obj.t;llast: Obj.t};;
type v_BreakableError'2056 =
  | CAmbiguities'2057 of Obj.t;;
type v_record'2321 =
  | CRec'2311 of {lparents: Obj.t;lnode: Obj.t};;
type v_record'2322 =
  | CRec'2310 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t};;
type v_record'2323 =
  | CRec'2309 of {lparents: Obj.t;laddedNodesLeftChildren: Obj.t;laddedNodesRightChildren: Obj.t;ltentativeData: Obj.t;lmaxDistanceFromRoot: Obj.t};;
type v_record'2324 =
  | CRec'2308 of {lidx: Obj.t;linput: Obj.t;lself: Obj.t};;
type v_record'2325 =
  | CRec'2303 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t};;
type v_record'2326 =
  | CRec'2301 of {lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t};;
type v_record'2327 =
  | CRec'2298 of {lconstruct: Obj.t;lleftAllow: Obj.t;lid: Obj.t;lprecWhenThisIsRight: Obj.t};;
type v_record'2328 =
  | CRec'2297 of {lconstruct: Obj.t;lleftAllow: Obj.t;lrightAllow: Obj.t;lid: Obj.t;lprecWhenThisIsRight: Obj.t};;
type v_record'2329 =
  | CRec'2296 of {lconstruct: Obj.t;lrightAllow: Obj.t;lid: Obj.t};;
type v_record'2330 =
  | CRec'2294 of {lconstruct: Obj.t;lid: Obj.t};;
type v_record'2331 =
  | CRec'2291 of {ltimestep: Obj.t;lnextIdx: Obj.t;lfrontier: Obj.t};;
type v_record'2332 =
  | CRec'2290 of {laddedNodesLeftChildren: Obj.t;laddedNodesRightChildren: Obj.t};;
type v_TentativeNode'1715 =
  | CTentativeLeaf'1716 of {lparents: Obj.t;lnode: Obj.t}
  | CTentativeMid'1717 of {lparents: Obj.t;laddedNodesLeftChildren: Obj.t;laddedNodesRightChildren: Obj.t;ltentativeData: Obj.t;lmaxDistanceFromRoot: Obj.t}
  | CTentativeRoot'1718 of {laddedNodesLeftChildren: Obj.t;laddedNodesRightChildren: Obj.t};;
type v_TentativeData'1711 =
  | CInfixT'1712 of {lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t}
  | CPrefixT'1713 of {lidx: Obj.t;linput: Obj.t;lself: Obj.t};;
type v_record'2333 =
  | CRec'2284 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lrightChildAlts: Obj.t};;
type v_record'2334 =
  | CRec'2283 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t;lrightChildAlts: Obj.t};;
type v_PermanentNode'1706 =
  | CAtomP'1707 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t}
  | CInfixP'1708 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t;lrightChildAlts: Obj.t}
  | CPrefixP'1709 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lrightChildAlts: Obj.t}
  | CPostfixP'1710 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t};;
type v_record'2335 =
  | CRec'2281 of {latoms: Obj.t;lprefixes: Obj.t;linfixes: Obj.t;lpostfixes: Obj.t};;
type v_BreakableInput'1700 =
  | CAtomI'1701 of {lconstruct: Obj.t;lid: Obj.t}
  | CInfixI'1702 of {lconstruct: Obj.t;lleftAllow: Obj.t;lrightAllow: Obj.t;lid: Obj.t;lprecWhenThisIsRight: Obj.t}
  | CPrefixI'1703 of {lconstruct: Obj.t;lrightAllow: Obj.t;lid: Obj.t}
  | CPostfixI'1704 of {lconstruct: Obj.t;lleftAllow: Obj.t;lid: Obj.t;lprecWhenThisIsRight: Obj.t};;
type v_record'2336 =
  | CRec'2276 of {lproductions: Obj.t;lprecedences: Obj.t};;
type v_record'2337 =
  | CRec'2274 of {lmayGroupLeft: Obj.t;lmayGroupRight: Obj.t};;
type v_record'2338 =
  | CRec'2273 of {llabel: Obj.t;lconstruct: Obj.t;lleftAllow: Obj.t};;
type v_record'2339 =
  | CRec'2272 of {llabel: Obj.t;lconstruct: Obj.t;lrightAllow: Obj.t};;
type v_record'2340 =
  | CRec'2271 of {llabel: Obj.t;lconstruct: Obj.t;lleftAllow: Obj.t;lrightAllow: Obj.t};;
type v_record'2341 =
  | CRec'2270 of {llabel: Obj.t;lconstruct: Obj.t};;
type v_BreakableProduction'1687 =
  | CBreakableAtom'1688 of {llabel: Obj.t;lconstruct: Obj.t}
  | CBreakableInfix'1689 of {llabel: Obj.t;lconstruct: Obj.t;lleftAllow: Obj.t;lrightAllow: Obj.t}
  | CBreakablePrefix'1690 of {llabel: Obj.t;lconstruct: Obj.t;lrightAllow: Obj.t}
  | CBreakablePostfix'1691 of {llabel: Obj.t;lconstruct: Obj.t;lleftAllow: Obj.t};;
type v_AllowSet'1684 =
  | CAllowSet'1685 of Obj.t
  | CDisallowSet'1686 of Obj.t;;
type v_Either'1675 =
  | CLeft'1676 of Obj.t
  | CRight'1677 of Obj.t;;
type v_Option'1609 =
  | CSome'1610 of Obj.t
  | CNone'1611;;
let v_not =
  fun v_a'1607 ->
    if
      Obj.magic
        v_a'1607
    then
      false
    else
      Obj.magic
        true;;
let v_optionMap =
  fun v_f'1612 ->
    fun v_o'1613 ->
      match
        Obj.magic
          (let v__target'2342 =
             v_o'1613
           in
           match
             Obj.magic
               Obj.magic
               v__target'2342
           with
           | CSome'1610 v__n'2343 ->
               (Option.Some (v__n'2343))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_t'1614) ->
          (CSome'1610 (Obj.repr
              (Obj.magic
                 v_f'1612
                 v_t'1614)))
      | Option.None ->
          (Obj.magic
             CNone'1611);;
let v_optionZipWith =
  fun v_f'1616 ->
    fun v_o1'1617 ->
      fun v_o2'1618 ->
        match
          Obj.magic
            (let v__target'2344 =
               CRec'2315 { l0 =
                   (Obj.repr
                     v_o1'1617);
                 l1 =
                   (Obj.repr
                     v_o2'1618) }
             in
             let
               CRec'2315 ({l0 = v_0'2345;l1 = v_1'2346})
             =
               Obj.magic
                 Obj.magic
                 v__target'2344
             in
             match
               Obj.magic
                 Obj.magic
                 v_0'2345
             with
             | CSome'1610 v__n'2347 ->
                 (match
                    Obj.magic
                      Obj.magic
                      v_1'2346
                  with
                  | CSome'1610 v__n'2348 ->
                      (Option.Some (v__n'2347, v__n'2348))
                  | _ ->
                      (Obj.magic
                         Obj.magic
                         (Option.None)))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None)))
        with
        | Option.Some (v_v1'1619, v_v2'1620) ->
            (CSome'1610 (Obj.repr
                (Obj.magic
                   v_f'1616
                   v_v1'1619
                   v_v2'1620)))
        | Option.None ->
            (Obj.magic
               CNone'1611);;
let v_optionGetOrElse =
  fun v_d'1622 ->
    fun v_o'1623 ->
      match
        Obj.magic
          (let v__target'2349 =
             v_o'1623
           in
           match
             Obj.magic
               Obj.magic
               v__target'2349
           with
           | CSome'1610 v__n'2350 ->
               (Option.Some (v__n'2350))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_t'1624) ->
          v_t'1624
      | Option.None ->
          (Obj.magic
             (Obj.magic
                v_d'1622
                ()));;
let v_mapOption =
  fun v_f'1626 ->
    let rec v_work'1627 =
        fun v_as'1628 ->
          match
            Obj.magic
              (let v__target'2351 =
                 v_as'1628
               in
               if
                 Obj.magic
                   ((<) : int -> int -> bool)
                   (Obj.magic
                      Boot.Intrinsics.Mseq.length
                      v__target'2351)
                   1
               then
                 Option.None
               else
                 Obj.magic
                   Obj.magic
                   (let
                      (v__prefix'2352, v__splitTemp'2353)
                    =
                      Obj.magic
                        Boot.Intrinsics.Mseq.split_at
                        v__target'2351
                        1
                    in
                    let
                      (v__middle'2354, v__postfix'2355)
                    =
                      Obj.magic
                        Boot.Intrinsics.Mseq.split_at
                        v__splitTemp'2353
                        (Obj.magic
                           Int.sub
                           (Obj.magic
                              Boot.Intrinsics.Mseq.length
                              v__splitTemp'2353)
                           0)
                    in
                    let v__seqElem'2356 =
                      Obj.magic
                        Boot.Intrinsics.Mseq.get
                        v__prefix'2352
                        0
                    in
                    Option.Some (v__seqElem'2356, v__middle'2354)))
          with
          | Option.Some (v_a'1629, v_as'1630) ->
              (match
                 Obj.magic
                   (let v__target'2357 =
                      Obj.magic
                        v_f'1626
                        v_a'1629
                    in
                    match
                      Obj.magic
                        Obj.magic
                        v__target'2357
                    with
                    | CSome'1610 v__n'2358 ->
                        (Option.Some (v__n'2358))
                    | _ ->
                        (Obj.magic
                           Obj.magic
                           (Option.None)))
               with
               | Option.Some (v_b'1631) ->
                   (Obj.magic
                      Boot.Intrinsics.Mseq.cons
                      v_b'1631
                      (Obj.magic
                         v_work'1627
                         v_as'1630))
               | Option.None ->
                   (Obj.magic
                      (Obj.magic
                         v_work'1627
                         v_as'1630)))
          | Option.None ->
              (Obj.magic
                 (Obj.magic
                    Boot.Intrinsics.Mseq.Helpers.of_array
                    [|  |]))
    in v_work'1627;;
let v_for_ =
  fun v_xs'1633 ->
    fun v_f'1634 ->
      Obj.magic
        Boot.Intrinsics.Mseq.iter
        v_f'1634
        v_xs'1633;;
let v_join =
  fun v_seqs'1636 ->
    Obj.magic
      Boot.Intrinsics.Mseq.Helpers.fold_left
      Boot.Intrinsics.Mseq.concat
      (Obj.magic
         Boot.Intrinsics.Mseq.Helpers.of_array
         [|  |])
      v_seqs'1636;;
let v_seqLiftA2 =
  fun v_f'1638 ->
    fun v_as'1639 ->
      fun v_bs'1640 ->
        Obj.magic
          v_join
          (Obj.magic
             Boot.Intrinsics.Mseq.map
             (fun v_a'1641 ->
                Obj.magic
                  Boot.Intrinsics.Mseq.map
                  (Obj.magic
                     v_f'1638
                     v_a'1641)
                  v_bs'1640)
             v_as'1639);;
let rec v_filter =
    fun v_p'1644 ->
      fun v_seq'1645 ->
        if
          Obj.magic
            (Obj.magic
               Boot.Intrinsics.Mseq.null
               v_seq'1645)
        then
          Obj.magic
            Boot.Intrinsics.Mseq.Helpers.of_array
            [|  |]
        else
          Obj.magic
            (if
               Obj.magic
                 (Obj.magic
                    v_p'1644
                    (Obj.magic
                       Boot.Intrinsics.Mseq.head
                       v_seq'1645))
             then
               Obj.magic
                 Boot.Intrinsics.Mseq.cons
                 (Obj.magic
                    Boot.Intrinsics.Mseq.head
                    v_seq'1645)
                 (Obj.magic
                    v_filter
                    v_p'1644
                    (Obj.magic
                       Boot.Intrinsics.Mseq.tail
                       v_seq'1645))
             else
               Obj.magic
                 (Obj.magic
                    v_filter
                    v_p'1644
                    (Obj.magic
                       Boot.Intrinsics.Mseq.tail
                       v_seq'1645)));;
let v_min =
  fun v_cmp'1646 ->
    fun v_seq'1647 ->
      let rec v_work'1648 =
          fun v_e'1649 ->
            fun v_seq'1650 ->
              if
                Obj.magic
                  (Obj.magic
                     Boot.Intrinsics.Mseq.null
                     v_seq'1650)
              then
                CSome'1610 (Obj.repr
                   v_e'1649)
              else
                Obj.magic
                  (let v_h'1651 =
                     Obj.magic
                       Boot.Intrinsics.Mseq.head
                       v_seq'1650
                   in
                   let v_t'1652 =
                     Obj.magic
                       Boot.Intrinsics.Mseq.tail
                       v_seq'1650
                   in
                   if
                     Obj.magic
                       (Obj.magic
                          ((<) : int -> int -> bool)
                          (Obj.magic
                             v_cmp'1646
                             v_e'1649
                             v_h'1651)
                          0)
                   then
                     Obj.magic
                       v_work'1648
                       v_e'1649
                       v_t'1652
                   else
                     Obj.magic
                       (Obj.magic
                          v_work'1648
                          v_h'1651
                          v_t'1652))
      in if
        Obj.magic
          (Obj.magic
             Boot.Intrinsics.Mseq.null
             v_seq'1647)
      then
        CNone'1611
      else
        Obj.magic
          (Obj.magic
             v_work'1648
             (Obj.magic
                Boot.Intrinsics.Mseq.head
                v_seq'1647)
             (Obj.magic
                Boot.Intrinsics.Mseq.tail
                v_seq'1647));;
let v_minOrElse =
  fun v_d'1654 ->
    fun v_cmp'1655 ->
      fun v_seq'1656 ->
        Obj.magic
          v_optionGetOrElse
          v_d'1654
          (Obj.magic
             v_min
             v_cmp'1655
             v_seq'1656);;
let v_maxOrElse =
  fun v_d'1658 ->
    fun v_cmp'1659 ->
      Obj.magic
        v_minOrElse
        v_d'1658
        (fun v_l'1660 ->
           fun v_r'1661 ->
             Obj.magic
               v_cmp'1659
               v_r'1661
               v_l'1660);;
let v_mapLookup =
  fun v_k'1663 ->
    fun v_m'1664 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find_apply_or_else
        (fun v_v'1665 ->
           CSome'1610 (Obj.repr
              v_v'1665))
        (fun v_'1666 ->
           CNone'1611)
        v_k'1663
        v_m'1664;;
let v_mapFromSeq =
  fun v_cmp'1668 ->
    fun v_bindings'1669 ->
      Obj.magic
        Boot.Intrinsics.Mseq.Helpers.fold_left
        (fun v_acc'1670 ->
           fun v_binding'1671 ->
             Obj.magic
               Boot.Intrinsics.Mmap.insert
               (let
                  CRec'2315 ({l0 = v_X'1672})
                =
                  Obj.magic
                    v_binding'1671
                in
                Obj.magic
                  v_X'1672)
               (let
                  CRec'2315 ({l1 = v_X'1673})
                =
                  Obj.magic
                    v_binding'1671
                in
                Obj.magic
                  v_X'1673)
               v_acc'1670)
        (Obj.magic
           Boot.Intrinsics.Mmap.empty
           v_cmp'1668)
        v_bindings'1669;;
let v_printLn =
  fun v_s'1678 ->
    let v_'1679 =
      Obj.magic
        Boot.Intrinsics.IO.print
        (Obj.magic
           Boot.Intrinsics.Mseq.concat
           v_s'1678
           (Obj.magic
              Boot.Intrinsics.Mseq.Helpers.of_array
              [| (10) |]))
    in
    Obj.magic
      Boot.Intrinsics.IO.flush_stdout
      ();;
let v_dprintLn =
  fun v_x'1681 ->
    let v_'1682 =
      Obj.magic
        Boot.Intrinsics.IO.dprint
        v_x'1681
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
  fun v_n'1728 ->
    match
      Obj.magic
        (let v__target'2359 =
           v_n'1728
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2359
             with
             | CTentativeLeaf'1716 v__n'2360 ->
                 (let
                    CRec'2311 ({lparents = v_parents'2361})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2359
                  in
                  Option.Some (v_parents'2361))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2364 ->
               (Option.Some v__x'2364)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     Obj.magic
                       Obj.magic
                       v__target'2359
                   with
                   | CTentativeMid'1717 v__n'2362 ->
                       (let
                          CRec'2309 ({lparents = v_parents'2363})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2359
                        in
                        Option.Some (v_parents'2363))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_ps'1729) ->
             (Option.Some (v_ps'1729))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_ps'1729) ->
        (CSome'1610 (Obj.repr
            v_ps'1729))
    | Option.None ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2365 =
                   v_n'1728
                 in
                 match
                   Obj.magic
                     Obj.magic
                     v__target'2365
                 with
                 | CTentativeRoot'1718 v__n'2366 ->
                     (Option.Some ())
                 | _ ->
                     (Obj.magic
                        Obj.magic
                        (Option.None)))
            with
            | Option.Some () ->
                CNone'1611
            | Option.None ->
                (Obj.magic
                   (failwith
                      "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 273:4-273:9 ERROR: Reached a never term, which should be impossible in a well-typed program."))));;
let v__opIdI =
  fun v_input'1731 ->
    match
      Obj.magic
        (let v__target'2367 =
           v_input'1731
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2367
             with
             | CAtomI'1701 v__n'2368 ->
                 (let
                    CRec'2294 ({lid = v_id'2369})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2367
                  in
                  Option.Some (v_id'2369))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2378 ->
               (Option.Some v__x'2378)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     match
                       match
                         Obj.magic
                           Obj.magic
                           v__target'2367
                       with
                       | CInfixI'1702 v__n'2370 ->
                           (let
                              CRec'2297 ({lid = v_id'2371})
                            =
                              Obj.magic
                                Obj.magic
                                v__target'2367
                            in
                            Option.Some (v_id'2371))
                       | _ ->
                           (Obj.magic
                              Obj.magic
                              (Option.None))
                     with
                     | Option.Some v__x'2377 ->
                         (Option.Some v__x'2377)
                     | Option.None ->
                         (Obj.magic
                            Obj.magic
                            (match
                               match
                                 match
                                   Obj.magic
                                     Obj.magic
                                     v__target'2367
                                 with
                                 | CPrefixI'1703 v__n'2372 ->
                                     (let
                                        CRec'2296 ({lid = v_id'2373})
                                      =
                                        Obj.magic
                                          Obj.magic
                                          v__target'2367
                                      in
                                      Option.Some (v_id'2373))
                                 | _ ->
                                     (Obj.magic
                                        Obj.magic
                                        (Option.None))
                               with
                               | Option.Some v__x'2376 ->
                                   (Option.Some v__x'2376)
                               | Option.None ->
                                   (Obj.magic
                                      Obj.magic
                                      (match
                                         Obj.magic
                                           Obj.magic
                                           v__target'2367
                                       with
                                       | CPostfixI'1704 v__n'2374 ->
                                           (let
                                              CRec'2298 ({lid = v_id'2375})
                                            =
                                              Obj.magic
                                                Obj.magic
                                                v__target'2367
                                            in
                                            Option.Some (v_id'2375))
                                       | _ ->
                                           (Obj.magic
                                              Obj.magic
                                              (Option.None))))
                             with
                             | Option.Some (v_id'1732) ->
                                 (Option.Some (v_id'1732))
                             | Option.None ->
                                 (Obj.magic
                                    Obj.magic
                                    (Option.None))))
                   with
                   | Option.Some (v_id'1732) ->
                       (Option.Some (v_id'1732))
                   | Option.None ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_id'1732) ->
             (Option.Some (v_id'1732))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_id'1732) ->
        v_id'1732
    | Option.None ->
        (Obj.magic
           (failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 284:9-284:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__opIdP =
  fun v_node'1734 ->
    let v_defaultCase'2379 =
      fun nv_ ->
        failwith
          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 293:4-293:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
    in
    match
      Obj.magic
        v_node'1734
    with
    | CAtomP'1707 v_x'2380 ->
        (match
           Obj.magic
             (let v__target'2381 =
                Obj.magic
                  Obj.magic
                  v_node'1734
              in
              let
                CRec'2310 ({linput = v_input'2382})
              =
                Obj.magic
                  Obj.magic
                  v__target'2381
              in
              Option.Some (v_input'2382))
         with
         | Option.Some (v_input'1735) ->
             (Obj.magic
                v__opIdI
                v_input'1735)
         | Option.None ->
             (Obj.magic
                (Obj.magic
                   v_defaultCase'2379
                   ())))
    | CInfixP'1708 v_x'2383 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2384 =
                   Obj.magic
                     Obj.magic
                     v_node'1734
                 in
                 let
                   CRec'2283 ({linput = v_input'2385})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2384
                 in
                 Option.Some (v_input'2385))
            with
            | Option.Some (v_input'1736) ->
                (Obj.magic
                   v__opIdI
                   v_input'1736)
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2379
                      ()))))
    | CPrefixP'1709 v_x'2386 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2387 =
                   Obj.magic
                     Obj.magic
                     v_node'1734
                 in
                 let
                   CRec'2284 ({linput = v_input'2388})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2387
                 in
                 Option.Some (v_input'2388))
            with
            | Option.Some (v_input'1737) ->
                (Obj.magic
                   v__opIdI
                   v_input'1737)
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2379
                      ()))))
    | CPostfixP'1710 v_x'2389 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2390 =
                   Obj.magic
                     Obj.magic
                     v_node'1734
                 in
                 let
                   CRec'2303 ({linput = v_input'2391})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2390
                 in
                 Option.Some (v_input'2391))
            with
            | Option.Some (v_input'1738) ->
                (Obj.magic
                   v__opIdI
                   v_input'1738)
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2379
                      ()))))
    | _ ->
        (Obj.magic
           (v_defaultCase'2379
              ()));;
let v__opIdxP =
  fun v_node'1740 ->
    let v_defaultCase'2392 =
      fun nv_ ->
        failwith
          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 302:4-302:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
    in
    match
      Obj.magic
        v_node'1740
    with
    | CAtomP'1707 v_x'2393 ->
        (match
           Obj.magic
             (let v__target'2394 =
                Obj.magic
                  Obj.magic
                  v_node'1740
              in
              let
                CRec'2310 ({lidx = v_idx'2395})
              =
                Obj.magic
                  Obj.magic
                  v__target'2394
              in
              Option.Some (v_idx'2395))
         with
         | Option.Some (v_idx'1741) ->
             v_idx'1741
         | Option.None ->
             (Obj.magic
                (Obj.magic
                   v_defaultCase'2392
                   ())))
    | CInfixP'1708 v_x'2396 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2397 =
                   Obj.magic
                     Obj.magic
                     v_node'1740
                 in
                 let
                   CRec'2283 ({lidx = v_idx'2398})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2397
                 in
                 Option.Some (v_idx'2398))
            with
            | Option.Some (v_idx'1742) ->
                v_idx'1742
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2392
                      ()))))
    | CPrefixP'1709 v_x'2399 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2400 =
                   Obj.magic
                     Obj.magic
                     v_node'1740
                 in
                 let
                   CRec'2284 ({lidx = v_idx'2401})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2400
                 in
                 Option.Some (v_idx'2401))
            with
            | Option.Some (v_idx'1743) ->
                v_idx'1743
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2392
                      ()))))
    | CPostfixP'1710 v_x'2402 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2403 =
                   Obj.magic
                     Obj.magic
                     v_node'1740
                 in
                 let
                   CRec'2303 ({lidx = v_idx'2404})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2403
                 in
                 Option.Some (v_idx'2404))
            with
            | Option.Some (v_idx'1744) ->
                v_idx'1744
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2392
                      ()))))
    | _ ->
        (Obj.magic
           (v_defaultCase'2392
              ()));;
let v__opIdTD =
  fun v_data'1746 ->
    match
      Obj.magic
        (let v__target'2405 =
           v_data'1746
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2405
             with
             | CInfixT'1712 v__n'2406 ->
                 (let
                    CRec'2301 ({linput = v_input'2407})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2405
                  in
                  Option.Some (v_input'2407))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2410 ->
               (Option.Some v__x'2410)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     Obj.magic
                       Obj.magic
                       v__target'2405
                   with
                   | CPrefixT'1713 v__n'2408 ->
                       (let
                          CRec'2308 ({linput = v_input'2409})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2405
                        in
                        Option.Some (v_input'2409))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_input'1747) ->
             (Option.Some (v_input'1747))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_input'1747) ->
        (Obj.magic
           v__opIdI
           v_input'1747)
    | Option.None ->
        (Obj.magic
           (failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 308:4-308:9 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__opIdT =
  fun v_node'1749 ->
    let v_defaultCase'2411 =
      fun nv_ ->
        failwith
          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 316:4-316:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
    in
    match
      Obj.magic
        v_node'1749
    with
    | CTentativeLeaf'1716 v_x'2412 ->
        (match
           Obj.magic
             (let v__target'2413 =
                Obj.magic
                  Obj.magic
                  v_node'1749
              in
              let
                CRec'2311 ({lnode = v_node'2414})
              =
                Obj.magic
                  Obj.magic
                  v__target'2413
              in
              Option.Some (v_node'2414))
         with
         | Option.Some (v_node'1750) ->
             (Obj.magic
                v__opIdP
                v_node'1750)
         | Option.None ->
             (Obj.magic
                (Obj.magic
                   v_defaultCase'2411
                   ())))
    | CTentativeMid'1717 v_x'2415 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2416 =
                   Obj.magic
                     Obj.magic
                     v_node'1749
                 in
                 let
                   CRec'2309 ({ltentativeData = v_tentativeData'2417})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2416
                 in
                 Option.Some (v_tentativeData'2417))
            with
            | Option.Some (v_data'1751) ->
                (Obj.magic
                   v__opIdTD
                   v_data'1751)
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2411
                      ()))))
    | CTentativeRoot'1718 v_x'2418 ->
        (Obj.magic
           v__rootID)
    | _ ->
        (Obj.magic
           (v_defaultCase'2411
              ()));;
let v__addedNodesLeftChildren =
  fun v_node'1753 ->
    match
      Obj.magic
        (let v__target'2419 =
           v_node'1753
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2419
             with
             | CTentativeRoot'1718 v__n'2420 ->
                 (let
                    CRec'2290 ({laddedNodesLeftChildren = v_addedNodesLeftChildren'2421})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2419
                  in
                  Option.Some (v_addedNodesLeftChildren'2421))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2424 ->
               (Option.Some v__x'2424)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     Obj.magic
                       Obj.magic
                       v__target'2419
                   with
                   | CTentativeMid'1717 v__n'2422 ->
                       (let
                          CRec'2309 ({laddedNodesLeftChildren = v_addedNodesLeftChildren'2423})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2419
                        in
                        Option.Some (v_addedNodesLeftChildren'2423))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_x'1754) ->
             (Option.Some (v_x'1754))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_x'1754) ->
        v_x'1754
    | Option.None ->
        (Obj.magic
           (failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 323:9-323:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__addedNodesRightChildren =
  fun v_node'1756 ->
    match
      Obj.magic
        (let v__target'2425 =
           v_node'1756
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2425
             with
             | CTentativeRoot'1718 v__n'2426 ->
                 (let
                    CRec'2290 ({laddedNodesRightChildren = v_addedNodesRightChildren'2427})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2425
                  in
                  Option.Some (v_addedNodesRightChildren'2427))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2430 ->
               (Option.Some v__x'2430)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     Obj.magic
                       Obj.magic
                       v__target'2425
                   with
                   | CTentativeMid'1717 v__n'2428 ->
                       (let
                          CRec'2309 ({laddedNodesRightChildren = v_addedNodesRightChildren'2429})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2425
                        in
                        Option.Some (v_addedNodesRightChildren'2429))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_x'1757) ->
             (Option.Some (v_x'1757))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_x'1757) ->
        v_x'1757
    | Option.None ->
        (Obj.magic
           (failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 330:9-330:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v_breakableInAllowSet =
  fun v_id'1759 ->
    fun v_set'1760 ->
      let v_defaultCase'2431 =
        fun nv_ ->
          failwith
            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 339:4-339:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
      in
      match
        Obj.magic
          v_set'1760
      with
      | CAllowSet'1685 v_x'2432 ->
          (let v_s'1761 =
             Obj.magic
               Obj.magic
               v_x'2432
           in
           Obj.magic
             Boot.Intrinsics.Mmap.mem
             v_id'1759
             v_s'1761)
      | CDisallowSet'1686 v_x'2433 ->
          (Obj.magic
             (let v_s'1762 =
                Obj.magic
                  Obj.magic
                  v_x'2433
              in
              Obj.magic
                v_not
                (Obj.magic
                   Boot.Intrinsics.Mmap.mem
                   v_id'1759
                   v_s'1762)))
      | _ ->
          (Obj.magic
             (v_defaultCase'2431
                ()));;
let v_breakableInsertAllowSet =
  fun v_id'1764 ->
    fun v_set'1765 ->
      let v_defaultCase'2434 =
        fun nv_ ->
          failwith
            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 348:4-348:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
      in
      match
        Obj.magic
          v_set'1765
      with
      | CAllowSet'1685 v_x'2435 ->
          (let v_s'1766 =
             Obj.magic
               Obj.magic
               v_x'2435
           in
           CAllowSet'1685 (Obj.repr
              (Obj.magic
                 Boot.Intrinsics.Mmap.insert
                 v_id'1764
                 ()
                 v_s'1766)))
      | CDisallowSet'1686 v_x'2436 ->
          (Obj.magic
             (let v_s'1767 =
                Obj.magic
                  Obj.magic
                  v_x'2436
              in
              CDisallowSet'1686 (Obj.repr
                 (Obj.magic
                    Boot.Intrinsics.Mmap.remove
                    v_id'1764
                    ()
                    v_s'1767))))
      | _ ->
          (Obj.magic
             (v_defaultCase'2434
                ()));;
let v_breakableRemoveAllowSet =
  fun v_id'1769 ->
    fun v_set'1770 ->
      let v_defaultCase'2437 =
        fun nv_ ->
          failwith
            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 357:4-357:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
      in
      match
        Obj.magic
          v_set'1770
      with
      | CAllowSet'1685 v_x'2438 ->
          (let v_s'1771 =
             Obj.magic
               Obj.magic
               v_x'2438
           in
           CAllowSet'1685 (Obj.repr
              (Obj.magic
                 Boot.Intrinsics.Mmap.remove
                 v_id'1769
                 v_s'1771)))
      | CDisallowSet'1686 v_x'2439 ->
          (Obj.magic
             (let v_s'1772 =
                Obj.magic
                  Obj.magic
                  v_x'2439
              in
              CDisallowSet'1686 (Obj.repr
                 (Obj.magic
                    Boot.Intrinsics.Mmap.insert
                    v_id'1769
                    v_s'1772))))
      | _ ->
          (Obj.magic
             (v_defaultCase'2437
                ()));;
let v_breakableMapAllowSet =
  fun v_f'1774 ->
    fun v_newCmp'1775 ->
      fun v_s'1776 ->
        let v_convert'1780 =
          fun v_s'1777 ->
            Obj.magic
              v_mapFromSeq
              v_newCmp'1775
              (Obj.magic
                 Boot.Intrinsics.Mseq.map
                 (fun v_x'1778 ->
                    CRec'2315 { l0 =
                        (Obj.repr
                          (Obj.magic
                             v_f'1774
                             (let
                                CRec'2315 ({l0 = v_X'1779})
                              =
                                Obj.magic
                                  v_x'1778
                              in
                              Obj.magic
                                v_X'1779)));
                      l1 =
                        (Obj.repr
                          ()) })
                 (Obj.magic
                    Boot.Intrinsics.Mmap.bindings
                    v_s'1777))
        in
        let v_defaultCase'2440 =
          fun nv_ ->
            failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 368:4-368:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
        in
        match
          Obj.magic
            v_s'1776
        with
        | CAllowSet'1685 v_x'2441 ->
            (let v_s'1781 =
               Obj.magic
                 Obj.magic
                 v_x'2441
             in
             CAllowSet'1685 (Obj.repr
                (Obj.magic
                   v_convert'1780
                   v_s'1781)))
        | CDisallowSet'1686 v_x'2442 ->
            (Obj.magic
               (let v_s'1782 =
                  Obj.magic
                    Obj.magic
                    v_x'2442
                in
                CDisallowSet'1686 (Obj.repr
                   (Obj.magic
                      v_convert'1780
                      v_s'1782))))
        | _ ->
            (Obj.magic
               (v_defaultCase'2440
                  ()));;
let v_breakableGenGrammar =
  fun v_cmp'1784 ->
    fun v_grammar'1785 ->
      let v_nOpId'1786 =
        Obj.magic
          ref
          v__firstOpId
      in
      let v_newOpId'1790 =
        fun v_'1787 ->
          let v_res'1788 =
            Obj.magic
              (!)
              v_nOpId'1786
          in
          let v_'1789 =
            Obj.magic
              (:=)
              v_nOpId'1786
              (Obj.magic
                 v__nextOpId
                 v_res'1788)
          in
          v_res'1788
      in
      let v_label'1796 =
        fun v_prod'1791 ->
          let v_defaultCase'2443 =
            fun nv_ ->
              failwith
                "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 389:8-389:13 ERROR: Reached a never term, which should be impossible in a well-typed program."
          in
          match
            Obj.magic
              v_prod'1791
          with
          | CBreakableAtom'1688 v_x'2444 ->
              (match
                 Obj.magic
                   (let v__target'2445 =
                      Obj.magic
                        Obj.magic
                        v_prod'1791
                    in
                    let
                      CRec'2270 ({llabel = v_label'2446})
                    =
                      Obj.magic
                        Obj.magic
                        v__target'2445
                    in
                    Option.Some (v_label'2446))
               with
               | Option.Some (v_label'1792) ->
                   v_label'1792
               | Option.None ->
                   (Obj.magic
                      (Obj.magic
                         v_defaultCase'2443
                         ())))
          | CBreakableInfix'1689 v_x'2447 ->
              (Obj.magic
                 (match
                    Obj.magic
                      (let v__target'2448 =
                         Obj.magic
                           Obj.magic
                           v_prod'1791
                       in
                       let
                         CRec'2271 ({llabel = v_label'2449})
                       =
                         Obj.magic
                           Obj.magic
                           v__target'2448
                       in
                       Option.Some (v_label'2449))
                  with
                  | Option.Some (v_label'1794) ->
                      v_label'1794
                  | Option.None ->
                      (Obj.magic
                         (Obj.magic
                            v_defaultCase'2443
                            ()))))
          | CBreakablePrefix'1690 v_x'2450 ->
              (Obj.magic
                 (match
                    Obj.magic
                      (let v__target'2451 =
                         Obj.magic
                           Obj.magic
                           v_prod'1791
                       in
                       let
                         CRec'2272 ({llabel = v_label'2452})
                       =
                         Obj.magic
                           Obj.magic
                           v__target'2451
                       in
                       Option.Some (v_label'2452))
                  with
                  | Option.Some (v_label'1793) ->
                      v_label'1793
                  | Option.None ->
                      (Obj.magic
                         (Obj.magic
                            v_defaultCase'2443
                            ()))))
          | CBreakablePostfix'1691 v_x'2453 ->
              (Obj.magic
                 (match
                    Obj.magic
                      (let v__target'2454 =
                         Obj.magic
                           Obj.magic
                           v_prod'1791
                       in
                       let
                         CRec'2273 ({llabel = v_label'2455})
                       =
                         Obj.magic
                           Obj.magic
                           v__target'2454
                       in
                       Option.Some (v_label'2455))
                  with
                  | Option.Some (v_label'1795) ->
                      v_label'1795
                  | Option.None ->
                      (Obj.magic
                         (Obj.magic
                            v_defaultCase'2443
                            ()))))
          | _ ->
              (Obj.magic
                 (v_defaultCase'2443
                    ()))
      in
      let v_prodLabelToOpId'1799 =
        Obj.magic
          v_mapFromSeq
          v_cmp'1784
          (Obj.magic
             Boot.Intrinsics.Mseq.map
             (fun v_prod'1797 ->
                CRec'2315 { l0 =
                    (Obj.repr
                      (Obj.magic
                         v_label'1796
                         v_prod'1797));
                  l1 =
                    (Obj.repr
                      (Obj.magic
                         v_newOpId'1790
                         ())) })
             (let
                CRec'2276 ({lproductions = v_X'1798})
              =
                Obj.magic
                  v_grammar'1785
              in
              Obj.magic
                v_X'1798))
      in
      let v_toOpId'1801 =
        fun v_label'1800 ->
          Obj.magic
            Boot.Intrinsics.Mmap.find
            v_label'1800
            v_prodLabelToOpId'1799
      in
      let v_groupingByRightOp'1812 =
        Obj.magic
          Boot.Intrinsics.Mseq.Helpers.fold_left
          (fun v_acc'1802 ->
             fun v_grouping'1803 ->
               match
                 Obj.magic
                   (let v__target'2456 =
                      v_grouping'1803
                    in
                    let
                      CRec'2315 ({l0 = v_0'2457;l1 = v_1'2458})
                    =
                      Obj.magic
                        Obj.magic
                        v__target'2456
                    in
                    let
                      CRec'2315 ({l0 = v_0'2459;l1 = v_1'2460})
                    =
                      Obj.magic
                        Obj.magic
                        v_0'2457
                    in
                    Option.Some (v_0'2459, v_1'2460, v_1'2458))
               with
               | Option.Some (v_lplab'1804, v_rplab'1805, v_grouping'1806) ->
                   (let v_lid'1807 =
                      Obj.magic
                        v_toOpId'1801
                        v_lplab'1804
                    in
                    let v_rid'1808 =
                      Obj.magic
                        v_toOpId'1801
                        v_rplab'1805
                    in
                    let v_prev'1810 =
                      match
                        Obj.magic
                          (let v__target'2461 =
                             Obj.magic
                               v_mapLookup
                               v_rid'1808
                               v_acc'1802
                           in
                           match
                             Obj.magic
                               Obj.magic
                               v__target'2461
                           with
                           | CSome'1610 v__n'2462 ->
                               (Option.Some (v__n'2462))
                           | _ ->
                               (Obj.magic
                                  Obj.magic
                                  (Option.None)))
                      with
                      | Option.Some (v_prev'1809) ->
                          v_prev'1809
                      | Option.None ->
                          (Obj.magic
                             (Obj.magic
                                Boot.Intrinsics.Mmap.empty
                                v__cmpOpId))
                    in
                    Obj.magic
                      Boot.Intrinsics.Mmap.insert
                      v_rid'1808
                      (Obj.magic
                         Boot.Intrinsics.Mmap.insert
                         v_lid'1807
                         v_grouping'1806
                         v_prev'1810)
                      v_acc'1802)
               | Option.None ->
                   (Obj.magic
                      (failwith
                         "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 411:15-411:20 ERROR: Reached a never term, which should be impossible in a well-typed program.")))
          (Obj.magic
             Boot.Intrinsics.Mmap.empty
             v__cmpOpId)
          (let
             CRec'2276 ({lprecedences = v_X'1811})
           =
             Obj.magic
               v_grammar'1785
           in
           Obj.magic
             v_X'1811)
      in
      let v_getGroupingByRight'1815 =
        fun v_opid'1813 ->
          match
            Obj.magic
              (let v__target'2463 =
                 Obj.magic
                   v_mapLookup
                   v_opid'1813
                   v_groupingByRightOp'1812
               in
               match
                 Obj.magic
                   Obj.magic
                   v__target'2463
               with
               | CSome'1610 v__n'2464 ->
                   (Option.Some (v__n'2464))
               | _ ->
                   (Obj.magic
                      Obj.magic
                      (Option.None)))
          with
          | Option.Some (v_res'1814) ->
              v_res'1814
          | Option.None ->
              (Obj.magic
                 (Obj.magic
                    Boot.Intrinsics.Mmap.empty
                    v__cmpOpId))
      in
      let v_atoms'1816 =
        Obj.magic
          ref
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |])
      in
      let v_prefixes'1817 =
        Obj.magic
          ref
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |])
      in
      let v_infixes'1818 =
        Obj.magic
          ref
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |])
      in
      let v_postfixes'1819 =
        Obj.magic
          ref
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |])
      in
      let v_updateRef'1822 =
        fun v_ref'1820 ->
          fun v_f'1821 ->
            Obj.magic
              (:=)
              v_ref'1820
              (Obj.magic
                 v_f'1821
                 (Obj.magic
                    (!)
                    v_ref'1820))
      in
      let v_'1841 =
        Obj.magic
          v_for_
          (let
             CRec'2276 ({lproductions = v_X'1823})
           =
             Obj.magic
               v_grammar'1785
           in
           Obj.magic
             v_X'1823)
          (fun v_prod'1824 ->
             let v_label'1825 =
               Obj.magic
                 v_label'1796
                 v_prod'1824
             in
             let v_id'1826 =
               Obj.magic
                 v_toOpId'1801
                 v_label'1825
             in
             let v_defaultCase'2465 =
               fun nv_ ->
                 failwith
                   "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 445:13-445:18 ERROR: Reached a never term, which should be impossible in a well-typed program."
             in
             match
               Obj.magic
                 v_prod'1824
             with
             | CBreakableAtom'1688 v_x'2466 ->
                 (match
                    Obj.magic
                      (let v__target'2467 =
                         Obj.magic
                           Obj.magic
                           v_prod'1824
                       in
                       let
                         CRec'2270 ({lconstruct = v_construct'2468})
                       =
                         Obj.magic
                           Obj.magic
                           v__target'2467
                       in
                       Option.Some (v_construct'2468))
                  with
                  | Option.Some (v_construct'1827) ->
                      (Obj.magic
                         v_updateRef'1822
                         v_atoms'1816
                         (Obj.magic
                            Boot.Intrinsics.Mseq.cons
                            (CRec'2315 { l0 =
                                 (Obj.repr
                                   v_label'1825);
                               l1 =
                                 (Obj.repr
                                   (CAtomI'1701 { lconstruct =
                                        (Obj.repr
                                          v_construct'1827);
                                      lid =
                                        (Obj.repr
                                          v_id'1826) })) })))
                  | Option.None ->
                      (Obj.magic
                         (Obj.magic
                            v_defaultCase'2465
                            ())))
             | CBreakableInfix'1689 v_x'2469 ->
                 (Obj.magic
                    (match
                       Obj.magic
                         (let v__target'2470 =
                            Obj.magic
                              Obj.magic
                              v_prod'1824
                          in
                          let
                            CRec'2271 ({lconstruct = v_construct'2471;lleftAllow = v_leftAllow'2472;lrightAllow = v_rightAllow'2473})
                          =
                            Obj.magic
                              Obj.magic
                              v__target'2470
                          in
                          Option.Some (v_construct'2471, v_leftAllow'2472, v_rightAllow'2473))
                     with
                     | Option.Some (v_c'1831, v_l'1832, v_r'1833) ->
                         (let v_l'1834 =
                            Obj.magic
                              v_breakableMapAllowSet
                              v_toOpId'1801
                              v__cmpOpId
                              v_l'1832
                          in
                          let v_r'1835 =
                            Obj.magic
                              v_breakableMapAllowSet
                              v_toOpId'1801
                              v__cmpOpId
                              v_r'1833
                          in
                          let v_p'1836 =
                            Obj.magic
                              v_getGroupingByRight'1815
                              v_id'1826
                          in
                          Obj.magic
                            v_updateRef'1822
                            v_infixes'1818
                            (Obj.magic
                               Boot.Intrinsics.Mseq.cons
                               (CRec'2315 { l0 =
                                    (Obj.repr
                                      v_label'1825);
                                  l1 =
                                    (Obj.repr
                                      (CInfixI'1702 { lconstruct =
                                           (Obj.repr
                                             v_c'1831);
                                         lleftAllow =
                                           (Obj.repr
                                             v_l'1834);
                                         lrightAllow =
                                           (Obj.repr
                                             v_r'1835);
                                         lid =
                                           (Obj.repr
                                             v_id'1826);
                                         lprecWhenThisIsRight =
                                           (Obj.repr
                                             v_p'1836) })) })))
                     | Option.None ->
                         (Obj.magic
                            (Obj.magic
                               v_defaultCase'2465
                               ()))))
             | CBreakablePrefix'1690 v_x'2474 ->
                 (Obj.magic
                    (match
                       Obj.magic
                         (let v__target'2475 =
                            Obj.magic
                              Obj.magic
                              v_prod'1824
                          in
                          let
                            CRec'2272 ({lconstruct = v_construct'2476;lrightAllow = v_rightAllow'2477})
                          =
                            Obj.magic
                              Obj.magic
                              v__target'2475
                          in
                          Option.Some (v_construct'2476, v_rightAllow'2477))
                     with
                     | Option.Some (v_c'1828, v_r'1829) ->
                         (let v_r'1830 =
                            Obj.magic
                              v_breakableMapAllowSet
                              v_toOpId'1801
                              v__cmpOpId
                              v_r'1829
                          in
                          Obj.magic
                            v_updateRef'1822
                            v_prefixes'1817
                            (Obj.magic
                               Boot.Intrinsics.Mseq.cons
                               (CRec'2315 { l0 =
                                    (Obj.repr
                                      v_label'1825);
                                  l1 =
                                    (Obj.repr
                                      (CPrefixI'1703 { lconstruct =
                                           (Obj.repr
                                             v_c'1828);
                                         lrightAllow =
                                           (Obj.repr
                                             v_r'1830);
                                         lid =
                                           (Obj.repr
                                             v_id'1826) })) })))
                     | Option.None ->
                         (Obj.magic
                            (Obj.magic
                               v_defaultCase'2465
                               ()))))
             | CBreakablePostfix'1691 v_x'2478 ->
                 (Obj.magic
                    (match
                       Obj.magic
                         (let v__target'2479 =
                            Obj.magic
                              Obj.magic
                              v_prod'1824
                          in
                          let
                            CRec'2273 ({lconstruct = v_construct'2480;lleftAllow = v_leftAllow'2481})
                          =
                            Obj.magic
                              Obj.magic
                              v__target'2479
                          in
                          Option.Some (v_construct'2480, v_leftAllow'2481))
                     with
                     | Option.Some (v_c'1837, v_l'1838) ->
                         (let v_l'1839 =
                            Obj.magic
                              v_breakableMapAllowSet
                              v_toOpId'1801
                              v__cmpOpId
                              v_l'1838
                          in
                          let v_p'1840 =
                            Obj.magic
                              v_getGroupingByRight'1815
                              v_id'1826
                          in
                          Obj.magic
                            v_updateRef'1822
                            v_postfixes'1819
                            (Obj.magic
                               Boot.Intrinsics.Mseq.cons
                               (CRec'2315 { l0 =
                                    (Obj.repr
                                      v_label'1825);
                                  l1 =
                                    (Obj.repr
                                      (CPostfixI'1704 { lconstruct =
                                           (Obj.repr
                                             v_c'1837);
                                         lleftAllow =
                                           (Obj.repr
                                             v_l'1839);
                                         lid =
                                           (Obj.repr
                                             v_id'1826);
                                         lprecWhenThisIsRight =
                                           (Obj.repr
                                             v_p'1840) })) })))
                     | Option.None ->
                         (Obj.magic
                            (Obj.magic
                               v_defaultCase'2465
                               ()))))
             | _ ->
                 (Obj.magic
                    (v_defaultCase'2465
                       ())))
      in
      CRec'2281 { latoms =
          (Obj.repr
            (Obj.magic
               v_mapFromSeq
               v_cmp'1784
               (Obj.magic
                  (!)
                  v_atoms'1816)));
        lprefixes =
          (Obj.repr
            (Obj.magic
               v_mapFromSeq
               v_cmp'1784
               (Obj.magic
                  (!)
                  v_prefixes'1817)));
        linfixes =
          (Obj.repr
            (Obj.magic
               v_mapFromSeq
               v_cmp'1784
               (Obj.magic
                  (!)
                  v_infixes'1818)));
        lpostfixes =
          (Obj.repr
            (Obj.magic
               v_mapFromSeq
               v_cmp'1784
               (Obj.magic
                  (!)
                  v_postfixes'1819))) };;
let v_breakableInitState =
  fun v_grammar'1843 ->
    let v_timestep'1844 =
      Obj.magic
        ref
        v__firstTimeStep
    in
    let v_nextIdx'1845 =
      Obj.magic
        ref
        0
    in
    let v_addedLeft'1846 =
      Obj.magic
        ref
        (CRec'2315 { l0 =
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
    let v_addedRight'1847 =
      Obj.magic
        ref
        (CRec'2315 { l0 =
             (Obj.repr
               v__firstTimeStep);
           l1 =
             (Obj.repr
               (Obj.magic
                  Boot.Intrinsics.Mseq.Helpers.of_array
                  [|  |])) })
    in
    CRec'2291 { ltimestep =
        (Obj.repr
          v_timestep'1844);
      lnextIdx =
        (Obj.repr
          v_nextIdx'1845);
      lfrontier =
        (Obj.repr
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [| (Obj.magic
                 (CTentativeRoot'1718 { laddedNodesLeftChildren =
                      (Obj.repr
                        v_addedLeft'1846);
                    laddedNodesRightChildren =
                      (Obj.repr
                        v_addedRight'1847) })) |])) };;
let rec v__maxDistanceFromRoot =
    fun v_n'1850 ->
      let v_defaultCase'2482 =
        fun nv_ ->
          let v_'1854 =
            Obj.magic
              v_dprintLn
              v_n'1850
          in
          failwith
            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 473:4-473:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
      in
      match
        Obj.magic
          v_n'1850
      with
      | CTentativeLeaf'1716 v_x'2483 ->
          (match
             Obj.magic
               (let v__target'2484 =
                  Obj.magic
                    Obj.magic
                    v_n'1850
                in
                let
                  CRec'2311 ({lparents = v_parents'2485})
                =
                  Obj.magic
                    Obj.magic
                    v__target'2484
                in
                Option.Some (v_parents'2485))
           with
           | Option.Some (v_parents'1852) ->
               (Obj.magic
                  v_maxOrElse
                  (fun v_'1853 ->
                     0)
                  Int.sub
                  (Obj.magic
                     Boot.Intrinsics.Mseq.map
                     v__maxDistanceFromRoot
                     v_parents'1852))
           | Option.None ->
               (Obj.magic
                  (Obj.magic
                     v_defaultCase'2482
                     ())))
      | CTentativeMid'1717 v_x'2486 ->
          (Obj.magic
             (match
                Obj.magic
                  (let v__target'2487 =
                     Obj.magic
                       Obj.magic
                       v_n'1850
                   in
                   let
                     CRec'2309 ({lmaxDistanceFromRoot = v_maxDistanceFromRoot'2488})
                   =
                     Obj.magic
                       Obj.magic
                       v__target'2487
                   in
                   Option.Some (v_maxDistanceFromRoot'2488))
              with
              | Option.Some (v_r'1851) ->
                  v_r'1851
              | Option.None ->
                  (Obj.magic
                     (Obj.magic
                        v_defaultCase'2482
                        ()))))
      | CTentativeRoot'1718 v_x'2489 ->
          (Obj.magic
             0)
      | _ ->
          (Obj.magic
             (v_defaultCase'2482
                ()));;
let v__shallowAllowedLeft =
  fun v_parent'1855 ->
    fun v_child'1856 ->
      match
        Obj.magic
          (let v__target'2490 =
             v_child'1856
           in
           match
             Obj.magic
               Obj.magic
               v__target'2490
           with
           | CTentativeLeaf'1716 v__n'2491 ->
               (let
                  CRec'2311 ({lnode = v_node'2492})
                =
                  Obj.magic
                    Obj.magic
                    v__target'2490
                in
                Option.Some (v_node'2492))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_node'1857) ->
          (match
             Obj.magic
               (let v__target'2493 =
                  v_parent'1855
                in
                match
                  match
                    match
                      Obj.magic
                        Obj.magic
                        v__target'2493
                    with
                    | CInfixI'1702 v__n'2494 ->
                        (let
                           CRec'2297 ({lleftAllow = v_leftAllow'2495})
                         =
                           Obj.magic
                             Obj.magic
                             v__target'2493
                         in
                         Option.Some (v_leftAllow'2495))
                    | _ ->
                        (Obj.magic
                           Obj.magic
                           (Option.None))
                  with
                  | Option.Some v__x'2498 ->
                      (Option.Some v__x'2498)
                  | Option.None ->
                      (Obj.magic
                         Obj.magic
                         (match
                            Obj.magic
                              Obj.magic
                              v__target'2493
                          with
                          | CPostfixI'1704 v__n'2496 ->
                              (let
                                 CRec'2298 ({lleftAllow = v_leftAllow'2497})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2493
                               in
                               Option.Some (v_leftAllow'2497))
                          | _ ->
                              (Obj.magic
                                 Obj.magic
                                 (Option.None))))
                with
                | Option.Some (v_s'1858) ->
                    (Option.Some (v_s'1858))
                | Option.None ->
                    (Obj.magic
                       Obj.magic
                       (Option.None)))
           with
           | Option.Some (v_s'1858) ->
               (if
                  Obj.magic
                    (Obj.magic
                       v_breakableInAllowSet
                       (Obj.magic
                          v__opIdP
                          v_node'1857)
                       v_s'1858)
                then
                  CSome'1610 (Obj.repr
                     v_node'1857)
                else
                  Obj.magic
                    CNone'1611)
           | Option.None ->
               (Obj.magic
                  (failwith
                     "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 484:11-484:16 ERROR: Reached a never term, which should be impossible in a well-typed program.")))
      | Option.None ->
          (Obj.magic
             (failwith
                "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 485:9-485:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__shallowAllowedRight =
  fun v_parent'1860 ->
    fun v_child'1861 ->
      match
        Obj.magic
          (let v__target'2499 =
             v_child'1861
           in
           match
             Obj.magic
               Obj.magic
               v__target'2499
           with
           | CTentativeLeaf'1716 v__n'2500 ->
               (let
                  CRec'2311 ({lnode = v_node'2501})
                =
                  Obj.magic
                    Obj.magic
                    v__target'2499
                in
                Option.Some (v_node'2501))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_node'1862) ->
          (let v_defaultCase'2502 =
             fun nv_ ->
               let v_'1864 =
                 Obj.magic
                   v_dprintLn
                   v_parent'1860
               in
               failwith
                 "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 496:28-496:33 ERROR: Reached a never term, which should be impossible in a well-typed program."
           in
           match
             Obj.magic
               v_parent'1860
           with
           | CTentativeMid'1717 v_x'2503 ->
               (match
                  Obj.magic
                    (let v__target'2504 =
                       Obj.magic
                         Obj.magic
                         v_parent'1860
                     in
                     let
                       CRec'2309 ({ltentativeData = v_tentativeData'2505})
                     =
                       Obj.magic
                         Obj.magic
                         v__target'2504
                     in
                     match
                       match
                         match
                           Obj.magic
                             Obj.magic
                             v_tentativeData'2505
                         with
                         | CInfixT'1712 v__n'2506 ->
                             (let
                                CRec'2301 ({linput = v_input'2507})
                              =
                                Obj.magic
                                  Obj.magic
                                  v_tentativeData'2505
                              in
                              match
                                Obj.magic
                                  Obj.magic
                                  v_input'2507
                              with
                              | CInfixI'1702 v__n'2508 ->
                                  (let
                                     CRec'2297 ({lrightAllow = v_rightAllow'2509})
                                   =
                                     Obj.magic
                                       Obj.magic
                                       v_input'2507
                                   in
                                   Option.Some (v_rightAllow'2509))
                              | _ ->
                                  (Obj.magic
                                     Obj.magic
                                     (Option.None)))
                         | _ ->
                             (Obj.magic
                                Obj.magic
                                (Option.None))
                       with
                       | Option.Some v__x'2514 ->
                           (Option.Some v__x'2514)
                       | Option.None ->
                           (Obj.magic
                              Obj.magic
                              (match
                                 Obj.magic
                                   Obj.magic
                                   v_tentativeData'2505
                               with
                               | CPrefixT'1713 v__n'2510 ->
                                   (let
                                      CRec'2308 ({linput = v_input'2511})
                                    =
                                      Obj.magic
                                        Obj.magic
                                        v_tentativeData'2505
                                    in
                                    match
                                      Obj.magic
                                        Obj.magic
                                        v_input'2511
                                    with
                                    | CPrefixI'1703 v__n'2512 ->
                                        (let
                                           CRec'2296 ({lrightAllow = v_rightAllow'2513})
                                         =
                                           Obj.magic
                                             Obj.magic
                                             v_input'2511
                                         in
                                         Option.Some (v_rightAllow'2513))
                                    | _ ->
                                        (Obj.magic
                                           Obj.magic
                                           (Option.None)))
                               | _ ->
                                   (Obj.magic
                                      Obj.magic
                                      (Option.None))))
                     with
                     | Option.Some (v_s'1863) ->
                         (Option.Some (v_s'1863))
                     | Option.None ->
                         (Obj.magic
                            Obj.magic
                            (Option.None)))
                with
                | Option.Some (v_s'1863) ->
                    (if
                       Obj.magic
                         (Obj.magic
                            v_breakableInAllowSet
                            (Obj.magic
                               v__opIdP
                               v_node'1862)
                            v_s'1863)
                     then
                       CSome'1610 (Obj.repr
                          v_node'1862)
                     else
                       Obj.magic
                         CNone'1611)
                | Option.None ->
                    (Obj.magic
                       (Obj.magic
                          v_defaultCase'2502
                          ())))
           | CTentativeRoot'1718 v_x'2515 ->
               (Obj.magic
                  (CSome'1610 (Obj.repr
                      v_node'1862)))
           | _ ->
               (Obj.magic
                  (v_defaultCase'2502
                     ())))
      | Option.None ->
          (Obj.magic
             (failwith
                "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 497:9-497:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__addRightChildren =
  fun v_st'1866 ->
    fun v_parent'1867 ->
      fun v_children'1868 ->
        let v_defaultCase'2516 =
          fun nv_ ->
            failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 516:9-516:14 ERROR: Reached a never term, which should be impossible in a well-typed program."
        in
        match
          Obj.magic
            v_parent'1867
        with
        | CTentativeMid'1717 v_x'2517 ->
            (match
               Obj.magic
                 (let v__target'2518 =
                    Obj.magic
                      Obj.magic
                      v_parent'1867
                  in
                  let
                    CRec'2309 ({lparents = v_parents'2519;ltentativeData = v_tentativeData'2520})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2518
                  in
                  Option.Some (v_parents'2519, v_tentativeData'2520))
             with
             | Option.Some (v_parents'1869, v_data'1870) ->
                 (let v_id'1871 =
                    Obj.magic
                      v__uniqueID
                      ()
                  in
                  let v_node'1879 =
                    let v_defaultCase'2521 =
                      fun nv_ ->
                        failwith
                          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 512:13-512:18 ERROR: Reached a never term, which should be impossible in a well-typed program."
                    in
                    match
                      Obj.magic
                        v_data'1870
                    with
                    | CInfixT'1712 v_x'2522 ->
                        (match
                           Obj.magic
                             (let v__target'2523 =
                                Obj.magic
                                  Obj.magic
                                  v_data'1870
                              in
                              let
                                CRec'2301 ({lidx = v_idx'2524;linput = v_input'2525;lself = v_self'2526;lleftChildAlts = v_leftChildAlts'2527})
                              =
                                Obj.magic
                                  Obj.magic
                                  v__target'2523
                              in
                              Option.Some (v_idx'2524, v_input'2525, v_self'2526, v_leftChildAlts'2527))
                         with
                         | Option.Some (v_idx'1872, v_input'1873, v_self'1874, v_l'1875) ->
                             (CInfixP'1708 { lid =
                                  (Obj.repr
                                    v_id'1871);
                                lidx =
                                  (Obj.repr
                                    v_idx'1872);
                                linput =
                                  (Obj.repr
                                    v_input'1873);
                                lself =
                                  (Obj.repr
                                    v_self'1874);
                                lleftChildAlts =
                                  (Obj.repr
                                    v_l'1875);
                                lrightChildAlts =
                                  (Obj.repr
                                    v_children'1868) })
                         | Option.None ->
                             (Obj.magic
                                (Obj.magic
                                   v_defaultCase'2521
                                   ())))
                    | CPrefixT'1713 v_x'2528 ->
                        (Obj.magic
                           (match
                              Obj.magic
                                (let v__target'2529 =
                                   Obj.magic
                                     Obj.magic
                                     v_data'1870
                                 in
                                 let
                                   CRec'2308 ({lidx = v_idx'2530;linput = v_input'2531;lself = v_self'2532})
                                 =
                                   Obj.magic
                                     Obj.magic
                                     v__target'2529
                                 in
                                 Option.Some (v_idx'2530, v_input'2531, v_self'2532))
                            with
                            | Option.Some (v_idx'1876, v_input'1877, v_self'1878) ->
                                (CPrefixP'1709 { lid =
                                     (Obj.repr
                                       v_id'1871);
                                   lidx =
                                     (Obj.repr
                                       v_idx'1876);
                                   linput =
                                     (Obj.repr
                                       v_input'1877);
                                   lself =
                                     (Obj.repr
                                       v_self'1878);
                                   lrightChildAlts =
                                     (Obj.repr
                                       v_children'1868) })
                            | Option.None ->
                                (Obj.magic
                                   (Obj.magic
                                      v_defaultCase'2521
                                      ()))))
                    | _ ->
                        (Obj.magic
                           (v_defaultCase'2521
                              ()))
                  in
                  CTentativeLeaf'1716 { lparents =
                      (Obj.repr
                        v_parents'1869);
                    lnode =
                      (Obj.repr
                        v_node'1879) })
             | Option.None ->
                 (Obj.magic
                    (Obj.magic
                       v_defaultCase'2516
                       ())))
        | CTentativeRoot'1718 v_x'2533 ->
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
               (v_defaultCase'2516
                  ()));;
let v__addLeftChildren =
  fun v_st'1881 ->
    fun v_input'1882 ->
      fun v_self'1883 ->
        fun v_leftChildren'1884 ->
          fun v_parents'1885 ->
            let v_idx'1887 =
              Obj.magic
                (!)
                (let
                   CRec'2291 ({lnextIdx = v_X'1886})
                 =
                   Obj.magic
                     v_st'1881
                 in
                 Obj.magic
                   v_X'1886)
            in
            let v_defaultCase'2534 =
              fun nv_ ->
                failwith
                  "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 544:9-544:14 ERROR: Reached a never term, which should be impossible in a well-typed program."
            in
            match
              Obj.magic
                v_input'1882
            with
            | CInfixI'1702 v_x'2535 ->
                (let v_time'1889 =
                   Obj.magic
                     (!)
                     (let
                        CRec'2291 ({ltimestep = v_X'1888})
                      =
                        Obj.magic
                          v_st'1881
                      in
                      Obj.magic
                        v_X'1888)
                 in
                 let v_addedLeft'1890 =
                   Obj.magic
                     ref
                     (CRec'2315 { l0 =
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
                 let v_addedRight'1891 =
                   Obj.magic
                     ref
                     (CRec'2315 { l0 =
                          (Obj.repr
                            v__firstTimeStep);
                        l1 =
                          (Obj.repr
                            (Obj.magic
                               Boot.Intrinsics.Mseq.Helpers.of_array
                               [|  |])) })
                 in
                 CTentativeMid'1717 { lparents =
                     (Obj.repr
                       v_parents'1885);
                   laddedNodesLeftChildren =
                     (Obj.repr
                       v_addedLeft'1890);
                   laddedNodesRightChildren =
                     (Obj.repr
                       v_addedRight'1891);
                   ltentativeData =
                     (Obj.repr
                       (CInfixT'1712 { lidx =
                            (Obj.repr
                              v_idx'1887);
                          linput =
                            (Obj.repr
                              v_input'1882);
                          lself =
                            (Obj.repr
                              v_self'1883);
                          lleftChildAlts =
                            (Obj.repr
                              v_leftChildren'1884) }));
                   lmaxDistanceFromRoot =
                     (Obj.repr
                       (Obj.magic
                          Int.add
                          1
                          (Obj.magic
                             v_maxOrElse
                             (fun v_'1892 ->
                                0)
                             Int.sub
                             (Obj.magic
                                Boot.Intrinsics.Mseq.map
                                v__maxDistanceFromRoot
                                v_parents'1885)))) })
            | CPostfixI'1704 v_x'2536 ->
                (Obj.magic
                   (let v_id'1893 =
                      Obj.magic
                        v__uniqueID
                        ()
                    in
                    CTentativeLeaf'1716 { lparents =
                        (Obj.repr
                          v_parents'1885);
                      lnode =
                        (Obj.repr
                          (CPostfixP'1710 { lid =
                               (Obj.repr
                                 v_id'1893);
                             lidx =
                               (Obj.repr
                                 v_idx'1887);
                             linput =
                               (Obj.repr
                                 v_input'1882);
                             lself =
                               (Obj.repr
                                 v_self'1883);
                             lleftChildAlts =
                               (Obj.repr
                                 v_leftChildren'1884) })) }))
            | _ ->
                (Obj.magic
                   (v_defaultCase'2534
                      ()));;
let v__addRightChildToParent =
  fun v_time'1895 ->
    fun v_child'1896 ->
      fun v_parent'1897 ->
        let v_target'1898 =
          Obj.magic
            v__addedNodesRightChildren
            v_parent'1897
        in
        match
          Obj.magic
            (let v__target'2537 =
               Obj.magic
                 (!)
                 v_target'1898
             in
             let
               CRec'2315 ({l0 = v_0'2538;l1 = v_1'2539})
             =
               Obj.magic
                 Obj.magic
                 v__target'2537
             in
             Option.Some (v_0'2538, v_1'2539))
        with
        | Option.Some (v_lastUpdate'1899, v_prev'1900) ->
            (if
               Obj.magic
                 (Obj.magic
                    v__isBefore
                    v_lastUpdate'1899
                    v_time'1895)
             then
               let v_'1901 =
                 Obj.magic
                   (:=)
                   v_target'1898
                   (CRec'2315 { l0 =
                        (Obj.repr
                          v_time'1895);
                      l1 =
                        (Obj.repr
                          (Obj.magic
                             Boot.Intrinsics.Mseq.Helpers.of_array
                             [| (Obj.magic
                                 v_child'1896) |])) })
               in
               CSome'1610 (Obj.repr
                  v_parent'1897)
             else
               Obj.magic
                 (let v_'1902 =
                    Obj.magic
                      (:=)
                      v_target'1898
                      (CRec'2315 { l0 =
                           (Obj.repr
                             v_time'1895);
                         l1 =
                           (Obj.repr
                             (Obj.magic
                                Boot.Intrinsics.Mseq.cons
                                v_child'1896
                                v_prev'1900)) })
                  in
                  CNone'1611))
        | Option.None ->
            (Obj.magic
               (failwith
                  "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 560:9-560:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__addLeftChildToParent =
  fun v_time'1904 ->
    fun v_child'1905 ->
      fun v_parents'1906 ->
        match
          Obj.magic
            (let v__target'2540 =
               v_parents'1906
             in
             if
               Obj.magic
                 ((<) : int -> int -> bool)
                 (Obj.magic
                    Boot.Intrinsics.Mseq.length
                    v__target'2540)
                 1
             then
               Option.None
             else
               Obj.magic
                 Obj.magic
                 (let
                    (v__prefix'2541, v__splitTemp'2542)
                  =
                    Obj.magic
                      Boot.Intrinsics.Mseq.split_at
                      v__target'2540
                      1
                  in
                  let
                    (v__middle'2543, v__postfix'2544)
                  =
                    Obj.magic
                      Boot.Intrinsics.Mseq.split_at
                      v__splitTemp'2542
                      (Obj.magic
                         Int.sub
                         (Obj.magic
                            Boot.Intrinsics.Mseq.length
                            v__splitTemp'2542)
                         0)
                  in
                  let v__seqElem'2545 =
                    Obj.magic
                      Boot.Intrinsics.Mseq.get
                      v__prefix'2541
                      0
                  in
                  Option.Some (v__seqElem'2545)))
        with
        | Option.Some (v_p'1907) ->
            (let v_target'1908 =
               Obj.magic
                 v__addedNodesLeftChildren
                 v_p'1907
             in
             match
               Obj.magic
                 (let v__target'2546 =
                    Obj.magic
                      (!)
                      v_target'1908
                  in
                  let
                    CRec'2315 ({l0 = v_0'2547;l1 = v_1'2548})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2546
                  in
                  Option.Some (v_0'2547, v_1'2548))
             with
             | Option.Some (v_lastUpdate'1909, v_prev'1910) ->
                 (if
                    Obj.magic
                      (Obj.magic
                         v__isBefore
                         v_lastUpdate'1909
                         v_time'1904)
                  then
                    let v_leftChildrenHere'1911 =
                      Obj.magic
                        ref
                        (Obj.magic
                           Boot.Intrinsics.Mseq.Helpers.of_array
                           [| (Obj.magic
                               v_child'1905) |])
                    in
                    let v_'1913 =
                      Obj.magic
                        v_for_
                        v_parents'1906
                        (fun v_p'1912 ->
                           Obj.magic
                             (:=)
                             (Obj.magic
                                v__addedNodesLeftChildren
                                v_p'1912)
                             (CRec'2315 { l0 =
                                  (Obj.repr
                                    v_time'1904);
                                l1 =
                                  (Obj.repr
                                    v_leftChildrenHere'1911) }))
                    in
                    CSome'1610 (Obj.repr
                       v_parents'1906)
                  else
                    Obj.magic
                      (let v_'1914 =
                         Obj.magic
                           (:=)
                           v_prev'1910
                           (Obj.magic
                              Boot.Intrinsics.Mseq.cons
                              v_child'1905
                              (Obj.magic
                                 (!)
                                 v_prev'1910))
                       in
                       CNone'1611))
             | Option.None ->
                 (Obj.magic
                    (failwith
                       "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 578:11-578:16 ERROR: Reached a never term, which should be impossible in a well-typed program.")))
        | Option.None ->
            (Obj.magic
               (failwith
                  "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 579:9-579:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__getOpGroup =
  fun v_input'1916 ->
    fun v_id'1917 ->
      if
        Obj.magic
          (Obj.magic
             v__eqOpId
             v_id'1917
             v__rootID)
      then
        CRec'2274 { lmayGroupLeft =
            (Obj.repr
              false);
          lmayGroupRight =
            (Obj.repr
              true) }
      else
        Obj.magic
          (match
             Obj.magic
               (let v__target'2549 =
                  v_input'1916
                in
                match
                  match
                    match
                      Obj.magic
                        Obj.magic
                        v__target'2549
                    with
                    | CInfixI'1702 v__n'2550 ->
                        (let
                           CRec'2297 ({lprecWhenThisIsRight = v_precWhenThisIsRight'2551})
                         =
                           Obj.magic
                             Obj.magic
                             v__target'2549
                         in
                         Option.Some (v_precWhenThisIsRight'2551))
                    | _ ->
                        (Obj.magic
                           Obj.magic
                           (Option.None))
                  with
                  | Option.Some v__x'2554 ->
                      (Option.Some v__x'2554)
                  | Option.None ->
                      (Obj.magic
                         Obj.magic
                         (match
                            Obj.magic
                              Obj.magic
                              v__target'2549
                          with
                          | CPostfixI'1704 v__n'2552 ->
                              (let
                                 CRec'2298 ({lprecWhenThisIsRight = v_precWhenThisIsRight'2553})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2549
                               in
                               Option.Some (v_precWhenThisIsRight'2553))
                          | _ ->
                              (Obj.magic
                                 Obj.magic
                                 (Option.None))))
                with
                | Option.Some (v_prec'1918) ->
                    (Option.Some (v_prec'1918))
                | Option.None ->
                    (Obj.magic
                       Obj.magic
                       (Option.None)))
           with
           | Option.Some (v_prec'1918) ->
               (match
                  Obj.magic
                    (let v__target'2555 =
                       Obj.magic
                         v_mapLookup
                         v_id'1917
                         v_prec'1918
                     in
                     match
                       Obj.magic
                         Obj.magic
                         v__target'2555
                     with
                     | CSome'1610 v__n'2556 ->
                         (Option.Some (v__n'2556))
                     | _ ->
                         (Obj.magic
                            Obj.magic
                            (Option.None)))
                with
                | Option.Some (v_res'1919) ->
                    v_res'1919
                | Option.None ->
                    (Obj.magic
                       (CRec'2274 { lmayGroupLeft =
                            (Obj.repr
                              true);
                          lmayGroupRight =
                            (Obj.repr
                              true) })))
           | Option.None ->
               (Obj.magic
                  (failwith
                     "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 591:9-591:14 ERROR: Reached a never term, which should be impossible in a well-typed program.")));;
let v__mayGroupRight =
  fun v_l'1921 ->
    fun v_r'1922 ->
      let
        CRec'2274 ({lmayGroupRight = v_X'1923})
      =
        Obj.magic
          (Obj.magic
             v__getOpGroup
             v_r'1922
             (Obj.magic
                v__opIdT
                v_l'1921))
      in
      Obj.magic
        v_X'1923;;
let v__mayGroupLeft =
  fun v_l'1925 ->
    fun v_r'1926 ->
      let
        CRec'2274 ({lmayGroupLeft = v_X'1927})
      =
        Obj.magic
          (Obj.magic
             v__getOpGroup
             v_r'1926
             (Obj.magic
                v__opIdT
                v_l'1925))
      in
      Obj.magic
        v_X'1927;;
let v__newQueueFromFrontier =
  fun v_frontier'1930 ->
    Obj.magic
      Boot.Intrinsics.Mseq.map
      (fun v_'1931 ->
         Obj.magic
           ref
           (Obj.magic
              Boot.Intrinsics.Mseq.Helpers.of_array
              [|  |]))
      (Obj.magic
         Boot.Intrinsics.Mseq.create
         (Obj.magic
            Int.add
            1
            (Obj.magic
               v_maxOrElse
               (fun v_'1932 ->
                  0)
               Int.sub
               (Obj.magic
                  Boot.Intrinsics.Mseq.map
                  v__maxDistanceFromRoot
                  v_frontier'1930)))
         (fun v_'1933 ->
            ()));;
let v__addToQueue =
  fun v_node'1935 ->
    fun v_queue'1936 ->
      let v_dist'1937 =
        Obj.magic
          v__maxDistanceFromRoot
          v_node'1935
      in
      let v_target'1938 =
        Obj.magic
          Boot.Intrinsics.Mseq.get
          v_queue'1936
          v_dist'1937
      in
      Obj.magic
        (:=)
        v_target'1938
        (Obj.magic
           Boot.Intrinsics.Mseq.snoc
           (Obj.magic
              (!)
              v_target'1938)
           v_node'1935);;
let rec v__popFromQueue =
    fun v_queue'1941 ->
      match
        Obj.magic
          (let v__target'2557 =
             v_queue'1941
           in
           if
             Obj.magic
               ((<) : int -> int -> bool)
               (Obj.magic
                  Boot.Intrinsics.Mseq.length
                  v__target'2557)
               1
           then
             Option.None
           else
             Obj.magic
               Obj.magic
               (let
                  (v__prefix'2558, v__splitTemp'2559)
                =
                  Obj.magic
                    Boot.Intrinsics.Mseq.split_at
                    v__target'2557
                    0
                in
                let
                  (v__middle'2560, v__postfix'2561)
                =
                  Obj.magic
                    Boot.Intrinsics.Mseq.split_at
                    v__splitTemp'2559
                    (Obj.magic
                       Int.sub
                       (Obj.magic
                          Boot.Intrinsics.Mseq.length
                          v__splitTemp'2559)
                       1)
                in
                let v__seqElem'2562 =
                  Obj.magic
                    Boot.Intrinsics.Mseq.get
                    v__postfix'2561
                    0
                in
                Option.Some (v__middle'2560, v__seqElem'2562)))
      with
      | Option.Some (v_queue'1942, v_target'1943) ->
          (let v_nodes'1944 =
             Obj.magic
               (!)
               v_target'1943
           in
           match
             Obj.magic
               (let v__target'2563 =
                  v_nodes'1944
                in
                if
                  Obj.magic
                    ((<) : int -> int -> bool)
                    (Obj.magic
                       Boot.Intrinsics.Mseq.length
                       v__target'2563)
                    1
                then
                  Option.None
                else
                  Obj.magic
                    Obj.magic
                    (let
                       (v__prefix'2564, v__splitTemp'2565)
                     =
                       Obj.magic
                         Boot.Intrinsics.Mseq.split_at
                         v__target'2563
                         1
                     in
                     let
                       (v__middle'2566, v__postfix'2567)
                     =
                       Obj.magic
                         Boot.Intrinsics.Mseq.split_at
                         v__splitTemp'2565
                         (Obj.magic
                            Int.sub
                            (Obj.magic
                               Boot.Intrinsics.Mseq.length
                               v__splitTemp'2565)
                            0)
                     in
                     let v__seqElem'2568 =
                       Obj.magic
                         Boot.Intrinsics.Mseq.get
                         v__prefix'2564
                         0
                     in
                     Option.Some (v__seqElem'2568, v__middle'2566)))
           with
           | Option.Some (v_node'1945, v_nodes'1946) ->
               (let v_'1947 =
                  Obj.magic
                    (:=)
                    v_target'1943
                    v_nodes'1946
                in
                CSome'1610 (Obj.repr
                   v_node'1945))
           | Option.None ->
               (Obj.magic
                  (Obj.magic
                     v__popFromQueue
                     v_queue'1942)))
      | Option.None ->
          (Obj.magic
             CNone'1611);;
let v__addLOpen =
  fun v_input'1948 ->
    fun v_self'1949 ->
      fun v_st'1950 ->
        let v_time'1952 =
          Obj.magic
            Int.add
            1
            (Obj.magic
               (!)
               (let
                  CRec'2291 ({ltimestep = v_X'1951})
                =
                  Obj.magic
                    v_st'1950
                in
                Obj.magic
                  v_X'1951))
        in
        let v_'1954 =
          Obj.magic
            (:=)
            (let
               CRec'2291 ({ltimestep = v_X'1953})
             =
               Obj.magic
                 v_st'1950
             in
             Obj.magic
               v_X'1953)
            v_time'1952
        in
        let v_makeNewParents'1961 =
          fun v_parents'1955 ->
            match
              Obj.magic
                (let v__target'2569 =
                   v_parents'1955
                 in
                 if
                   Obj.magic
                     ((<) : int -> int -> bool)
                     (Obj.magic
                        Boot.Intrinsics.Mseq.length
                        v__target'2569)
                     1
                 then
                   Option.None
                 else
                   Obj.magic
                     Obj.magic
                     (let
                        (v__prefix'2570, v__splitTemp'2571)
                      =
                        Obj.magic
                          Boot.Intrinsics.Mseq.split_at
                          v__target'2569
                          1
                      in
                      let
                        (v__middle'2572, v__postfix'2573)
                      =
                        Obj.magic
                          Boot.Intrinsics.Mseq.split_at
                          v__splitTemp'2571
                          (Obj.magic
                             Int.sub
                             (Obj.magic
                                Boot.Intrinsics.Mseq.length
                                v__splitTemp'2571)
                             0)
                      in
                      let v__seqElem'2574 =
                        Obj.magic
                          Boot.Intrinsics.Mseq.get
                          v__prefix'2570
                          0
                      in
                      Option.Some (v__seqElem'2574)))
            with
            | Option.Some (v_p'1956) ->
                (let v_snd'1959 =
                   fun v_x'1957 ->
                     let
                       CRec'2315 ({l1 = v_X'1958})
                     =
                       Obj.magic
                         v_x'1957
                     in
                     Obj.magic
                       v_X'1958
                 in
                 let v_cs'1960 =
                   Obj.magic
                     (!)
                     (Obj.magic
                        v_snd'1959
                        (Obj.magic
                           (!)
                           (Obj.magic
                              v__addedNodesLeftChildren
                              v_p'1956)))
                 in
                 match
                   Obj.magic
                     (let v__target'2575 =
                        v_cs'1960
                      in
                      if
                        Obj.magic
                          ((<) : int -> int -> bool)
                          (Obj.magic
                             Boot.Intrinsics.Mseq.length
                             v__target'2575)
                          1
                      then
                        Option.None
                      else
                        Obj.magic
                          Obj.magic
                          (let
                             (v__prefix'2576, v__splitTemp'2577)
                           =
                             Obj.magic
                               Boot.Intrinsics.Mseq.split_at
                               v__target'2575
                               1
                           in
                           let
                             (v__middle'2578, v__postfix'2579)
                           =
                             Obj.magic
                               Boot.Intrinsics.Mseq.split_at
                               v__splitTemp'2577
                               (Obj.magic
                                  Int.sub
                                  (Obj.magic
                                     Boot.Intrinsics.Mseq.length
                                     v__splitTemp'2577)
                                  0)
                           in
                           let v__seqElem'2580 =
                             Obj.magic
                               Boot.Intrinsics.Mseq.get
                               v__prefix'2576
                               0
                           in
                           Option.Some ()))
                 with
                 | Option.Some () ->
                     (Obj.magic
                        v__addLeftChildren
                        v_st'1950
                        v_input'1948
                        v_self'1949
                        v_cs'1960
                        v_parents'1955)
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
                      "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 662:13-662:18 ERROR: Reached a never term, which should be impossible in a well-typed program."))
        in
        let v_handleLeaf'1972 =
          fun v_queue'1962 ->
            fun v_child'1963 ->
              match
                Obj.magic
                  (let v__target'2581 =
                     Obj.magic
                       v__getParents
                       v_child'1963
                   in
                   match
                     Obj.magic
                       Obj.magic
                       v__target'2581
                   with
                   | CSome'1610 v__n'2582 ->
                       (Option.Some (v__n'2582))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None)))
              with
              | Option.Some (v_parents'1964) ->
                  (let v_'1968 =
                     Obj.magic
                       v_for_
                       v_parents'1964
                       (fun v_parent'1965 ->
                          if
                            Obj.magic
                              (Obj.magic
                                 v_not
                                 (Obj.magic
                                    v__mayGroupLeft
                                    v_parent'1965
                                    v_input'1948))
                          then
                            ()
                          else
                            Obj.magic
                              (match
                                 Obj.magic
                                   (let v__target'2583 =
                                      Obj.magic
                                        v__shallowAllowedRight
                                        v_parent'1965
                                        v_child'1963
                                    in
                                    match
                                      Obj.magic
                                        Obj.magic
                                        v__target'2583
                                    with
                                    | CSome'1610 v__n'2584 ->
                                        (Option.Some (v__n'2584))
                                    | _ ->
                                        (Obj.magic
                                           Obj.magic
                                           (Option.None)))
                               with
                               | Option.Some (v_child'1966) ->
                                   (match
                                      Obj.magic
                                        (let v__target'2585 =
                                           Obj.magic
                                             v__addRightChildToParent
                                             v_time'1952
                                             v_child'1966
                                             v_parent'1965
                                         in
                                         match
                                           Obj.magic
                                             Obj.magic
                                             v__target'2585
                                         with
                                         | CSome'1610 v__n'2586 ->
                                             (Option.Some (v__n'2586))
                                         | _ ->
                                             (Obj.magic
                                                Obj.magic
                                                (Option.None)))
                                    with
                                    | Option.Some (v_parent'1967) ->
                                        (Obj.magic
                                           v__addToQueue
                                           v_parent'1967
                                           v_queue'1962)
                                    | Option.None ->
                                        (Obj.magic
                                           ()))
                               | Option.None ->
                                   (Obj.magic
                                      ())))
                   in
                   match
                     Obj.magic
                       (let v__target'2587 =
                          CRec'2315 { l0 =
                              (Obj.repr
                                (Obj.magic
                                   v__shallowAllowedLeft
                                   v_input'1948
                                   v_child'1963));
                            l1 =
                              (Obj.repr
                                (Obj.magic
                                   v_filter
                                   (fun v_l'1971 ->
                                      Obj.magic
                                        v__mayGroupRight
                                        v_l'1971
                                        v_input'1948)
                                   v_parents'1964)) }
                        in
                        let
                          CRec'2315 ({l0 = v_0'2588;l1 = v_1'2589})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2587
                        in
                        match
                          Obj.magic
                            Obj.magic
                            v_0'2588
                        with
                        | CSome'1610 v__n'2590 ->
                            (if
                               Obj.magic
                                 ((<) : int -> int -> bool)
                                 (Obj.magic
                                    Boot.Intrinsics.Mseq.length
                                    v_1'2589)
                                 1
                             then
                               Option.None
                             else
                               Obj.magic
                                 Obj.magic
                                 (let
                                    (v__prefix'2591, v__splitTemp'2592)
                                  =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.split_at
                                      v_1'2589
                                      1
                                  in
                                  let
                                    (v__middle'2593, v__postfix'2594)
                                  =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.split_at
                                      v__splitTemp'2592
                                      (Obj.magic
                                         Int.sub
                                         (Obj.magic
                                            Boot.Intrinsics.Mseq.length
                                            v__splitTemp'2592)
                                         0)
                                  in
                                  let v__seqElem'2595 =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.get
                                      v__prefix'2591
                                      0
                                  in
                                  Option.Some (v__n'2590, v_1'2589)))
                        | _ ->
                            (Obj.magic
                               Obj.magic
                               (Option.None)))
                   with
                   | Option.Some (v_child'1969, v_parents'1970) ->
                       (Obj.magic
                          v__addLeftChildToParent
                          v_time'1952
                          v_child'1969
                          v_parents'1970)
                   | Option.None ->
                       (Obj.magic
                          CNone'1611))
              | Option.None ->
                  (Obj.magic
                     (failwith
                        "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 683:13-683:18 ERROR: Reached a never term, which should be impossible in a well-typed program."))
        in
        let rec v_work'1973 =
            fun v_queue'1974 ->
              fun v_acc'1975 ->
                match
                  Obj.magic
                    (let v__target'2596 =
                       Obj.magic
                         v__popFromQueue
                         v_queue'1974
                     in
                     match
                       Obj.magic
                         Obj.magic
                         v__target'2596
                     with
                     | CSome'1610 v__n'2597 ->
                         (match
                            Obj.magic
                              Obj.magic
                              v__n'2597
                          with
                          | CTentativeMid'1717 v__n'2598 ->
                              (let
                                 CRec'2309 ({laddedNodesRightChildren = v_addedNodesRightChildren'2599})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__n'2597
                               in
                               Option.Some (v__n'2597, v_addedNodesRightChildren'2599))
                          | _ ->
                              (Obj.magic
                                 Obj.magic
                                 (Option.None)))
                     | _ ->
                         (Obj.magic
                            Obj.magic
                            (Option.None)))
                with
                | Option.Some (v_parent'1976, v_addedRight'1977) ->
                    (match
                       Obj.magic
                         (let v__target'2600 =
                            Obj.magic
                              (!)
                              v_addedRight'1977
                          in
                          let
                            CRec'2315 ({l0 = v_0'2601;l1 = v_1'2602})
                          =
                            Obj.magic
                              Obj.magic
                              v__target'2600
                          in
                          if
                            Obj.magic
                              ((<) : int -> int -> bool)
                              (Obj.magic
                                 Boot.Intrinsics.Mseq.length
                                 v_1'2602)
                              1
                          then
                            Option.None
                          else
                            Obj.magic
                              Obj.magic
                              (let
                                 (v__prefix'2603, v__splitTemp'2604)
                               =
                                 Obj.magic
                                   Boot.Intrinsics.Mseq.split_at
                                   v_1'2602
                                   1
                               in
                               let
                                 (v__middle'2605, v__postfix'2606)
                               =
                                 Obj.magic
                                   Boot.Intrinsics.Mseq.split_at
                                   v__splitTemp'2604
                                   (Obj.magic
                                      Int.sub
                                      (Obj.magic
                                         Boot.Intrinsics.Mseq.length
                                         v__splitTemp'2604)
                                      0)
                               in
                               let v__seqElem'2607 =
                                 Obj.magic
                                   Boot.Intrinsics.Mseq.get
                                   v__prefix'2603
                                   0
                               in
                               Option.Some (v_1'2602)))
                     with
                     | Option.Some (v_children'1978) ->
                         (let v_acc'1980 =
                            match
                              Obj.magic
                                (let v__target'2608 =
                                   Obj.magic
                                     v_handleLeaf'1972
                                     v_queue'1974
                                     (Obj.magic
                                        v__addRightChildren
                                        v_st'1950
                                        v_parent'1976
                                        v_children'1978)
                                 in
                                 match
                                   Obj.magic
                                     Obj.magic
                                     v__target'2608
                                 with
                                 | CSome'1610 v__n'2609 ->
                                     (Option.Some (v__n'2609))
                                 | _ ->
                                     (Obj.magic
                                        Obj.magic
                                        (Option.None)))
                            with
                            | Option.Some (v_n'1979) ->
                                (Obj.magic
                                   Boot.Intrinsics.Mseq.cons
                                   v_n'1979
                                   v_acc'1975)
                            | Option.None ->
                                (Obj.magic
                                   v_acc'1975)
                          in
                          Obj.magic
                            v_work'1973
                            v_queue'1974
                            v_acc'1980)
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
                       v_acc'1975)
        in let v_frontier'1982 =
          let
            CRec'2291 ({lfrontier = v_X'1981})
          =
            Obj.magic
              v_st'1950
          in
          Obj.magic
            v_X'1981
        in
        let v_queue'1983 =
          Obj.magic
            v__newQueueFromFrontier
            v_frontier'1982
        in
        let v_newParents'1984 =
          Obj.magic
            v_mapOption
            (Obj.magic
               v_handleLeaf'1972
               v_queue'1983)
            v_frontier'1982
        in
        let v_newParents'1985 =
          Obj.magic
            v_work'1973
            v_queue'1983
            v_newParents'1984
        in
        match
          Obj.magic
            (let v__target'2610 =
               Obj.magic
                 Boot.Intrinsics.Mseq.map
                 v_makeNewParents'1961
                 v_newParents'1985
             in
             if
               Obj.magic
                 ((<) : int -> int -> bool)
                 (Obj.magic
                    Boot.Intrinsics.Mseq.length
                    v__target'2610)
                 1
             then
               Option.None
             else
               Obj.magic
                 Obj.magic
                 (let
                    (v__prefix'2611, v__splitTemp'2612)
                  =
                    Obj.magic
                      Boot.Intrinsics.Mseq.split_at
                      v__target'2610
                      1
                  in
                  let
                    (v__middle'2613, v__postfix'2614)
                  =
                    Obj.magic
                      Boot.Intrinsics.Mseq.split_at
                      v__splitTemp'2612
                      (Obj.magic
                         Int.sub
                         (Obj.magic
                            Boot.Intrinsics.Mseq.length
                            v__splitTemp'2612)
                         0)
                  in
                  let v__seqElem'2615 =
                    Obj.magic
                      Boot.Intrinsics.Mseq.get
                      v__prefix'2611
                      0
                  in
                  Option.Some (v__target'2610)))
        with
        | Option.Some (v_frontier'1986) ->
            (CSome'1610 (Obj.repr
                (let
                   CRec'2291 v_rec'2616
                 =
                   Obj.magic
                     v_st'1950
                 in
                 CRec'2291 { v_rec'2616
                   with
                   lfrontier =
                     Obj.repr
                       v_frontier'1986 })))
        | Option.None ->
            (Obj.magic
               CNone'1611);;
let v_breakableAddPrefix =
  fun v_input'1988 ->
    fun v_self'1989 ->
      fun v_st'1990 ->
        let v_frontier'1992 =
          let
            CRec'2291 ({lfrontier = v_X'1991})
          =
            Obj.magic
              v_st'1990
          in
          Obj.magic
            v_X'1991
        in
        let v_time'1994 =
          Obj.magic
            (!)
            (let
               CRec'2291 ({ltimestep = v_X'1993})
             =
               Obj.magic
                 v_st'1990
             in
             Obj.magic
               v_X'1993)
        in
        let v_idx'1996 =
          Obj.magic
            (!)
            (let
               CRec'2291 ({lnextIdx = v_X'1995})
             =
               Obj.magic
                 v_st'1990
             in
             Obj.magic
               v_X'1995)
        in
        let v_'1998 =
          Obj.magic
            (:=)
            (let
               CRec'2291 ({lnextIdx = v_X'1997})
             =
               Obj.magic
                 v_st'1990
             in
             Obj.magic
               v_X'1997)
            (Obj.magic
               Int.add
               1
               v_idx'1996)
        in
        let v_addedLeft'1999 =
          Obj.magic
            ref
            (CRec'2315 { l0 =
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
        let v_addedRight'2000 =
          Obj.magic
            ref
            (CRec'2315 { l0 =
                 (Obj.repr
                   v__firstTimeStep);
               l1 =
                 (Obj.repr
                   (Obj.magic
                      Boot.Intrinsics.Mseq.Helpers.of_array
                      [|  |])) })
        in
        let
          CRec'2291 v_rec'2617
        =
          Obj.magic
            v_st'1990
        in
        CRec'2291 { v_rec'2617
          with
          lfrontier =
            Obj.repr
              (Obj.magic
                 Boot.Intrinsics.Mseq.Helpers.of_array
                 [| (Obj.magic
                     (CTentativeMid'1717 { lparents =
                          (Obj.repr
                            v_frontier'1992);
                        laddedNodesLeftChildren =
                          (Obj.repr
                            v_addedLeft'1999);
                        laddedNodesRightChildren =
                          (Obj.repr
                            v_addedRight'2000);
                        ltentativeData =
                          (Obj.repr
                            (CPrefixT'1713 { lidx =
                                 (Obj.repr
                                   v_idx'1996);
                               linput =
                                 (Obj.repr
                                   v_input'1988);
                               lself =
                                 (Obj.repr
                                   v_self'1989) }));
                        lmaxDistanceFromRoot =
                          (Obj.repr
                            (Obj.magic
                               Int.add
                               1
                               (Obj.magic
                                  v_maxOrElse
                                  (fun v_'2001 ->
                                     0)
                                  Int.sub
                                  (Obj.magic
                                     Boot.Intrinsics.Mseq.map
                                     v__maxDistanceFromRoot
                                     v_frontier'1992)))) })) |]) };;
let v_breakableAddInfix =
  fun v_input'2003 ->
    fun v_self'2004 ->
      fun v_st'2005 ->
        let v_res'2006 =
          Obj.magic
            v__addLOpen
            v_input'2003
            v_self'2004
            v_st'2005
        in
        let v_'2009 =
          Obj.magic
            (:=)
            (let
               CRec'2291 ({lnextIdx = v_X'2007})
             =
               Obj.magic
                 v_st'2005
             in
             Obj.magic
               v_X'2007)
            (Obj.magic
               Int.add
               1
               (Obj.magic
                  (!)
                  (let
                     CRec'2291 ({lnextIdx = v_X'2008})
                   =
                     Obj.magic
                       v_st'2005
                   in
                   Obj.magic
                     v_X'2008)))
        in
        v_res'2006;;
let v_breakableAddPostfix =
  fun v_input'2011 ->
    fun v_self'2012 ->
      fun v_st'2013 ->
        let v_res'2014 =
          Obj.magic
            v__addLOpen
            v_input'2011
            v_self'2012
            v_st'2013
        in
        let v_'2017 =
          Obj.magic
            (:=)
            (let
               CRec'2291 ({lnextIdx = v_X'2015})
             =
               Obj.magic
                 v_st'2013
             in
             Obj.magic
               v_X'2015)
            (Obj.magic
               Int.add
               1
               (Obj.magic
                  (!)
                  (let
                     CRec'2291 ({lnextIdx = v_X'2016})
                   =
                     Obj.magic
                       v_st'2013
                   in
                   Obj.magic
                     v_X'2016)))
        in
        v_res'2014;;
let v_breakableAddAtom =
  fun v_input'2019 ->
    fun v_self'2020 ->
      fun v_st'2021 ->
        let v_idx'2023 =
          Obj.magic
            (!)
            (let
               CRec'2291 ({lnextIdx = v_X'2022})
             =
               Obj.magic
                 v_st'2021
             in
             Obj.magic
               v_X'2022)
        in
        let v_'2025 =
          Obj.magic
            (:=)
            (let
               CRec'2291 ({lnextIdx = v_X'2024})
             =
               Obj.magic
                 v_st'2021
             in
             Obj.magic
               v_X'2024)
            (Obj.magic
               Int.add
               1
               v_idx'2023)
        in
        let v_id'2026 =
          Obj.magic
            v__uniqueID
            ()
        in
        let
          CRec'2291 v_rec'2618
        =
          Obj.magic
            v_st'2021
        in
        CRec'2291 { v_rec'2618
          with
          lfrontier =
            Obj.repr
              (Obj.magic
                 Boot.Intrinsics.Mseq.Helpers.of_array
                 [| (Obj.magic
                     (CTentativeLeaf'1716 { lparents =
                          (Obj.repr
                            (let
                               CRec'2291 ({lfrontier = v_X'2027})
                             =
                               Obj.magic
                                 v_st'2021
                             in
                             Obj.magic
                               v_X'2027));
                        lnode =
                          (Obj.repr
                            (CAtomP'1707 { lid =
                                 (Obj.repr
                                   v_id'2026);
                               lidx =
                                 (Obj.repr
                                   v_idx'2023);
                               linput =
                                 (Obj.repr
                                   v_input'2019);
                               lself =
                                 (Obj.repr
                                   v_self'2020) })) })) |]) };;
let v_breakableFinalizeParse =
  fun v_st'2029 ->
    let v_time'2031 =
      Obj.magic
        Int.add
        1
        (Obj.magic
           (!)
           (let
              CRec'2291 ({ltimestep = v_X'2030})
            =
              Obj.magic
                v_st'2029
            in
            Obj.magic
              v_X'2030))
    in
    let v_'2033 =
      Obj.magic
        (:=)
        (let
           CRec'2291 ({ltimestep = v_X'2032})
         =
           Obj.magic
             v_st'2029
         in
         Obj.magic
           v_X'2032)
        v_time'2031
    in
    let v_handleLeaf'2040 =
      fun v_queue'2034 ->
        fun v_child'2035 ->
          match
            Obj.magic
              (let v__target'2619 =
                 Obj.magic
                   v__getParents
                   v_child'2035
               in
               match
                 Obj.magic
                   Obj.magic
                   v__target'2619
               with
               | CSome'1610 v__n'2620 ->
                   (Option.Some (v__n'2620))
               | _ ->
                   (Obj.magic
                      Obj.magic
                      (Option.None)))
          with
          | Option.Some (v_parents'2036) ->
              (Obj.magic
                 v_for_
                 v_parents'2036
                 (fun v_parent'2037 ->
                    match
                      Obj.magic
                        (let v__target'2621 =
                           Obj.magic
                             v__shallowAllowedRight
                             v_parent'2037
                             v_child'2035
                         in
                         match
                           Obj.magic
                             Obj.magic
                             v__target'2621
                         with
                         | CSome'1610 v__n'2622 ->
                             (Option.Some (v__n'2622))
                         | _ ->
                             (Obj.magic
                                Obj.magic
                                (Option.None)))
                    with
                    | Option.Some (v_child'2038) ->
                        (match
                           Obj.magic
                             (let v__target'2623 =
                                Obj.magic
                                  v__addRightChildToParent
                                  v_time'2031
                                  v_child'2038
                                  v_parent'2037
                              in
                              match
                                Obj.magic
                                  Obj.magic
                                  v__target'2623
                              with
                              | CSome'1610 v__n'2624 ->
                                  (Option.Some (v__n'2624))
                              | _ ->
                                  (Obj.magic
                                     Obj.magic
                                     (Option.None)))
                         with
                         | Option.Some (v_parent'2039) ->
                             (Obj.magic
                                v__addToQueue
                                v_parent'2039
                                v_queue'2034)
                         | Option.None ->
                             (Obj.magic
                                ()))
                    | Option.None ->
                        (Obj.magic
                           ())))
          | Option.None ->
              (Obj.magic
                 (failwith
                    "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 795:13-795:18 ERROR: Reached a never term, which should be impossible in a well-typed program."))
    in
    let rec v_work'2041 =
        fun v_queue'2042 ->
          match
            Obj.magic
              (let v__target'2625 =
                 Obj.magic
                   v__popFromQueue
                   v_queue'2042
               in
               match
                 Obj.magic
                   Obj.magic
                   v__target'2625
               with
               | CSome'1610 v__n'2626 ->
                   (Option.Some (v__n'2626))
               | _ ->
                   (Obj.magic
                      Obj.magic
                      (Option.None)))
          with
          | Option.Some (v_p'2043) ->
              (let v_snd'2046 =
                 fun v_x'2044 ->
                   let
                     CRec'2315 ({l1 = v_X'2045})
                   =
                     Obj.magic
                       v_x'2044
                   in
                   Obj.magic
                     v_X'2045
               in
               let v_children'2047 =
                 Obj.magic
                   v_snd'2046
                   (Obj.magic
                      (!)
                      (Obj.magic
                         v__addedNodesRightChildren
                         v_p'2043))
               in
               let v_defaultCase'2627 =
                 fun nv_ ->
                   match
                     Obj.magic
                       (let v__target'2628 =
                          CRec'2315 { l0 =
                              (Obj.repr
                                v_p'2043);
                            l1 =
                              (Obj.repr
                                v_children'2047) }
                        in
                        let
                          CRec'2315 ({l0 = v_0'2629;l1 = v_1'2630})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2628
                        in
                        match
                          Obj.magic
                            Obj.magic
                            v_0'2629
                        with
                        | CTentativeMid'1717 v__n'2631 ->
                            (if
                               Obj.magic
                                 ((<) : int -> int -> bool)
                                 (Obj.magic
                                    Boot.Intrinsics.Mseq.length
                                    v_1'2630)
                                 1
                             then
                               Option.None
                             else
                               Obj.magic
                                 Obj.magic
                                 (let
                                    (v__prefix'2632, v__splitTemp'2633)
                                  =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.split_at
                                      v_1'2630
                                      1
                                  in
                                  let
                                    (v__middle'2634, v__postfix'2635)
                                  =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.split_at
                                      v__splitTemp'2633
                                      (Obj.magic
                                         Int.sub
                                         (Obj.magic
                                            Boot.Intrinsics.Mseq.length
                                            v__splitTemp'2633)
                                         0)
                                  in
                                  let v__seqElem'2636 =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.get
                                      v__prefix'2632
                                      0
                                  in
                                  Option.Some ()))
                        | _ ->
                            (Obj.magic
                               Obj.magic
                               (Option.None)))
                   with
                   | Option.Some () ->
                       (let v_'2048 =
                          Obj.magic
                            v_handleLeaf'2040
                            v_queue'2042
                            (Obj.magic
                               v__addRightChildren
                               v_st'2029
                               v_p'2043
                               v_children'2047)
                        in
                        Obj.magic
                          v_work'2041
                          v_queue'2042)
                   | Option.None ->
                       (Obj.magic
                          (match
                             Obj.magic
                               (let v__target'2637 =
                                  v_p'2043
                                in
                                match
                                  Obj.magic
                                    Obj.magic
                                    v__target'2637
                                with
                                | CTentativeMid'1717 v__n'2638 ->
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
                                     "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 811:15-811:20 ERROR: Reached a never term, which should be impossible in a well-typed program."))))
               in
               match
                 Obj.magic
                   v_p'2043
               with
               | CTentativeRoot'1718 v_x'2639 ->
                   v_children'2047
               | _ ->
                   (Obj.magic
                      (v_defaultCase'2627
                         ())))
          | Option.None ->
              (Obj.magic
                 (Obj.magic
                    Boot.Intrinsics.Mseq.Helpers.of_array
                    [|  |]))
    in let v_frontier'2050 =
      let
        CRec'2291 ({lfrontier = v_X'2049})
      =
        Obj.magic
          v_st'2029
      in
      Obj.magic
        v_X'2049
    in
    let v_queue'2051 =
      Obj.magic
        v__newQueueFromFrontier
        v_frontier'2050
    in
    let v_'2052 =
      Obj.magic
        Boot.Intrinsics.Mseq.iter
        (Obj.magic
           v_handleLeaf'2040
           v_queue'2051)
        v_frontier'2050
    in
    match
      Obj.magic
        (let v__target'2640 =
           Obj.magic
             v_work'2041
             v_queue'2051
         in
         if
           Obj.magic
             ((<) : int -> int -> bool)
             (Obj.magic
                Boot.Intrinsics.Mseq.length
                v__target'2640)
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
                  v__target'2640
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
              Option.Some (v__target'2640)))
    with
    | Option.Some (v_res'2053) ->
        (CSome'1610 (Obj.repr
            v_res'2053))
    | Option.None ->
        (Obj.magic
           CNone'1611);;
let v_breakableConstructResult =
  fun v_selfToTok'2058 ->
    fun v_lpar'2059 ->
      fun v_rpar'2060 ->
        fun v_parInput'2061 ->
          fun v_nodes'2062 ->
            let v_parId'2063 =
              Obj.magic
                v__opIdI
                v_parInput'2061
            in
            let rec v_range'2064 =
                fun v_node'2065 ->
                  let v_defaultCase'2646 =
                    fun nv_ ->
                      failwith
                        "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 856:13-856:18 ERROR: Reached a never term, which should be impossible in a well-typed program."
                  in
                  match
                    Obj.magic
                      v_node'2065
                  with
                  | CAtomP'1707 v_x'2647 ->
                      (match
                         Obj.magic
                           (let v__target'2648 =
                              Obj.magic
                                Obj.magic
                                v_node'2065
                            in
                            let
                              CRec'2310 ({lself = v_self'2649})
                            =
                              Obj.magic
                                Obj.magic
                                v__target'2648
                            in
                            Option.Some (v_self'2649))
                       with
                       | Option.Some (v_self'2066) ->
                           (CRec'2313 { lfirst =
                                (Obj.repr
                                  v_self'2066);
                              llast =
                                (Obj.repr
                                  v_self'2066) })
                       | Option.None ->
                           (Obj.magic
                              (Obj.magic
                                 v_defaultCase'2646
                                 ())))
                  | CInfixP'1708 v_x'2650 ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2651 =
                                 Obj.magic
                                   Obj.magic
                                   v_node'2065
                               in
                               let
                                 CRec'2283 ({lleftChildAlts = v_leftChildAlts'2652;lrightChildAlts = v_rightChildAlts'2653})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2651
                               in
                               if
                                 Obj.magic
                                   ((<) : int -> int -> bool)
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.length
                                      v_leftChildAlts'2652)
                                   1
                               then
                                 Option.None
                               else
                                 Obj.magic
                                   Obj.magic
                                   (let
                                      (v__prefix'2654, v__splitTemp'2655)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v_leftChildAlts'2652
                                        1
                                    in
                                    let
                                      (v__middle'2656, v__postfix'2657)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v__splitTemp'2655
                                        (Obj.magic
                                           Int.sub
                                           (Obj.magic
                                              Boot.Intrinsics.Mseq.length
                                              v__splitTemp'2655)
                                           0)
                                    in
                                    let v__seqElem'2658 =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.get
                                        v__prefix'2654
                                        0
                                    in
                                    if
                                      Obj.magic
                                        ((<) : int -> int -> bool)
                                        (Obj.magic
                                           Boot.Intrinsics.Mseq.length
                                           v_rightChildAlts'2653)
                                        1
                                    then
                                      Option.None
                                    else
                                      Obj.magic
                                        Obj.magic
                                        (let
                                           (v__prefix'2659, v__splitTemp'2660)
                                         =
                                           Obj.magic
                                             Boot.Intrinsics.Mseq.split_at
                                             v_rightChildAlts'2653
                                             1
                                         in
                                         let
                                           (v__middle'2661, v__postfix'2662)
                                         =
                                           Obj.magic
                                             Boot.Intrinsics.Mseq.split_at
                                             v__splitTemp'2660
                                             (Obj.magic
                                                Int.sub
                                                (Obj.magic
                                                   Boot.Intrinsics.Mseq.length
                                                   v__splitTemp'2660)
                                                0)
                                         in
                                         let v__seqElem'2663 =
                                           Obj.magic
                                             Boot.Intrinsics.Mseq.get
                                             v__prefix'2659
                                             0
                                         in
                                         Option.Some (v__seqElem'2658, v__seqElem'2663))))
                          with
                          | Option.Some (v_l'2067, v_r'2068) ->
                              (CRec'2313 { lfirst =
                                   (Obj.repr
                                     (let
                                        CRec'2313 ({lfirst = v_X'2069})
                                      =
                                        Obj.magic
                                          (Obj.magic
                                             v_range'2064
                                             v_l'2067)
                                      in
                                      Obj.magic
                                        v_X'2069));
                                 llast =
                                   (Obj.repr
                                     (let
                                        CRec'2313 ({llast = v_X'2070})
                                      =
                                        Obj.magic
                                          (Obj.magic
                                             v_range'2064
                                             v_r'2068)
                                      in
                                      Obj.magic
                                        v_X'2070)) })
                          | Option.None ->
                              (Obj.magic
                                 (Obj.magic
                                    v_defaultCase'2646
                                    ()))))
                  | CPrefixP'1709 v_x'2664 ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2665 =
                                 Obj.magic
                                   Obj.magic
                                   v_node'2065
                               in
                               let
                                 CRec'2284 ({lself = v_self'2666;lrightChildAlts = v_rightChildAlts'2667})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2665
                               in
                               if
                                 Obj.magic
                                   ((<) : int -> int -> bool)
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.length
                                      v_rightChildAlts'2667)
                                   1
                               then
                                 Option.None
                               else
                                 Obj.magic
                                   Obj.magic
                                   (let
                                      (v__prefix'2668, v__splitTemp'2669)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v_rightChildAlts'2667
                                        1
                                    in
                                    let
                                      (v__middle'2670, v__postfix'2671)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v__splitTemp'2669
                                        (Obj.magic
                                           Int.sub
                                           (Obj.magic
                                              Boot.Intrinsics.Mseq.length
                                              v__splitTemp'2669)
                                           0)
                                    in
                                    let v__seqElem'2672 =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.get
                                        v__prefix'2668
                                        0
                                    in
                                    Option.Some (v_self'2666, v__seqElem'2672)))
                          with
                          | Option.Some (v_self'2071, v_r'2072) ->
                              (CRec'2313 { lfirst =
                                   (Obj.repr
                                     v_self'2071);
                                 llast =
                                   (Obj.repr
                                     (let
                                        CRec'2313 ({llast = v_X'2073})
                                      =
                                        Obj.magic
                                          (Obj.magic
                                             v_range'2064
                                             v_r'2072)
                                      in
                                      Obj.magic
                                        v_X'2073)) })
                          | Option.None ->
                              (Obj.magic
                                 (Obj.magic
                                    v_defaultCase'2646
                                    ()))))
                  | CPostfixP'1710 v_x'2673 ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2674 =
                                 Obj.magic
                                   Obj.magic
                                   v_node'2065
                               in
                               let
                                 CRec'2303 ({lself = v_self'2675;lleftChildAlts = v_leftChildAlts'2676})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2674
                               in
                               if
                                 Obj.magic
                                   ((<) : int -> int -> bool)
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.length
                                      v_leftChildAlts'2676)
                                   1
                               then
                                 Option.None
                               else
                                 Obj.magic
                                   Obj.magic
                                   (let
                                      (v__prefix'2677, v__splitTemp'2678)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v_leftChildAlts'2676
                                        1
                                    in
                                    let
                                      (v__middle'2679, v__postfix'2680)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v__splitTemp'2678
                                        (Obj.magic
                                           Int.sub
                                           (Obj.magic
                                              Boot.Intrinsics.Mseq.length
                                              v__splitTemp'2678)
                                           0)
                                    in
                                    let v__seqElem'2681 =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.get
                                        v__prefix'2677
                                        0
                                    in
                                    Option.Some (v_self'2675, v__seqElem'2681)))
                          with
                          | Option.Some (v_self'2074, v_l'2075) ->
                              (CRec'2313 { lfirst =
                                   (Obj.repr
                                     (let
                                        CRec'2313 ({lfirst = v_X'2076})
                                      =
                                        Obj.magic
                                          (Obj.magic
                                             v_range'2064
                                             v_l'2075)
                                      in
                                      Obj.magic
                                        v_X'2076));
                                 llast =
                                   (Obj.repr
                                     v_self'2074) })
                          | Option.None ->
                              (Obj.magic
                                 (Obj.magic
                                    v_defaultCase'2646
                                    ()))))
                  | _ ->
                      (Obj.magic
                         (v_defaultCase'2646
                            ()))
            in let rec v_flattenOne'2077 =
                fun v_node'2079 ->
                  let v_X'2080 =
                    v_node'2079
                  in
                  let v_defaultCase'2682 =
                    fun nv_ ->
                      failwith
                        "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 869:8-869:11 ERROR: Reached a never term, which should be impossible in a well-typed program."
                  in
                  match
                    Obj.magic
                      v_X'2080
                  with
                  | CAtomP'1707 v_x'2683 ->
                      (match
                         Obj.magic
                           (let v__target'2684 =
                              Obj.magic
                                Obj.magic
                                v_X'2080
                            in
                            let
                              CRec'2310 ({lself = v_self'2685})
                            =
                              Obj.magic
                                Obj.magic
                                v__target'2684
                            in
                            Option.Some (v_self'2685))
                       with
                       | Option.Some (v_self'2081) ->
                           (Obj.magic
                              Boot.Intrinsics.Mseq.Helpers.of_array
                              [| (Obj.magic
                                  (Obj.magic
                                     v_selfToTok'2058
                                     v_self'2081)) |])
                       | Option.None ->
                           (Obj.magic
                              (Obj.magic
                                 v_defaultCase'2682
                                 ())))
                  | CInfixP'1708 v_x'2686 ->
                      (Obj.magic
                         (let v_p'2082 =
                            Obj.magic
                              Obj.magic
                              v_X'2080
                          in
                          Obj.magic
                            v_join
                            (Obj.magic
                               Boot.Intrinsics.Mseq.Helpers.of_array
                               [| (Obj.magic
                                   (Obj.magic
                                      v_flattenMany'2078
                                      (let
                                         CRec'2283 ({lleftChildAlts = v_X'2083})
                                       =
                                         Obj.magic
                                           v_p'2082
                                       in
                                       Obj.magic
                                         v_X'2083)));
                                 (Obj.magic
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.Helpers.of_array
                                      [| (Obj.magic
                                          (Obj.magic
                                             v_selfToTok'2058
                                             (let
                                                CRec'2283 ({lself = v_X'2084})
                                              =
                                                Obj.magic
                                                  v_p'2082
                                              in
                                              Obj.magic
                                                v_X'2084))) |]));
                                 (Obj.magic
                                   (Obj.magic
                                      v_flattenMany'2078
                                      (let
                                         CRec'2283 ({lrightChildAlts = v_X'2085})
                                       =
                                         Obj.magic
                                           v_p'2082
                                       in
                                       Obj.magic
                                         v_X'2085))) |])))
                  | CPrefixP'1709 v_x'2687 ->
                      (Obj.magic
                         (let v_p'2086 =
                            Obj.magic
                              Obj.magic
                              v_X'2080
                          in
                          Obj.magic
                            Boot.Intrinsics.Mseq.cons
                            (Obj.magic
                               v_selfToTok'2058
                               (let
                                  CRec'2284 ({lself = v_X'2087})
                                =
                                  Obj.magic
                                    v_p'2086
                                in
                                Obj.magic
                                  v_X'2087))
                            (Obj.magic
                               v_flattenMany'2078
                               (let
                                  CRec'2284 ({lrightChildAlts = v_X'2088})
                                =
                                  Obj.magic
                                    v_p'2086
                                in
                                Obj.magic
                                  v_X'2088))))
                  | CPostfixP'1710 v_x'2688 ->
                      (Obj.magic
                         (let v_p'2089 =
                            Obj.magic
                              Obj.magic
                              v_X'2080
                          in
                          Obj.magic
                            Boot.Intrinsics.Mseq.snoc
                            (Obj.magic
                               v_flattenMany'2078
                               (let
                                  CRec'2303 ({lleftChildAlts = v_X'2090})
                                =
                                  Obj.magic
                                    v_p'2089
                                in
                                Obj.magic
                                  v_X'2090))
                            (Obj.magic
                               v_selfToTok'2058
                               (let
                                  CRec'2303 ({lself = v_X'2091})
                                =
                                  Obj.magic
                                    v_p'2089
                                in
                                Obj.magic
                                  v_X'2091))))
                  | _ ->
                      (Obj.magic
                         (v_defaultCase'2682
                            ()))
            and v_flattenMany'2078 =
                fun v_nodes'2092 ->
                  match
                    Obj.magic
                      (let v__target'2689 =
                         v_nodes'2092
                       in
                       if
                         Obj.magic
                           ((<) : int -> int -> bool)
                           (Obj.magic
                              Boot.Intrinsics.Mseq.length
                              v__target'2689)
                           1
                       then
                         Option.None
                       else
                         Obj.magic
                           Obj.magic
                           (let
                              (v__prefix'2690, v__splitTemp'2691)
                            =
                              Obj.magic
                                Boot.Intrinsics.Mseq.split_at
                                v__target'2689
                                1
                            in
                            let
                              (v__middle'2692, v__postfix'2693)
                            =
                              Obj.magic
                                Boot.Intrinsics.Mseq.split_at
                                v__splitTemp'2691
                                (Obj.magic
                                   Int.sub
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.length
                                      v__splitTemp'2691)
                                   0)
                            in
                            let v__seqElem'2694 =
                              Obj.magic
                                Boot.Intrinsics.Mseq.get
                                v__prefix'2690
                                0
                            in
                            Option.Some (v__seqElem'2694)))
                  with
                  | Option.Some (v_n'2093) ->
                      (Obj.magic
                         v_flattenOne'2077
                         v_n'2093)
                  | Option.None ->
                      (Obj.magic
                         (failwith
                            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 873:13-873:18 ERROR: Reached a never term, which should be impossible in a well-typed program."))
            in let v_resolveWith'2099 =
              fun v_tops'2094 ->
                fun v_allowSet'2095 ->
                  fun v_children'2096 ->
                    fun v_resolveDir'2097 ->
                      let v_needToWrap'2098 =
                        Obj.magic
                          v_not
                          (Obj.magic
                             Boot.Intrinsics.Mseq.null
                             v_tops'2094)
                      in
                      if
                        Obj.magic
                          v_needToWrap'2098
                      then
                        if
                          Obj.magic
                            (Obj.magic
                               v_breakableInAllowSet
                               v_parId'2063
                               v_allowSet'2095)
                        then
                          Obj.magic
                            Boot.Intrinsics.Mseq.Helpers.of_array
                            [| (Obj.magic
                                (Obj.magic
                                   Boot.Intrinsics.Mseq.cons
                                   v_lpar'2059
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.snoc
                                      (Obj.magic
                                         v_flattenMany'2078
                                         v_children'2096)
                                      v_rpar'2060))) |]
                        else
                          Obj.magic
                            (Obj.magic
                               v_join
                               (Obj.magic
                                  Boot.Intrinsics.Mseq.map
                                  (Obj.magic
                                     v_resolveDir'2097
                                     v_tops'2094)
                                  v_children'2096))
                      else
                        Obj.magic
                          (Obj.magic
                             Boot.Intrinsics.Mseq.Helpers.of_array
                             [| (Obj.magic
                                 (Obj.magic
                                    v_flattenMany'2078
                                    v_children'2096)) |])
            in
            let rec v_resolveDir'2100 =
                fun v_forceLeft'2101 ->
                  fun v_forceRight'2102 ->
                    fun v_tops'2103 ->
                      fun v_node'2104 ->
                        let v_X'2105 =
                          v_node'2104
                        in
                        let v_defaultCase'2695 =
                          fun nv_ ->
                            failwith
                              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 935:8-935:11 ERROR: Reached a never term, which should be impossible in a well-typed program."
                        in
                        match
                          Obj.magic
                            v_X'2105
                        with
                        | CAtomP'1707 v_x'2696 ->
                            (match
                               Obj.magic
                                 (let v__target'2697 =
                                    Obj.magic
                                      Obj.magic
                                      v_X'2105
                                  in
                                  let
                                    CRec'2310 ({lself = v_self'2698})
                                  =
                                    Obj.magic
                                      Obj.magic
                                      v__target'2697
                                  in
                                  Option.Some (v_self'2698))
                             with
                             | Option.Some (v_self'2106) ->
                                 (Obj.magic
                                    Boot.Intrinsics.Mseq.Helpers.of_array
                                    [| (Obj.magic
                                        (Obj.magic
                                           Boot.Intrinsics.Mseq.Helpers.of_array
                                           [| (Obj.magic
                                               (Obj.magic
                                                  v_selfToTok'2058
                                                  v_self'2106)) |])) |])
                             | Option.None ->
                                 (Obj.magic
                                    (Obj.magic
                                       v_defaultCase'2695
                                       ())))
                        | CInfixP'1708 v_x'2699 ->
                            (Obj.magic
                               (match
                                  Obj.magic
                                    (let v__target'2700 =
                                       Obj.magic
                                         Obj.magic
                                         v_X'2105
                                     in
                                     let
                                       CRec'2283 ({linput = v_input'2701})
                                     =
                                       Obj.magic
                                         Obj.magic
                                         v__target'2700
                                     in
                                     match
                                       Obj.magic
                                         Obj.magic
                                         v_input'2701
                                     with
                                     | CInfixI'1702 v__n'2702 ->
                                         (Option.Some (v__target'2700, v_input'2701))
                                     | _ ->
                                         (Obj.magic
                                            Obj.magic
                                            (Option.None)))
                                with
                                | Option.Some (v_node'2107, v_i'2108) ->
                                    (let v_left'2114 =
                                       if
                                         Obj.magic
                                           v_forceLeft'2101
                                       then
                                         Obj.magic
                                           Boot.Intrinsics.Mseq.Helpers.of_array
                                           [| (Obj.magic
                                               (Obj.magic
                                                  Boot.Intrinsics.Mseq.cons
                                                  v_lpar'2059
                                                  (Obj.magic
                                                     Boot.Intrinsics.Mseq.snoc
                                                     (Obj.magic
                                                        v_flattenMany'2078
                                                        (let
                                                           CRec'2283 ({lleftChildAlts = v_X'2109})
                                                         =
                                                           Obj.magic
                                                             v_node'2107
                                                         in
                                                         Obj.magic
                                                           v_X'2109))
                                                     v_rpar'2060))) |]
                                       else
                                         Obj.magic
                                           (let v_tops'2111 =
                                              Obj.magic
                                                v_filter
                                                (Obj.magic
                                                   ((>) : int -> int -> bool)
                                                   (let
                                                      CRec'2283 ({lidx = v_X'2110})
                                                    =
                                                      Obj.magic
                                                        v_node'2107
                                                    in
                                                    Obj.magic
                                                      v_X'2110))
                                                v_tops'2103
                                            in
                                            Obj.magic
                                              v_resolveWith'2099
                                              v_tops'2111
                                              (let
                                                 CRec'2297 ({lleftAllow = v_X'2112})
                                               =
                                                 Obj.magic
                                                   v_i'2108
                                               in
                                               Obj.magic
                                                 v_X'2112)
                                              (let
                                                 CRec'2283 ({lleftChildAlts = v_X'2113})
                                               =
                                                 Obj.magic
                                                   v_node'2107
                                               in
                                               Obj.magic
                                                 v_X'2113)
                                              (Obj.magic
                                                 v_resolveDir'2100
                                                 false
                                                 true))
                                     in
                                     let v_right'2120 =
                                       if
                                         Obj.magic
                                           v_forceRight'2102
                                       then
                                         Obj.magic
                                           Boot.Intrinsics.Mseq.Helpers.of_array
                                           [| (Obj.magic
                                               (Obj.magic
                                                  Boot.Intrinsics.Mseq.cons
                                                  v_lpar'2059
                                                  (Obj.magic
                                                     Boot.Intrinsics.Mseq.snoc
                                                     (Obj.magic
                                                        v_flattenMany'2078
                                                        (let
                                                           CRec'2283 ({lrightChildAlts = v_X'2115})
                                                         =
                                                           Obj.magic
                                                             v_node'2107
                                                         in
                                                         Obj.magic
                                                           v_X'2115))
                                                     v_rpar'2060))) |]
                                       else
                                         Obj.magic
                                           (let v_tops'2117 =
                                              Obj.magic
                                                v_filter
                                                (Obj.magic
                                                   ((<) : int -> int -> bool)
                                                   (let
                                                      CRec'2283 ({lidx = v_X'2116})
                                                    =
                                                      Obj.magic
                                                        v_node'2107
                                                    in
                                                    Obj.magic
                                                      v_X'2116))
                                                v_tops'2103
                                            in
                                            Obj.magic
                                              v_resolveWith'2099
                                              v_tops'2117
                                              (let
                                                 CRec'2297 ({lrightAllow = v_X'2118})
                                               =
                                                 Obj.magic
                                                   v_i'2108
                                               in
                                               Obj.magic
                                                 v_X'2118)
                                              (let
                                                 CRec'2283 ({lrightChildAlts = v_X'2119})
                                               =
                                                 Obj.magic
                                                   v_node'2107
                                               in
                                               Obj.magic
                                                 v_X'2119)
                                              (Obj.magic
                                                 v_resolveDir'2100
                                                 true
                                                 false))
                                     in
                                     let v_here'2122 =
                                       Obj.magic
                                         Boot.Intrinsics.Mseq.Helpers.of_array
                                         [| (Obj.magic
                                             (Obj.magic
                                                v_selfToTok'2058
                                                (let
                                                   CRec'2283 ({lself = v_X'2121})
                                                 =
                                                   Obj.magic
                                                     v_node'2107
                                                 in
                                                 Obj.magic
                                                   v_X'2121))) |]
                                     in
                                     Obj.magic
                                       v_seqLiftA2
                                       (fun v_l'2123 ->
                                          fun v_r'2124 ->
                                            Obj.magic
                                              v_join
                                              (Obj.magic
                                                 Boot.Intrinsics.Mseq.Helpers.of_array
                                                 [| (Obj.magic
                                                     v_l'2123);
                                                   (Obj.magic
                                                     v_here'2122);
                                                   (Obj.magic
                                                     v_r'2124) |]))
                                       v_left'2114
                                       v_right'2120)
                                | Option.None ->
                                    (Obj.magic
                                       (Obj.magic
                                          v_defaultCase'2695
                                          ()))))
                        | CPrefixP'1709 v_x'2703 ->
                            (Obj.magic
                               (match
                                  Obj.magic
                                    (let v__target'2704 =
                                       Obj.magic
                                         Obj.magic
                                         v_X'2105
                                     in
                                     let
                                       CRec'2284 ({linput = v_input'2705})
                                     =
                                       Obj.magic
                                         Obj.magic
                                         v__target'2704
                                     in
                                     match
                                       Obj.magic
                                         Obj.magic
                                         v_input'2705
                                     with
                                     | CPrefixI'1703 v__n'2706 ->
                                         (Option.Some (v__target'2704, v_input'2705))
                                     | _ ->
                                         (Obj.magic
                                            Obj.magic
                                            (Option.None)))
                                with
                                | Option.Some (v_node'2125, v_i'2126) ->
                                    (let v_left'2127 =
                                       Obj.magic
                                         Boot.Intrinsics.Mseq.Helpers.of_array
                                         [| (Obj.magic
                                             (Obj.magic
                                                Boot.Intrinsics.Mseq.Helpers.of_array
                                                [|  |])) |]
                                     in
                                     let v_right'2133 =
                                       if
                                         Obj.magic
                                           v_forceRight'2102
                                       then
                                         Obj.magic
                                           Boot.Intrinsics.Mseq.Helpers.of_array
                                           [| (Obj.magic
                                               (Obj.magic
                                                  Boot.Intrinsics.Mseq.cons
                                                  v_lpar'2059
                                                  (Obj.magic
                                                     Boot.Intrinsics.Mseq.snoc
                                                     (Obj.magic
                                                        v_flattenMany'2078
                                                        (let
                                                           CRec'2284 ({lrightChildAlts = v_X'2128})
                                                         =
                                                           Obj.magic
                                                             v_node'2125
                                                         in
                                                         Obj.magic
                                                           v_X'2128))
                                                     v_rpar'2060))) |]
                                       else
                                         Obj.magic
                                           (let v_tops'2130 =
                                              Obj.magic
                                                v_filter
                                                (Obj.magic
                                                   ((<) : int -> int -> bool)
                                                   (let
                                                      CRec'2284 ({lidx = v_X'2129})
                                                    =
                                                      Obj.magic
                                                        v_node'2125
                                                    in
                                                    Obj.magic
                                                      v_X'2129))
                                                v_tops'2103
                                            in
                                            Obj.magic
                                              v_resolveWith'2099
                                              v_tops'2130
                                              (let
                                                 CRec'2296 ({lrightAllow = v_X'2131})
                                               =
                                                 Obj.magic
                                                   v_i'2126
                                               in
                                               Obj.magic
                                                 v_X'2131)
                                              (let
                                                 CRec'2284 ({lrightChildAlts = v_X'2132})
                                               =
                                                 Obj.magic
                                                   v_node'2125
                                               in
                                               Obj.magic
                                                 v_X'2132)
                                              (Obj.magic
                                                 v_resolveDir'2100
                                                 true
                                                 false))
                                     in
                                     let v_here'2135 =
                                       Obj.magic
                                         Boot.Intrinsics.Mseq.Helpers.of_array
                                         [| (Obj.magic
                                             (Obj.magic
                                                v_selfToTok'2058
                                                (let
                                                   CRec'2284 ({lself = v_X'2134})
                                                 =
                                                   Obj.magic
                                                     v_node'2125
                                                 in
                                                 Obj.magic
                                                   v_X'2134))) |]
                                     in
                                     Obj.magic
                                       v_seqLiftA2
                                       (fun v_l'2136 ->
                                          fun v_r'2137 ->
                                            Obj.magic
                                              v_join
                                              (Obj.magic
                                                 Boot.Intrinsics.Mseq.Helpers.of_array
                                                 [| (Obj.magic
                                                     v_l'2136);
                                                   (Obj.magic
                                                     v_here'2135);
                                                   (Obj.magic
                                                     v_r'2137) |]))
                                       v_left'2127
                                       v_right'2133)
                                | Option.None ->
                                    (Obj.magic
                                       (Obj.magic
                                          v_defaultCase'2695
                                          ()))))
                        | CPostfixP'1710 v_x'2707 ->
                            (Obj.magic
                               (match
                                  Obj.magic
                                    (let v__target'2708 =
                                       Obj.magic
                                         Obj.magic
                                         v_X'2105
                                     in
                                     let
                                       CRec'2303 ({linput = v_input'2709})
                                     =
                                       Obj.magic
                                         Obj.magic
                                         v__target'2708
                                     in
                                     match
                                       Obj.magic
                                         Obj.magic
                                         v_input'2709
                                     with
                                     | CPostfixI'1704 v__n'2710 ->
                                         (Option.Some (v__target'2708, v_input'2709))
                                     | _ ->
                                         (Obj.magic
                                            Obj.magic
                                            (Option.None)))
                                with
                                | Option.Some (v_node'2138, v_i'2139) ->
                                    (let v_left'2145 =
                                       if
                                         Obj.magic
                                           v_forceLeft'2101
                                       then
                                         Obj.magic
                                           Boot.Intrinsics.Mseq.Helpers.of_array
                                           [| (Obj.magic
                                               (Obj.magic
                                                  Boot.Intrinsics.Mseq.cons
                                                  v_lpar'2059
                                                  (Obj.magic
                                                     Boot.Intrinsics.Mseq.snoc
                                                     (Obj.magic
                                                        v_flattenMany'2078
                                                        (let
                                                           CRec'2303 ({lleftChildAlts = v_X'2140})
                                                         =
                                                           Obj.magic
                                                             v_node'2138
                                                         in
                                                         Obj.magic
                                                           v_X'2140))
                                                     v_rpar'2060))) |]
                                       else
                                         Obj.magic
                                           (let v_tops'2142 =
                                              Obj.magic
                                                v_filter
                                                (Obj.magic
                                                   ((>) : int -> int -> bool)
                                                   (let
                                                      CRec'2303 ({lidx = v_X'2141})
                                                    =
                                                      Obj.magic
                                                        v_node'2138
                                                    in
                                                    Obj.magic
                                                      v_X'2141))
                                                v_tops'2103
                                            in
                                            Obj.magic
                                              v_resolveWith'2099
                                              v_tops'2142
                                              (let
                                                 CRec'2298 ({lleftAllow = v_X'2143})
                                               =
                                                 Obj.magic
                                                   v_i'2139
                                               in
                                               Obj.magic
                                                 v_X'2143)
                                              (let
                                                 CRec'2303 ({lleftChildAlts = v_X'2144})
                                               =
                                                 Obj.magic
                                                   v_node'2138
                                               in
                                               Obj.magic
                                                 v_X'2144)
                                              (Obj.magic
                                                 v_resolveDir'2100
                                                 false
                                                 true))
                                     in
                                     let v_right'2146 =
                                       Obj.magic
                                         Boot.Intrinsics.Mseq.Helpers.of_array
                                         [| (Obj.magic
                                             (Obj.magic
                                                Boot.Intrinsics.Mseq.Helpers.of_array
                                                [|  |])) |]
                                     in
                                     let v_here'2148 =
                                       Obj.magic
                                         Boot.Intrinsics.Mseq.Helpers.of_array
                                         [| (Obj.magic
                                             (Obj.magic
                                                v_selfToTok'2058
                                                (let
                                                   CRec'2303 ({lself = v_X'2147})
                                                 =
                                                   Obj.magic
                                                     v_node'2138
                                                 in
                                                 Obj.magic
                                                   v_X'2147))) |]
                                     in
                                     Obj.magic
                                       v_seqLiftA2
                                       (fun v_l'2149 ->
                                          fun v_r'2150 ->
                                            Obj.magic
                                              v_join
                                              (Obj.magic
                                                 Boot.Intrinsics.Mseq.Helpers.of_array
                                                 [| (Obj.magic
                                                     v_l'2149);
                                                   (Obj.magic
                                                     v_here'2148);
                                                   (Obj.magic
                                                     v_r'2150) |]))
                                       v_left'2145
                                       v_right'2146)
                                | Option.None ->
                                    (Obj.magic
                                       (Obj.magic
                                          v_defaultCase'2695
                                          ()))))
                        | _ ->
                            (Obj.magic
                               (v_defaultCase'2695
                                  ()))
            in let v_ambiguities'2151 =
              Obj.magic
                ref
                (Obj.magic
                   Boot.Intrinsics.Mseq.Helpers.of_array
                   [|  |])
            in
            let rec v_workMany'2152 =
                fun v_tops'2154 ->
                  match
                    Obj.magic
                      (let v__target'2711 =
                         v_tops'2154
                       in
                       if
                         Obj.magic
                           Int.equal
                           (Obj.magic
                              Boot.Intrinsics.Mseq.length
                              v__target'2711)
                           1
                       then
                         let v__seqElem'2712 =
                           Obj.magic
                             Boot.Intrinsics.Mseq.get
                             v__target'2711
                             0
                         in
                         Option.Some (v__seqElem'2712)
                       else
                         Obj.magic
                           Obj.magic
                           (Option.None))
                  with
                  | Option.Some (v_n'2155) ->
                      (Obj.magic
                         v_workOne'2153
                         v_n'2155)
                  | Option.None ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2713 =
                                 v_tops'2154
                               in
                               if
                                 Obj.magic
                                   ((<) : int -> int -> bool)
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.length
                                      v__target'2713)
                                   1
                               then
                                 Option.None
                               else
                                 Obj.magic
                                   Obj.magic
                                   (let
                                      (v__prefix'2714, v__splitTemp'2715)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v__target'2713
                                        1
                                    in
                                    let
                                      (v__middle'2716, v__postfix'2717)
                                    =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.split_at
                                        v__splitTemp'2715
                                        (Obj.magic
                                           Int.sub
                                           (Obj.magic
                                              Boot.Intrinsics.Mseq.length
                                              v__splitTemp'2715)
                                           0)
                                    in
                                    let v__seqElem'2718 =
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.get
                                        v__prefix'2714
                                        0
                                    in
                                    Option.Some (v__seqElem'2718)))
                          with
                          | Option.Some (v_n'2156) ->
                              (let v_topIdxs'2157 =
                                 Obj.magic
                                   Boot.Intrinsics.Mseq.map
                                   v__opIdxP
                                   v_tops'2154
                               in
                               let v_range'2158 =
                                 Obj.magic
                                   v_range'2064
                                   v_n'2156
                               in
                               let v_resolutions'2159 =
                                 Obj.magic
                                   v_join
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.map
                                      (Obj.magic
                                         v_resolveDir'2100
                                         false
                                         false
                                         v_topIdxs'2157)
                                      v_tops'2154)
                               in
                               let v_err'2162 =
                                 CRec'2314 { lfirst =
                                     (Obj.repr
                                       (let
                                          CRec'2313 ({lfirst = v_X'2160})
                                        =
                                          Obj.magic
                                            v_range'2158
                                        in
                                        Obj.magic
                                          v_X'2160));
                                   llast =
                                     (Obj.repr
                                       (let
                                          CRec'2313 ({llast = v_X'2161})
                                        =
                                          Obj.magic
                                            v_range'2158
                                        in
                                        Obj.magic
                                          v_X'2161));
                                   lpartialResolutions =
                                     (Obj.repr
                                       v_resolutions'2159) }
                               in
                               let v_'2163 =
                                 Obj.magic
                                   (:=)
                                   v_ambiguities'2151
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.cons
                                      v_err'2162
                                      (Obj.magic
                                         (!)
                                         v_ambiguities'2151))
                               in
                               CNone'1611)
                          | Option.None ->
                              (Obj.magic
                                 (let v_'2164 =
                                    Obj.magic
                                      v_dprintLn
                                      v_tops'2154
                                  in
                                  failwith
                                    "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 956:30-956:35 ERROR: Reached a never term, which should be impossible in a well-typed program."))))
            and v_workOne'2153 =
                fun v_node'2165 ->
                  let v_defaultCase'2719 =
                    fun nv_ ->
                      failwith
                        "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 971:15-971:20 ERROR: Reached a never term, which should be impossible in a well-typed program."
                  in
                  match
                    Obj.magic
                      v_node'2165
                  with
                  | CAtomP'1707 v_x'2720 ->
                      (match
                         Obj.magic
                           (let v__target'2721 =
                              Obj.magic
                                Obj.magic
                                v_node'2165
                            in
                            let
                              CRec'2310 ({linput = v_input'2722;lself = v_self'2723})
                            =
                              Obj.magic
                                Obj.magic
                                v__target'2721
                            in
                            match
                              Obj.magic
                                Obj.magic
                                v_input'2722
                            with
                            | CAtomI'1701 v__n'2724 ->
                                (let
                                   CRec'2294 ({lconstruct = v_construct'2725})
                                 =
                                   Obj.magic
                                     Obj.magic
                                     v_input'2722
                                 in
                                 Option.Some (v_construct'2725, v_self'2723))
                            | _ ->
                                (Obj.magic
                                   Obj.magic
                                   (Option.None)))
                       with
                       | Option.Some (v_c'2166, v_self'2167) ->
                           (CSome'1610 (Obj.repr
                               (Obj.magic
                                  v_c'2166
                                  v_self'2167)))
                       | Option.None ->
                           (Obj.magic
                              (Obj.magic
                                 v_defaultCase'2719
                                 ())))
                  | CInfixP'1708 v_x'2726 ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2727 =
                                 Obj.magic
                                   Obj.magic
                                   v_node'2165
                               in
                               let
                                 CRec'2283 ({linput = v_input'2728;lself = v_self'2729;lleftChildAlts = v_leftChildAlts'2730;lrightChildAlts = v_rightChildAlts'2731})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2727
                               in
                               match
                                 Obj.magic
                                   Obj.magic
                                   v_input'2728
                               with
                               | CInfixI'1702 v__n'2732 ->
                                   (let
                                      CRec'2297 ({lconstruct = v_construct'2733})
                                    =
                                      Obj.magic
                                        Obj.magic
                                        v_input'2728
                                    in
                                    Option.Some (v_construct'2733, v_self'2729, v_leftChildAlts'2730, v_rightChildAlts'2731))
                               | _ ->
                                   (Obj.magic
                                      Obj.magic
                                      (Option.None)))
                          with
                          | Option.Some (v_c'2171, v_self'2172, v_ls'2173, v_rs'2174) ->
                              (let v_l'2175 =
                                 Obj.magic
                                   v_workMany'2152
                                   v_ls'2173
                               in
                               let v_r'2176 =
                                 Obj.magic
                                   v_workMany'2152
                                   v_rs'2174
                               in
                               Obj.magic
                                 v_optionZipWith
                                 (Obj.magic
                                    v_c'2171
                                    v_self'2172)
                                 v_l'2175
                                 v_r'2176)
                          | Option.None ->
                              (Obj.magic
                                 (Obj.magic
                                    v_defaultCase'2719
                                    ()))))
                  | CPrefixP'1709 v_x'2734 ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2735 =
                                 Obj.magic
                                   Obj.magic
                                   v_node'2165
                               in
                               let
                                 CRec'2284 ({linput = v_input'2736;lself = v_self'2737;lrightChildAlts = v_rightChildAlts'2738})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2735
                               in
                               match
                                 Obj.magic
                                   Obj.magic
                                   v_input'2736
                               with
                               | CPrefixI'1703 v__n'2739 ->
                                   (let
                                      CRec'2296 ({lconstruct = v_construct'2740})
                                    =
                                      Obj.magic
                                        Obj.magic
                                        v_input'2736
                                    in
                                    Option.Some (v_construct'2740, v_self'2737, v_rightChildAlts'2738))
                               | _ ->
                                   (Obj.magic
                                      Obj.magic
                                      (Option.None)))
                          with
                          | Option.Some (v_c'2168, v_self'2169, v_rs'2170) ->
                              (Obj.magic
                                 v_optionMap
                                 (Obj.magic
                                    v_c'2168
                                    v_self'2169)
                                 (Obj.magic
                                    v_workMany'2152
                                    v_rs'2170))
                          | Option.None ->
                              (Obj.magic
                                 (Obj.magic
                                    v_defaultCase'2719
                                    ()))))
                  | CPostfixP'1710 v_x'2741 ->
                      (Obj.magic
                         (match
                            Obj.magic
                              (let v__target'2742 =
                                 Obj.magic
                                   Obj.magic
                                   v_node'2165
                               in
                               let
                                 CRec'2303 ({linput = v_input'2743;lself = v_self'2744;lleftChildAlts = v_leftChildAlts'2745})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2742
                               in
                               match
                                 Obj.magic
                                   Obj.magic
                                   v_input'2743
                               with
                               | CPostfixI'1704 v__n'2746 ->
                                   (let
                                      CRec'2298 ({lconstruct = v_construct'2747})
                                    =
                                      Obj.magic
                                        Obj.magic
                                        v_input'2743
                                    in
                                    Option.Some (v_construct'2747, v_self'2744, v_leftChildAlts'2745))
                               | _ ->
                                   (Obj.magic
                                      Obj.magic
                                      (Option.None)))
                          with
                          | Option.Some (v_c'2177, v_self'2178, v_ls'2179) ->
                              (Obj.magic
                                 v_optionMap
                                 (Obj.magic
                                    v_c'2177
                                    v_self'2178)
                                 (Obj.magic
                                    v_workMany'2152
                                    v_ls'2179))
                          | Option.None ->
                              (Obj.magic
                                 (Obj.magic
                                    v_defaultCase'2719
                                    ()))))
                  | _ ->
                      (Obj.magic
                         (v_defaultCase'2719
                            ()))
            in match
              Obj.magic
                (let v__target'2748 =
                   Obj.magic
                     v_workMany'2152
                     v_nodes'2062
                 in
                 match
                   Obj.magic
                     Obj.magic
                     v__target'2748
                 with
                 | CSome'1610 v__n'2749 ->
                     (Option.Some (v__n'2749))
                 | _ ->
                     (Obj.magic
                        Obj.magic
                        (Option.None)))
            with
            | Option.Some (v_res'2180) ->
                (CRight'1677 (Obj.repr
                    v_res'2180))
            | Option.None ->
                (Obj.magic
                   (CLeft'1676 (Obj.repr
                       (CAmbiguities'2057 (Obj.repr
                           (Obj.magic
                              (!)
                              v_ambiguities'2151))))));;
let v_allowAll =
  fun v_cmp'2182 ->
    CDisallowSet'1686 (Obj.repr
       (Obj.magic
          Boot.Intrinsics.Mmap.empty
          v_cmp'2182));;
let v_allowNone =
  fun v_cmp'2184 ->
    CAllowSet'1685 (Obj.repr
       (Obj.magic
          Boot.Intrinsics.Mmap.empty
          v_cmp'2184));;
let v_allowOneMore =
  fun v_label'2186 ->
    fun v_set'2187 ->
      Obj.magic
        v_breakableInsertAllowSet
        v_label'2186
        v_set'2187;;
let v_allowOneLess =
  fun v_label'2189 ->
    fun v_set'2190 ->
      Obj.magic
        v_breakableRemoveAllowSet
        v_label'2189
        v_set'2190;;
let v_atom =
  fun v_label'2192 ->
    fun v_construct'2193 ->
      CBreakableAtom'1688 { llabel =
          (Obj.repr
            v_label'2192);
        lconstruct =
          (Obj.repr
            v_construct'2193) };;
let v_prefix =
  fun v_label'2195 ->
    fun v_construct'2196 ->
      fun v_rightAllow'2197 ->
        CBreakablePrefix'1690 { llabel =
            (Obj.repr
              v_label'2195);
          lconstruct =
            (Obj.repr
              v_construct'2196);
          lrightAllow =
            (Obj.repr
              v_rightAllow'2197) };;
let v_postfix =
  fun v_label'2199 ->
    fun v_construct'2200 ->
      fun v_leftAllow'2201 ->
        CBreakablePostfix'1691 { llabel =
            (Obj.repr
              v_label'2199);
          lconstruct =
            (Obj.repr
              v_construct'2200);
          lleftAllow =
            (Obj.repr
              v_leftAllow'2201) };;
let v_infix =
  fun v_label'2203 ->
    fun v_construct'2204 ->
      fun v_leftAllow'2205 ->
        fun v_rightAllow'2206 ->
          CBreakableInfix'1689 { llabel =
              (Obj.repr
                v_label'2203);
            lconstruct =
              (Obj.repr
                v_construct'2204);
            lleftAllow =
              (Obj.repr
                v_leftAllow'2205);
            lrightAllow =
              (Obj.repr
                v_rightAllow'2206) };;
let v_emptyGrammar =
  CRec'2276 { lproductions =
      (Obj.repr
        (Obj.magic
           Boot.Intrinsics.Mseq.Helpers.of_array
           [|  |]));
    lprecedences =
      (Obj.repr
        (Obj.magic
           Boot.Intrinsics.Mseq.Helpers.of_array
           [|  |])) };;
let v_addProd =
  fun v_prod'2209 ->
    fun v_gram'2210 ->
      let
        CRec'2276 v_rec'2750
      =
        Obj.magic
          v_gram'2210
      in
      CRec'2276 { v_rec'2750
        with
        lproductions =
          Obj.repr
            (Obj.magic
               Boot.Intrinsics.Mseq.snoc
               (let
                  CRec'2276 ({lproductions = v_X'2211})
                =
                  Obj.magic
                    v_gram'2210
                in
                Obj.magic
                  v_X'2211)
               v_prod'2209) };;
let v_addPrec =
  fun v_l'2213 ->
    fun v_r'2214 ->
      fun v_mayL'2215 ->
        fun v_mayR'2216 ->
          fun v_gram'2217 ->
            let
              CRec'2276 v_rec'2751
            =
              Obj.magic
                v_gram'2217
            in
            CRec'2276 { v_rec'2751
              with
              lprecedences =
                Obj.repr
                  (Obj.magic
                     Boot.Intrinsics.Mseq.snoc
                     (let
                        CRec'2276 ({lprecedences = v_X'2218})
                      =
                        Obj.magic
                          v_gram'2217
                      in
                      Obj.magic
                        v_X'2218)
                     (CRec'2315 { l0 =
                          (Obj.repr
                            (CRec'2315 { l0 =
                                 (Obj.repr
                                   v_l'2213);
                               l1 =
                                 (Obj.repr
                                   v_r'2214) }));
                        l1 =
                          (Obj.repr
                            (CRec'2274 { lmayGroupLeft =
                                 (Obj.repr
                                   v_mayL'2215);
                               lmayGroupRight =
                                 (Obj.repr
                                   v_mayR'2216) })) })) };;
let v_finalize =
  v_breakableGenGrammar;;
let v_getAtom =
  fun v_gram'2221 ->
    fun v_label'2222 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find
        v_label'2222
        (let
           CRec'2281 ({latoms = v_X'2223})
         =
           Obj.magic
             v_gram'2221
         in
         Obj.magic
           v_X'2223);;
let v_getPrefix =
  fun v_gram'2225 ->
    fun v_label'2226 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find
        v_label'2226
        (let
           CRec'2281 ({lprefixes = v_X'2227})
         =
           Obj.magic
             v_gram'2225
         in
         Obj.magic
           v_X'2227);;
let v_getPostfix =
  fun v_gram'2229 ->
    fun v_label'2230 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find
        v_label'2230
        (let
           CRec'2281 ({lpostfixes = v_X'2231})
         =
           Obj.magic
             v_gram'2229
         in
         Obj.magic
           v_X'2231);;
let v_getInfix =
  fun v_gram'2233 ->
    fun v_label'2234 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find
        v_label'2234
        (let
           CRec'2281 ({linfixes = v_X'2235})
         =
           Obj.magic
             v_gram'2233
         in
         Obj.magic
           v_X'2235);;
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
  fun v_none'2243 ->
    fun v_some'2244 ->
      fun v_opt'2245 ->
        match
          Obj.magic
            (let v__target'2752 =
               v_opt'2245
             in
             match
               Obj.magic
                 Obj.magic
                 v__target'2752
             with
             | CSome'1610 v__n'2753 ->
                 (Option.Some (v__n'2753))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None)))
        with
        | Option.Some (v_a'2246) ->
            (Obj.magic
               v_some'2244
               v_a'2246)
        | Option.None ->
            (Obj.magic
               (Obj.magic
                  v_none'2243
                  ()));;
let v_constructResult =
  v_breakableConstructResult;;
let v_either =
  fun v_left'2249 ->
    fun v_right'2250 ->
      fun v_either'2251 ->
        let v_X'2252 =
          v_either'2251
        in
        let v_defaultCase'2754 =
          fun nv_ ->
            failwith
              "FILE \"/home/vipa/Projects/static-resolvable/breakable-ml/breakable_impl.mc\" 163:4-163:7 ERROR: Reached a never term, which should be impossible in a well-typed program."
        in
        match
          Obj.magic
            v_X'2252
        with
        | CLeft'1676 v_x'2755 ->
            (let v_a'2253 =
               Obj.magic
                 Obj.magic
                 v_x'2755
             in
             Obj.magic
               v_left'2249
               v_a'2253)
        | CRight'1677 v_x'2756 ->
            (Obj.magic
               (let v_b'2254 =
                  Obj.magic
                    Obj.magic
                    v_x'2756
                in
                Obj.magic
                  v_right'2250
                  v_b'2254))
        | _ ->
            (Obj.magic
               (v_defaultCase'2754
                  ()));;
let v_foldError =
  fun v_amb'2256 ->
    fun v_err'2257 ->
      let v_X'2258 =
        v_err'2257
      in
      match
        Obj.magic
          (let v__target'2757 =
             v_X'2258
           in
           match
             Obj.magic
               Obj.magic
               v__target'2757
           with
           | CAmbiguities'2057 v__n'2758 ->
               (Option.Some (v__n'2758))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_ambs'2259) ->
          (Obj.magic
             v_amb'2256
             v_ambs'2259)
      | Option.None ->
          (Obj.magic
             (failwith
                "FILE \"/home/vipa/Projects/static-resolvable/breakable-ml/breakable_impl.mc\" 172:4-172:7 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v_seqFoldl =
  Boot.Intrinsics.Mseq.Helpers.fold_left;;
let v_ambiguity =
  fun v_f'2262 ->
    fun v_amb'2263 ->
      Obj.magic
        v_f'2262
        (let
           CRec'2314 ({lfirst = v_X'2264})
         =
           Obj.magic
             v_amb'2263
         in
         Obj.magic
           v_X'2264)
        (let
           CRec'2314 ({llast = v_X'2265})
         =
           Obj.magic
             v_amb'2263
         in
         Obj.magic
           v_X'2265)
        (let
           CRec'2314 ({lpartialResolutions = v_X'2266})
         =
           Obj.magic
             v_amb'2263
         in
         Obj.magic
           v_X'2266);;
CRec'2316 { l0 =
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

  let emptyGrammar = Obj.magic v_emptyGrammar
  let addProd prod gram = Obj.magic v_addProd prod gram
  let addPrec l r ml mr gram = Obj.magic v_addPrec l r ml mr gram

  let finalize gram = Obj.magic v_finalize compareLabel gram

  let getAtom gen label = Obj.magic v_getAtom gen label
  let getInfix gen label = Obj.magic v_getInfix gen label
  let getPrefix gen label = Obj.magic v_getPrefix gen label
  let getPostfix gen label = Obj.magic v_getPostfix gen label

  let init () = Obj.magic v_init ()

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
