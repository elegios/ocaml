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
type v_record'2501 =
  | CRec'2500 of {l0: Obj.t;l1: Obj.t;l2: Obj.t;l3: Obj.t;l4: Obj.t;l5: Obj.t;l6: Obj.t;l7: Obj.t;l8: Obj.t;l9: Obj.t;l10: Obj.t;l11: Obj.t;l12: Obj.t;l13: Obj.t;l14: Obj.t;l15: Obj.t;l16: Obj.t;l17: Obj.t;l18: Obj.t;l19: Obj.t;l20: Obj.t;l21: Obj.t;l22: Obj.t;l23: Obj.t;l24: Obj.t;l25: Obj.t;l26: Obj.t;l27: Obj.t};;
type v_record'2502 =
  | CRec'2499 of {l0: Obj.t;l1: Obj.t};;
type v_record'2503 =
  | CRec'2498 of {lproductions: Obj.t;lprecedences: Obj.t;ltopAllowed: Obj.t};;
type v_record'2504 =
  | CRec'2497 of {l0: Obj.t;l1: Obj.t;l2: Obj.t};;
type v_record'2505 =
  | CRec'2493 of {lfirst: Obj.t;llast: Obj.t};;
type v_BreakableError'2242 =
  | CAmbiguities'2243 of Obj.t;;
type v_record'2506 =
  | CRec'2492 of {lfirst: Obj.t;llast: Obj.t;lpartialResolutions: Obj.t};;
type v_record'2507 =
  | CRec'2491 of {lparents: Obj.t;lnode: Obj.t};;
type v_record'2508 =
  | CRec'2490 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t};;
type v_record'2509 =
  | CRec'2489 of {lparents: Obj.t;laddedNodesLeftChildren: Obj.t;laddedNodesRightChildren: Obj.t;ltentativeData: Obj.t;lmaxDistanceFromRoot: Obj.t};;
type v_record'2510 =
  | CRec'2488 of {lidx: Obj.t;linput: Obj.t;lself: Obj.t};;
type v_record'2511 =
  | CRec'2486 of {l0: Obj.t;l1: Obj.t;l2: Obj.t;l3: Obj.t};;
type v_record'2512 =
  | CRec'2482 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t};;
type v_record'2513 =
  | CRec'2480 of {lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t};;
type v_record'2514 =
  | CRec'2477 of {lconstruct: Obj.t;lleftAllow: Obj.t;lid: Obj.t;lallowedTop: Obj.t;lprecWhenThisIsRight: Obj.t};;
type v_record'2515 =
  | CRec'2476 of {lconstruct: Obj.t;lleftAllow: Obj.t;lrightAllow: Obj.t;lid: Obj.t;lallowedTop: Obj.t;lprecWhenThisIsRight: Obj.t};;
type v_record'2516 =
  | CRec'2475 of {lconstruct: Obj.t;lrightAllow: Obj.t;lid: Obj.t;lallowedTop: Obj.t};;
type v_record'2517 =
  | CRec'2473 of {lconstruct: Obj.t;lid: Obj.t;lallowedTop: Obj.t};;
type v_record'2518 =
  | CRec'2469 of {ltimestep: Obj.t;lnextIdx: Obj.t;lfrontier: Obj.t};;
type v_record'2519 =
  | CRec'2468 of {laddedNodesLeftChildren: Obj.t;laddedNodesRightChildren: Obj.t};;
type v_TentativeNode'1840 =
  | CTentativeLeaf'1841 of {lparents: Obj.t;lnode: Obj.t}
  | CTentativeMid'1842 of {lparents: Obj.t;laddedNodesLeftChildren: Obj.t;laddedNodesRightChildren: Obj.t;ltentativeData: Obj.t;lmaxDistanceFromRoot: Obj.t}
  | CTentativeRoot'1843 of {laddedNodesLeftChildren: Obj.t;laddedNodesRightChildren: Obj.t};;
type v_TentativeData'1836 =
  | CInfixT'1837 of {lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t}
  | CPrefixT'1838 of {lidx: Obj.t;linput: Obj.t;lself: Obj.t};;
type v_record'2520 =
  | CRec'2462 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lrightChildAlts: Obj.t};;
type v_record'2521 =
  | CRec'2461 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t;lrightChildAlts: Obj.t};;
type v_PermanentNode'1831 =
  | CAtomP'1832 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t}
  | CInfixP'1833 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t;lrightChildAlts: Obj.t}
  | CPrefixP'1834 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lrightChildAlts: Obj.t}
  | CPostfixP'1835 of {lid: Obj.t;lidx: Obj.t;linput: Obj.t;lself: Obj.t;lleftChildAlts: Obj.t};;
type v_record'2522 =
  | CRec'2459 of {latoms: Obj.t;lprefixes: Obj.t;linfixes: Obj.t;lpostfixes: Obj.t};;
type v_BreakableInput'1825 =
  | CAtomI'1826 of {lconstruct: Obj.t;lid: Obj.t;lallowedTop: Obj.t}
  | CInfixI'1827 of {lconstruct: Obj.t;lleftAllow: Obj.t;lrightAllow: Obj.t;lid: Obj.t;lallowedTop: Obj.t;lprecWhenThisIsRight: Obj.t}
  | CPrefixI'1828 of {lconstruct: Obj.t;lrightAllow: Obj.t;lid: Obj.t;lallowedTop: Obj.t}
  | CPostfixI'1829 of {lconstruct: Obj.t;lleftAllow: Obj.t;lid: Obj.t;lallowedTop: Obj.t;lprecWhenThisIsRight: Obj.t};;
type v_record'2523 =
  | CRec'2452 of {lmayGroupLeft: Obj.t;lmayGroupRight: Obj.t};;
type v_record'2524 =
  | CRec'2451 of {llabel: Obj.t;lconstruct: Obj.t;lleftAllow: Obj.t};;
type v_record'2525 =
  | CRec'2450 of {llabel: Obj.t;lconstruct: Obj.t;lrightAllow: Obj.t};;
type v_record'2526 =
  | CRec'2449 of {llabel: Obj.t;lconstruct: Obj.t;lleftAllow: Obj.t;lrightAllow: Obj.t};;
type v_record'2527 =
  | CRec'2448 of {llabel: Obj.t;lconstruct: Obj.t};;
type v_BreakableProduction'1812 =
  | CBreakableAtom'1813 of {llabel: Obj.t;lconstruct: Obj.t}
  | CBreakableInfix'1814 of {llabel: Obj.t;lconstruct: Obj.t;lleftAllow: Obj.t;lrightAllow: Obj.t}
  | CBreakablePrefix'1815 of {llabel: Obj.t;lconstruct: Obj.t;lrightAllow: Obj.t}
  | CBreakablePostfix'1816 of {llabel: Obj.t;lconstruct: Obj.t;lleftAllow: Obj.t};;
type v_AllowSet'1807 =
  | CAllowSet'1808 of Obj.t
  | CDisallowSet'1809 of Obj.t;;
type v_Either'1798 =
  | CLeft'1799 of Obj.t
  | CRight'1800 of Obj.t;;
type v_Option'1689 =
  | CSome'1690 of Obj.t
  | CNone'1691;;
let v_not =
  fun v_a'1684 ->
    if
      Obj.magic
        v_a'1684
    then
      false
    else
      Obj.magic
        true;;
let v_or =
  fun v_a'1686 ->
    fun v_b'1687 ->
      if
        Obj.magic
          v_a'1686
      then
        true
      else
        Obj.magic
          v_b'1687;;
let v_optionMap =
  fun v_f'1692 ->
    fun v_o'1693 ->
      match
        Obj.magic
          (let v__target'2528 =
             v_o'1693
           in
           match
             Obj.magic
               Obj.magic
               v__target'2528
           with
           | CSome'1690 v__n'2529 ->
               (Option.Some (v__n'2529))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_t'1694) ->
          (CSome'1690 (Obj.repr
              (Obj.magic
                 v_f'1692
                 v_t'1694)))
      | Option.None ->
          (Obj.magic
             CNone'1691);;
let v_optionGetOrElse =
  fun v_d'1696 ->
    fun v_o'1697 ->
      match
        Obj.magic
          (let v__target'2530 =
             v_o'1697
           in
           match
             Obj.magic
               Obj.magic
               v__target'2530
           with
           | CSome'1690 v__n'2531 ->
               (Option.Some (v__n'2531))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_t'1698) ->
          v_t'1698
      | Option.None ->
          (Obj.magic
             (Obj.magic
                v_d'1696
                ()));;
let v_optionOrElse =
  fun v_f'1700 ->
    fun v_o'1701 ->
      Obj.magic
        v_optionGetOrElse
        v_f'1700
        (Obj.magic
           v_optionMap
           (fun v_x'1702 ->
              CSome'1690 (Obj.repr
                 v_x'1702))
           v_o'1701);;
let v_optionOr =
  fun v_o1'1704 ->
    fun v_o2'1705 ->
      Obj.magic
        v_optionOrElse
        (fun v_'1706 ->
           v_o2'1705)
        v_o1'1704;;
let v_mapOption =
  fun v_f'1708 ->
    let rec v_work'1709 =
        fun v_as'1710 ->
          match
            Obj.magic
              (let v__target'2532 =
                 v_as'1710
               in
               if
                 Obj.magic
                   ((<) : int -> int -> bool)
                   (Obj.magic
                      Boot.Intrinsics.Mseq.length
                      v__target'2532)
                   1
               then
                 Option.None
               else
                 Obj.magic
                   Obj.magic
                   (let
                      (v__prefix'2533, v__splitTemp'2534)
                    =
                      Obj.magic
                        Boot.Intrinsics.Mseq.split_at
                        v__target'2532
                        1
                    in
                    let
                      (v__middle'2535, v__postfix'2536)
                    =
                      Obj.magic
                        Boot.Intrinsics.Mseq.split_at
                        v__splitTemp'2534
                        (Obj.magic
                           Int.sub
                           (Obj.magic
                              Boot.Intrinsics.Mseq.length
                              v__splitTemp'2534)
                           0)
                    in
                    let v__seqElem'2537 =
                      Obj.magic
                        Boot.Intrinsics.Mseq.get
                        v__prefix'2533
                        0
                    in
                    Option.Some (v__seqElem'2537, v__middle'2535)))
          with
          | Option.Some (v_a'1711, v_as'1712) ->
              (match
                 Obj.magic
                   (let v__target'2538 =
                      Obj.magic
                        v_f'1708
                        v_a'1711
                    in
                    match
                      Obj.magic
                        Obj.magic
                        v__target'2538
                    with
                    | CSome'1690 v__n'2539 ->
                        (Option.Some (v__n'2539))
                    | _ ->
                        (Obj.magic
                           Obj.magic
                           (Option.None)))
               with
               | Option.Some (v_b'1713) ->
                   (Obj.magic
                      Boot.Intrinsics.Mseq.cons
                      v_b'1713
                      (Obj.magic
                         v_work'1709
                         v_as'1712))
               | Option.None ->
                   (Obj.magic
                      (Obj.magic
                         v_work'1709
                         v_as'1712)))
          | Option.None ->
              (Obj.magic
                 (Obj.magic
                    Boot.Intrinsics.Mseq.Helpers.of_array
                    [|  |]))
    in v_work'1709;;
let v_for_ =
  fun v_xs'1715 ->
    fun v_f'1716 ->
      Obj.magic
        Boot.Intrinsics.Mseq.iter
        v_f'1716
        v_xs'1715;;
let rec v_any =
    fun v_p'1719 ->
      fun v_seq'1720 ->
        if
          Obj.magic
            (Obj.magic
               Boot.Intrinsics.Mseq.null
               v_seq'1720)
        then
          false
        else
          Obj.magic
            (if
               Obj.magic
                 (Obj.magic
                    v_p'1719
                    (Obj.magic
                       Boot.Intrinsics.Mseq.head
                       v_seq'1720))
             then
               true
             else
               Obj.magic
                 (Obj.magic
                    v_any
                    v_p'1719
                    (Obj.magic
                       Boot.Intrinsics.Mseq.tail
                       v_seq'1720)));;
let v_join =
  fun v_seqs'1721 ->
    Obj.magic
      Boot.Intrinsics.Mseq.Helpers.fold_left
      Boot.Intrinsics.Mseq.concat
      (Obj.magic
         Boot.Intrinsics.Mseq.Helpers.of_array
         [|  |])
      v_seqs'1721;;
let v_seqLiftA2 =
  fun v_f'1723 ->
    fun v_as'1724 ->
      fun v_bs'1725 ->
        Obj.magic
          v_join
          (Obj.magic
             Boot.Intrinsics.Mseq.map
             (fun v_a'1726 ->
                Obj.magic
                  Boot.Intrinsics.Mseq.map
                  (Obj.magic
                     v_f'1723
                     v_a'1726)
                  v_bs'1725)
             v_as'1724);;
let rec v_filter =
    fun v_p'1729 ->
      fun v_seq'1730 ->
        if
          Obj.magic
            (Obj.magic
               Boot.Intrinsics.Mseq.null
               v_seq'1730)
        then
          Obj.magic
            Boot.Intrinsics.Mseq.Helpers.of_array
            [|  |]
        else
          Obj.magic
            (if
               Obj.magic
                 (Obj.magic
                    v_p'1729
                    (Obj.magic
                       Boot.Intrinsics.Mseq.head
                       v_seq'1730))
             then
               Obj.magic
                 Boot.Intrinsics.Mseq.cons
                 (Obj.magic
                    Boot.Intrinsics.Mseq.head
                    v_seq'1730)
                 (Obj.magic
                    v_filter
                    v_p'1729
                    (Obj.magic
                       Boot.Intrinsics.Mseq.tail
                       v_seq'1730))
             else
               Obj.magic
                 (Obj.magic
                    v_filter
                    v_p'1729
                    (Obj.magic
                       Boot.Intrinsics.Mseq.tail
                       v_seq'1730)));;
let v_partition =
  fun v_p'1731 ->
    fun v_seq'1732 ->
      let rec v_work'1733 =
          fun v_l'1734 ->
            fun v_r'1735 ->
              fun v_seq'1736 ->
                if
                  Obj.magic
                    Int.equal
                    0
                    (Obj.magic
                       Boot.Intrinsics.Mseq.length
                       v_seq'1736)
                then
                  CRec'2499 { l0 =
                      (Obj.repr
                        v_l'1734);
                    l1 =
                      (Obj.repr
                        v_r'1735) }
                else
                  Obj.magic
                    (match
                       Obj.magic
                         (let v__target'2540 =
                            v_seq'1736
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
                               Option.Some (v__seqElem'2545, v__middle'2543)))
                     with
                     | Option.Some (v_s'1737, v_seq'1738) ->
                         (if
                            Obj.magic
                              (Obj.magic
                                 v_p'1731
                                 v_s'1737)
                          then
                            Obj.magic
                              v_work'1733
                              (Obj.magic
                                 Boot.Intrinsics.Mseq.cons
                                 v_s'1737
                                 v_l'1734)
                              v_r'1735
                              v_seq'1738
                          else
                            Obj.magic
                              (Obj.magic
                                 v_work'1733
                                 v_l'1734
                                 (Obj.magic
                                    Boot.Intrinsics.Mseq.cons
                                    v_s'1737
                                    v_r'1735)
                                 v_seq'1738))
                     | Option.None ->
                         (Obj.magic
                            (failwith
                               "FILE \"/home/vipa/.local/lib/mcore/stdlib/seq.mc\" 225:9-225:14 ERROR: Reached a never term, which should be impossible in a well-typed program.")))
      in Obj.magic
        v_work'1733
        (Obj.magic
           Boot.Intrinsics.Mseq.Helpers.of_array
           [|  |])
        (Obj.magic
           Boot.Intrinsics.Mseq.Helpers.of_array
           [|  |])
        (Obj.magic
           Boot.Intrinsics.Mseq.reverse
           v_seq'1732);;
let v_min =
  fun v_cmp'1740 ->
    fun v_seq'1741 ->
      let rec v_work'1742 =
          fun v_e'1743 ->
            fun v_seq'1744 ->
              if
                Obj.magic
                  (Obj.magic
                     Boot.Intrinsics.Mseq.null
                     v_seq'1744)
              then
                CSome'1690 (Obj.repr
                   v_e'1743)
              else
                Obj.magic
                  (let v_h'1745 =
                     Obj.magic
                       Boot.Intrinsics.Mseq.head
                       v_seq'1744
                   in
                   let v_t'1746 =
                     Obj.magic
                       Boot.Intrinsics.Mseq.tail
                       v_seq'1744
                   in
                   if
                     Obj.magic
                       (Obj.magic
                          ((<) : int -> int -> bool)
                          (Obj.magic
                             v_cmp'1740
                             v_e'1743
                             v_h'1745)
                          0)
                   then
                     Obj.magic
                       v_work'1742
                       v_e'1743
                       v_t'1746
                   else
                     Obj.magic
                       (Obj.magic
                          v_work'1742
                          v_h'1745
                          v_t'1746))
      in if
        Obj.magic
          (Obj.magic
             Boot.Intrinsics.Mseq.null
             v_seq'1741)
      then
        CNone'1691
      else
        Obj.magic
          (Obj.magic
             v_work'1742
             (Obj.magic
                Boot.Intrinsics.Mseq.head
                v_seq'1741)
             (Obj.magic
                Boot.Intrinsics.Mseq.tail
                v_seq'1741));;
let v_minOrElse =
  fun v_d'1748 ->
    fun v_cmp'1749 ->
      fun v_seq'1750 ->
        Obj.magic
          v_optionGetOrElse
          v_d'1748
          (Obj.magic
             v_min
             v_cmp'1749
             v_seq'1750);;
let v_maxOrElse =
  fun v_d'1752 ->
    fun v_cmp'1753 ->
      Obj.magic
        v_minOrElse
        v_d'1752
        (fun v_l'1754 ->
           fun v_r'1755 ->
             Obj.magic
               v_cmp'1753
               v_r'1755
               v_l'1754);;
let v_mapLookup =
  fun v_k'1757 ->
    fun v_m'1758 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find_apply_or_else
        (fun v_v'1759 ->
           CSome'1690 (Obj.repr
              v_v'1759))
        (fun v_'1760 ->
           CNone'1691)
        v_k'1757
        v_m'1758;;
let v_mapUnion =
  fun v_l'1762 ->
    fun v_r'1763 ->
      Obj.magic
        Boot.Intrinsics.Mseq.Helpers.fold_left
        (fun v_acc'1764 ->
           fun v_binding'1765 ->
             Obj.magic
               Boot.Intrinsics.Mmap.insert
               (let
                  CRec'2499 ({l0 = v_X'1766})
                =
                  Obj.magic
                    v_binding'1765
                in
                Obj.magic
                  v_X'1766)
               (let
                  CRec'2499 ({l1 = v_X'1767})
                =
                  Obj.magic
                    v_binding'1765
                in
                Obj.magic
                  v_X'1767)
               v_acc'1764)
        v_l'1762
        (Obj.magic
           Boot.Intrinsics.Mmap.bindings
           v_r'1763);;
let v_mapFromSeq =
  fun v_cmp'1769 ->
    fun v_bindings'1770 ->
      Obj.magic
        Boot.Intrinsics.Mseq.Helpers.fold_left
        (fun v_acc'1771 ->
           fun v_binding'1772 ->
             Obj.magic
               Boot.Intrinsics.Mmap.insert
               (let
                  CRec'2499 ({l0 = v_X'1773})
                =
                  Obj.magic
                    v_binding'1772
                in
                Obj.magic
                  v_X'1773)
               (let
                  CRec'2499 ({l1 = v_X'1774})
                =
                  Obj.magic
                    v_binding'1772
                in
                Obj.magic
                  v_X'1774)
               v_acc'1771)
        (Obj.magic
           Boot.Intrinsics.Mmap.empty
           v_cmp'1769)
        v_bindings'1770;;
let v_mapKeys =
  fun v_m'1776 ->
    Obj.magic
      Boot.Intrinsics.Mmap.fold_with_key
      (fun v_ks'1777 ->
         fun v_k'1778 ->
           fun v_'1779 ->
             Obj.magic
               Boot.Intrinsics.Mseq.snoc
               v_ks'1777
               v_k'1778)
      (Obj.magic
         Boot.Intrinsics.Mseq.Helpers.of_array
         [|  |])
      v_m'1776;;
let v_setEmpty =
  fun v_cmp'1782 ->
    Obj.magic
      Boot.Intrinsics.Mmap.empty
      v_cmp'1782;;
let v_setInsert =
  fun v_e'1784 ->
    fun v_s'1785 ->
      Obj.magic
        Boot.Intrinsics.Mmap.insert
        v_e'1784
        ()
        v_s'1785;;
let v_setMem =
  fun v_e'1787 ->
    fun v_s'1788 ->
      Obj.magic
        Boot.Intrinsics.Mmap.mem
        v_e'1787
        v_s'1788;;
let v_setUnion =
  fun v_s1'1790 ->
    fun v_s2'1791 ->
      Obj.magic
        v_mapUnion
        v_s1'1790
        v_s2'1791;;
let v_setOfSeq =
  fun v_cmp'1793 ->
    fun v_seq'1794 ->
      Obj.magic
        Boot.Intrinsics.Mseq.Helpers.fold_right
        v_setInsert
        (Obj.magic
           v_setEmpty
           v_cmp'1793)
        v_seq'1794;;
let v_setToSeq =
  fun v_s'1796 ->
    Obj.magic
      v_mapKeys
      v_s'1796;;
let v_printLn =
  fun v_s'1801 ->
    let v_'1802 =
      Obj.magic
        Boot.Intrinsics.IO.print
        (Obj.magic
           Boot.Intrinsics.Mseq.concat
           v_s'1801
           (Obj.magic
              Boot.Intrinsics.Mseq.Helpers.of_array
              [| (10) |]))
    in
    Obj.magic
      Boot.Intrinsics.IO.flush_stdout
      ();;
let v_dprintLn =
  fun v_x'1804 ->
    let v_'1805 =
      Obj.magic
        Boot.Intrinsics.IO.dprint
        v_x'1804
    in
    Obj.magic
      v_printLn
      (Obj.magic
         Boot.Intrinsics.Mseq.Helpers.of_array
         [|  |]);;
let v__isWhitelist =
  fun v_a'1810 ->
    match
      Obj.magic
        (let v__target'2546 =
           v_a'1810
         in
         match
           Obj.magic
             Obj.magic
             v__target'2546
         with
         | CAllowSet'1808 v__n'2547 ->
             (Option.Some ())
         | _ ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some () ->
        true
    | Option.None ->
        (Obj.magic
           false);;
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
  fun v_n'1853 ->
    match
      Obj.magic
        (let v__target'2548 =
           v_n'1853
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2548
             with
             | CTentativeLeaf'1841 v__n'2549 ->
                 (let
                    CRec'2491 ({lparents = v_parents'2550})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2548
                  in
                  Option.Some (v_parents'2550))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2553 ->
               (Option.Some v__x'2553)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     Obj.magic
                       Obj.magic
                       v__target'2548
                   with
                   | CTentativeMid'1842 v__n'2551 ->
                       (let
                          CRec'2489 ({lparents = v_parents'2552})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2548
                        in
                        Option.Some (v_parents'2552))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_ps'1854) ->
             (Option.Some (v_ps'1854))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_ps'1854) ->
        (CSome'1690 (Obj.repr
            v_ps'1854))
    | Option.None ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2554 =
                   v_n'1853
                 in
                 match
                   Obj.magic
                     Obj.magic
                     v__target'2554
                 with
                 | CTentativeRoot'1843 v__n'2555 ->
                     (Option.Some ())
                 | _ ->
                     (Obj.magic
                        Obj.magic
                        (Option.None)))
            with
            | Option.Some () ->
                CNone'1691
            | Option.None ->
                (Obj.magic
                   (failwith
                      "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 283:4-283:9 ERROR: Reached a never term, which should be impossible in a well-typed program."))));;
let v__opIdI =
  fun v_input'1856 ->
    match
      Obj.magic
        (let v__target'2556 =
           v_input'1856
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2556
             with
             | CAtomI'1826 v__n'2557 ->
                 (let
                    CRec'2473 ({lid = v_id'2558})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2556
                  in
                  Option.Some (v_id'2558))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2567 ->
               (Option.Some v__x'2567)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     match
                       match
                         Obj.magic
                           Obj.magic
                           v__target'2556
                       with
                       | CInfixI'1827 v__n'2559 ->
                           (let
                              CRec'2476 ({lid = v_id'2560})
                            =
                              Obj.magic
                                Obj.magic
                                v__target'2556
                            in
                            Option.Some (v_id'2560))
                       | _ ->
                           (Obj.magic
                              Obj.magic
                              (Option.None))
                     with
                     | Option.Some v__x'2566 ->
                         (Option.Some v__x'2566)
                     | Option.None ->
                         (Obj.magic
                            Obj.magic
                            (match
                               match
                                 match
                                   Obj.magic
                                     Obj.magic
                                     v__target'2556
                                 with
                                 | CPrefixI'1828 v__n'2561 ->
                                     (let
                                        CRec'2475 ({lid = v_id'2562})
                                      =
                                        Obj.magic
                                          Obj.magic
                                          v__target'2556
                                      in
                                      Option.Some (v_id'2562))
                                 | _ ->
                                     (Obj.magic
                                        Obj.magic
                                        (Option.None))
                               with
                               | Option.Some v__x'2565 ->
                                   (Option.Some v__x'2565)
                               | Option.None ->
                                   (Obj.magic
                                      Obj.magic
                                      (match
                                         Obj.magic
                                           Obj.magic
                                           v__target'2556
                                       with
                                       | CPostfixI'1829 v__n'2563 ->
                                           (let
                                              CRec'2477 ({lid = v_id'2564})
                                            =
                                              Obj.magic
                                                Obj.magic
                                                v__target'2556
                                            in
                                            Option.Some (v_id'2564))
                                       | _ ->
                                           (Obj.magic
                                              Obj.magic
                                              (Option.None))))
                             with
                             | Option.Some (v_id'1857) ->
                                 (Option.Some (v_id'1857))
                             | Option.None ->
                                 (Obj.magic
                                    Obj.magic
                                    (Option.None))))
                   with
                   | Option.Some (v_id'1857) ->
                       (Option.Some (v_id'1857))
                   | Option.None ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_id'1857) ->
             (Option.Some (v_id'1857))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_id'1857) ->
        v_id'1857
    | Option.None ->
        (Obj.magic
           (failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 294:9-294:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__opIdP =
  fun v_node'1859 ->
    let v_defaultCase'2568 =
      fun nv_ ->
        failwith
          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 303:4-303:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
    in
    match
      Obj.magic
        v_node'1859
    with
    | CAtomP'1832 v_x'2569 ->
        (match
           Obj.magic
             (let v__target'2570 =
                Obj.magic
                  Obj.magic
                  v_node'1859
              in
              let
                CRec'2490 ({linput = v_input'2571})
              =
                Obj.magic
                  Obj.magic
                  v__target'2570
              in
              Option.Some (v_input'2571))
         with
         | Option.Some (v_input'1860) ->
             (Obj.magic
                v__opIdI
                v_input'1860)
         | Option.None ->
             (Obj.magic
                (Obj.magic
                   v_defaultCase'2568
                   ())))
    | CInfixP'1833 v_x'2572 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2573 =
                   Obj.magic
                     Obj.magic
                     v_node'1859
                 in
                 let
                   CRec'2461 ({linput = v_input'2574})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2573
                 in
                 Option.Some (v_input'2574))
            with
            | Option.Some (v_input'1861) ->
                (Obj.magic
                   v__opIdI
                   v_input'1861)
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2568
                      ()))))
    | CPrefixP'1834 v_x'2575 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2576 =
                   Obj.magic
                     Obj.magic
                     v_node'1859
                 in
                 let
                   CRec'2462 ({linput = v_input'2577})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2576
                 in
                 Option.Some (v_input'2577))
            with
            | Option.Some (v_input'1862) ->
                (Obj.magic
                   v__opIdI
                   v_input'1862)
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2568
                      ()))))
    | CPostfixP'1835 v_x'2578 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2579 =
                   Obj.magic
                     Obj.magic
                     v_node'1859
                 in
                 let
                   CRec'2482 ({linput = v_input'2580})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2579
                 in
                 Option.Some (v_input'2580))
            with
            | Option.Some (v_input'1863) ->
                (Obj.magic
                   v__opIdI
                   v_input'1863)
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2568
                      ()))))
    | _ ->
        (Obj.magic
           (v_defaultCase'2568
              ()));;
let v__opIdxP =
  fun v_node'1865 ->
    let v_defaultCase'2581 =
      fun nv_ ->
        failwith
          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 312:4-312:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
    in
    match
      Obj.magic
        v_node'1865
    with
    | CAtomP'1832 v_x'2582 ->
        (match
           Obj.magic
             (let v__target'2583 =
                Obj.magic
                  Obj.magic
                  v_node'1865
              in
              let
                CRec'2490 ({lidx = v_idx'2584})
              =
                Obj.magic
                  Obj.magic
                  v__target'2583
              in
              Option.Some (v_idx'2584))
         with
         | Option.Some (v_idx'1866) ->
             v_idx'1866
         | Option.None ->
             (Obj.magic
                (Obj.magic
                   v_defaultCase'2581
                   ())))
    | CInfixP'1833 v_x'2585 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2586 =
                   Obj.magic
                     Obj.magic
                     v_node'1865
                 in
                 let
                   CRec'2461 ({lidx = v_idx'2587})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2586
                 in
                 Option.Some (v_idx'2587))
            with
            | Option.Some (v_idx'1867) ->
                v_idx'1867
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2581
                      ()))))
    | CPrefixP'1834 v_x'2588 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2589 =
                   Obj.magic
                     Obj.magic
                     v_node'1865
                 in
                 let
                   CRec'2462 ({lidx = v_idx'2590})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2589
                 in
                 Option.Some (v_idx'2590))
            with
            | Option.Some (v_idx'1868) ->
                v_idx'1868
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2581
                      ()))))
    | CPostfixP'1835 v_x'2591 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2592 =
                   Obj.magic
                     Obj.magic
                     v_node'1865
                 in
                 let
                   CRec'2482 ({lidx = v_idx'2593})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2592
                 in
                 Option.Some (v_idx'2593))
            with
            | Option.Some (v_idx'1869) ->
                v_idx'1869
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2581
                      ()))))
    | _ ->
        (Obj.magic
           (v_defaultCase'2581
              ()));;
let v__opIdTD =
  fun v_data'1871 ->
    match
      Obj.magic
        (let v__target'2594 =
           v_data'1871
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2594
             with
             | CInfixT'1837 v__n'2595 ->
                 (let
                    CRec'2480 ({linput = v_input'2596})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2594
                  in
                  Option.Some (v_input'2596))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2599 ->
               (Option.Some v__x'2599)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     Obj.magic
                       Obj.magic
                       v__target'2594
                   with
                   | CPrefixT'1838 v__n'2597 ->
                       (let
                          CRec'2488 ({linput = v_input'2598})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2594
                        in
                        Option.Some (v_input'2598))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_input'1872) ->
             (Option.Some (v_input'1872))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_input'1872) ->
        (Obj.magic
           v__opIdI
           v_input'1872)
    | Option.None ->
        (Obj.magic
           (failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 318:4-318:9 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__opIdT =
  fun v_node'1874 ->
    let v_defaultCase'2600 =
      fun nv_ ->
        failwith
          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 326:4-326:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
    in
    match
      Obj.magic
        v_node'1874
    with
    | CTentativeLeaf'1841 v_x'2601 ->
        (match
           Obj.magic
             (let v__target'2602 =
                Obj.magic
                  Obj.magic
                  v_node'1874
              in
              let
                CRec'2491 ({lnode = v_node'2603})
              =
                Obj.magic
                  Obj.magic
                  v__target'2602
              in
              Option.Some (v_node'2603))
         with
         | Option.Some (v_node'1875) ->
             (Obj.magic
                v__opIdP
                v_node'1875)
         | Option.None ->
             (Obj.magic
                (Obj.magic
                   v_defaultCase'2600
                   ())))
    | CTentativeMid'1842 v_x'2604 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2605 =
                   Obj.magic
                     Obj.magic
                     v_node'1874
                 in
                 let
                   CRec'2489 ({ltentativeData = v_tentativeData'2606})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2605
                 in
                 Option.Some (v_tentativeData'2606))
            with
            | Option.Some (v_data'1876) ->
                (Obj.magic
                   v__opIdTD
                   v_data'1876)
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2600
                      ()))))
    | CTentativeRoot'1843 v_x'2607 ->
        (Obj.magic
           v__rootID)
    | _ ->
        (Obj.magic
           (v_defaultCase'2600
              ()));;
let v__addedNodesLeftChildren =
  fun v_node'1878 ->
    match
      Obj.magic
        (let v__target'2608 =
           v_node'1878
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2608
             with
             | CTentativeRoot'1843 v__n'2609 ->
                 (let
                    CRec'2468 ({laddedNodesLeftChildren = v_addedNodesLeftChildren'2610})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2608
                  in
                  Option.Some (v_addedNodesLeftChildren'2610))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2613 ->
               (Option.Some v__x'2613)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     Obj.magic
                       Obj.magic
                       v__target'2608
                   with
                   | CTentativeMid'1842 v__n'2611 ->
                       (let
                          CRec'2489 ({laddedNodesLeftChildren = v_addedNodesLeftChildren'2612})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2608
                        in
                        Option.Some (v_addedNodesLeftChildren'2612))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_x'1879) ->
             (Option.Some (v_x'1879))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_x'1879) ->
        v_x'1879
    | Option.None ->
        (Obj.magic
           (failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 333:9-333:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__addedNodesRightChildren =
  fun v_node'1881 ->
    match
      Obj.magic
        (let v__target'2614 =
           v_node'1881
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2614
             with
             | CTentativeRoot'1843 v__n'2615 ->
                 (let
                    CRec'2468 ({laddedNodesRightChildren = v_addedNodesRightChildren'2616})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2614
                  in
                  Option.Some (v_addedNodesRightChildren'2616))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2619 ->
               (Option.Some v__x'2619)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     Obj.magic
                       Obj.magic
                       v__target'2614
                   with
                   | CTentativeMid'1842 v__n'2617 ->
                       (let
                          CRec'2489 ({laddedNodesRightChildren = v_addedNodesRightChildren'2618})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2614
                        in
                        Option.Some (v_addedNodesRightChildren'2618))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_x'1882) ->
             (Option.Some (v_x'1882))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_x'1882) ->
        v_x'1882
    | Option.None ->
        (Obj.magic
           (failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 340:9-340:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__isTopAllowedP =
  fun v_p'1884 ->
    let v_X'1885 =
      v_p'1884
    in
    let v_defaultCase'2620 =
      fun nv_ ->
        failwith
          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 347:2-347:5 ERROR: Reached a never term, which should be impossible in a well-typed program."
    in
    match
      Obj.magic
        v_X'1885
    with
    | CAtomP'1832 v_x'2621 ->
        (match
           Obj.magic
             (let v__target'2622 =
                Obj.magic
                  Obj.magic
                  v_X'1885
              in
              let
                CRec'2490 ({linput = v_input'2623})
              =
                Obj.magic
                  Obj.magic
                  v__target'2622
              in
              match
                Obj.magic
                  Obj.magic
                  v_input'2623
              with
              | CAtomI'1826 v__n'2624 ->
                  (let
                     CRec'2473 ({lallowedTop = v_allowedTop'2625})
                   =
                     Obj.magic
                       Obj.magic
                       v_input'2623
                   in
                   Option.Some (v_allowedTop'2625))
              | _ ->
                  (Obj.magic
                     Obj.magic
                     (Option.None)))
         with
         | Option.Some (v_allowedTop'1886) ->
             v_allowedTop'1886
         | Option.None ->
             (Obj.magic
                (Obj.magic
                   v_defaultCase'2620
                   ())))
    | CInfixP'1833 v_x'2626 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2627 =
                   Obj.magic
                     Obj.magic
                     v_X'1885
                 in
                 let
                   CRec'2461 ({linput = v_input'2628})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2627
                 in
                 match
                   Obj.magic
                     Obj.magic
                     v_input'2628
                 with
                 | CInfixI'1827 v__n'2629 ->
                     (let
                        CRec'2476 ({lallowedTop = v_allowedTop'2630})
                      =
                        Obj.magic
                          Obj.magic
                          v_input'2628
                      in
                      Option.Some (v_allowedTop'2630))
                 | _ ->
                     (Obj.magic
                        Obj.magic
                        (Option.None)))
            with
            | Option.Some (v_allowedTop'1887) ->
                v_allowedTop'1887
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2620
                      ()))))
    | CPrefixP'1834 v_x'2631 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2632 =
                   Obj.magic
                     Obj.magic
                     v_X'1885
                 in
                 let
                   CRec'2462 ({linput = v_input'2633})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2632
                 in
                 match
                   Obj.magic
                     Obj.magic
                     v_input'2633
                 with
                 | CPrefixI'1828 v__n'2634 ->
                     (let
                        CRec'2475 ({lallowedTop = v_allowedTop'2635})
                      =
                        Obj.magic
                          Obj.magic
                          v_input'2633
                      in
                      Option.Some (v_allowedTop'2635))
                 | _ ->
                     (Obj.magic
                        Obj.magic
                        (Option.None)))
            with
            | Option.Some (v_allowedTop'1888) ->
                v_allowedTop'1888
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2620
                      ()))))
    | CPostfixP'1835 v_x'2636 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2637 =
                   Obj.magic
                     Obj.magic
                     v_X'1885
                 in
                 let
                   CRec'2482 ({linput = v_input'2638})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2637
                 in
                 match
                   Obj.magic
                     Obj.magic
                     v_input'2638
                 with
                 | CPostfixI'1829 v__n'2639 ->
                     (let
                        CRec'2477 ({lallowedTop = v_allowedTop'2640})
                      =
                        Obj.magic
                          Obj.magic
                          v_input'2638
                      in
                      Option.Some (v_allowedTop'2640))
                 | _ ->
                     (Obj.magic
                        Obj.magic
                        (Option.None)))
            with
            | Option.Some (v_allowedTop'1889) ->
                v_allowedTop'1889
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2620
                      ()))))
    | _ ->
        (Obj.magic
           (v_defaultCase'2620
              ()));;
let v__selfP =
  fun v_p'1891 ->
    match
      Obj.magic
        (let v__target'2641 =
           v_p'1891
         in
         match
           match
             match
               Obj.magic
                 Obj.magic
                 v__target'2641
             with
             | CAtomP'1832 v__n'2642 ->
                 (let
                    CRec'2490 ({lself = v_self'2643})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2641
                  in
                  Option.Some (v_self'2643))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None))
           with
           | Option.Some v__x'2652 ->
               (Option.Some v__x'2652)
           | Option.None ->
               (Obj.magic
                  Obj.magic
                  (match
                     match
                       match
                         Obj.magic
                           Obj.magic
                           v__target'2641
                       with
                       | CInfixP'1833 v__n'2644 ->
                           (let
                              CRec'2461 ({lself = v_self'2645})
                            =
                              Obj.magic
                                Obj.magic
                                v__target'2641
                            in
                            Option.Some (v_self'2645))
                       | _ ->
                           (Obj.magic
                              Obj.magic
                              (Option.None))
                     with
                     | Option.Some v__x'2651 ->
                         (Option.Some v__x'2651)
                     | Option.None ->
                         (Obj.magic
                            Obj.magic
                            (match
                               match
                                 match
                                   Obj.magic
                                     Obj.magic
                                     v__target'2641
                                 with
                                 | CPrefixP'1834 v__n'2646 ->
                                     (let
                                        CRec'2462 ({lself = v_self'2647})
                                      =
                                        Obj.magic
                                          Obj.magic
                                          v__target'2641
                                      in
                                      Option.Some (v_self'2647))
                                 | _ ->
                                     (Obj.magic
                                        Obj.magic
                                        (Option.None))
                               with
                               | Option.Some v__x'2650 ->
                                   (Option.Some v__x'2650)
                               | Option.None ->
                                   (Obj.magic
                                      Obj.magic
                                      (match
                                         Obj.magic
                                           Obj.magic
                                           v__target'2641
                                       with
                                       | CPostfixP'1835 v__n'2648 ->
                                           (let
                                              CRec'2482 ({lself = v_self'2649})
                                            =
                                              Obj.magic
                                                Obj.magic
                                                v__target'2641
                                            in
                                            Option.Some (v_self'2649))
                                       | _ ->
                                           (Obj.magic
                                              Obj.magic
                                              (Option.None))))
                             with
                             | Option.Some (v_self'1892) ->
                                 (Option.Some (v_self'1892))
                             | Option.None ->
                                 (Obj.magic
                                    Obj.magic
                                    (Option.None))))
                   with
                   | Option.Some (v_self'1892) ->
                       (Option.Some (v_self'1892))
                   | Option.None ->
                       (Obj.magic
                          Obj.magic
                          (Option.None))))
         with
         | Option.Some (v_self'1892) ->
             (Option.Some (v_self'1892))
         | Option.None ->
             (Obj.magic
                Obj.magic
                (Option.None)))
    with
    | Option.Some (v_self'1892) ->
        v_self'1892
    | Option.None ->
        (Obj.magic
           (failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 351:7-351:12 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__isBrokenEdge =
  fun v_isWhitelist'1894 ->
    fun v_node'1895 ->
      Obj.magic
        v_or
        v_isWhitelist'1894
        (Obj.magic
           v_not
           (Obj.magic
              v__isTopAllowedP
              v_node'1895));;
let v__leftStuffP =
  fun v_p'1897 ->
    let v_X'1898 =
      v_p'1897
    in
    let v_defaultCase'2653 =
      fun nv_ ->
        CNone'1691
    in
    match
      Obj.magic
        v_X'1898
    with
    | CInfixP'1833 v_x'2654 ->
        (match
           Obj.magic
             (let v__target'2655 =
                Obj.magic
                  Obj.magic
                  v_X'1898
              in
              let
                CRec'2461 ({linput = v_input'2656})
              =
                Obj.magic
                  Obj.magic
                  v__target'2655
              in
              match
                Obj.magic
                  Obj.magic
                  v_input'2656
              with
              | CInfixI'1827 v__n'2657 ->
                  (let
                     CRec'2476 ({lleftAllow = v_leftAllow'2658})
                   =
                     Obj.magic
                       Obj.magic
                       v_input'2656
                   in
                   Option.Some (v_leftAllow'2658, v__target'2655))
              | _ ->
                  (Obj.magic
                     Obj.magic
                     (Option.None)))
         with
         | Option.Some (v_allows'1899, v_r'1900) ->
             (CSome'1690 (Obj.repr
                 (CRec'2499 { l0 =
                      (Obj.repr
                        (let
                           CRec'2461 ({lleftChildAlts = v_X'1901})
                         =
                           Obj.magic
                             v_r'1900
                         in
                         Obj.magic
                           v_X'1901));
                    l1 =
                      (Obj.repr
                        v_allows'1899) })))
         | Option.None ->
             (Obj.magic
                (Obj.magic
                   v_defaultCase'2653
                   ())))
    | CPostfixP'1835 v_x'2659 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2660 =
                   Obj.magic
                     Obj.magic
                     v_X'1898
                 in
                 let
                   CRec'2482 ({linput = v_input'2661})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2660
                 in
                 match
                   Obj.magic
                     Obj.magic
                     v_input'2661
                 with
                 | CPostfixI'1829 v__n'2662 ->
                     (let
                        CRec'2477 ({lleftAllow = v_leftAllow'2663})
                      =
                        Obj.magic
                          Obj.magic
                          v_input'2661
                      in
                      Option.Some (v_leftAllow'2663, v__target'2660))
                 | _ ->
                     (Obj.magic
                        Obj.magic
                        (Option.None)))
            with
            | Option.Some (v_allows'1902, v_r'1903) ->
                (CSome'1690 (Obj.repr
                    (CRec'2499 { l0 =
                         (Obj.repr
                           (let
                              CRec'2482 ({lleftChildAlts = v_X'1904})
                            =
                              Obj.magic
                                v_r'1903
                            in
                            Obj.magic
                              v_X'1904));
                       l1 =
                         (Obj.repr
                           v_allows'1902) })))
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2653
                      ()))))
    | _ ->
        (Obj.magic
           (v_defaultCase'2653
              ()));;
let v__rightStuffP =
  fun v_p'1906 ->
    let v_X'1907 =
      v_p'1906
    in
    let v_defaultCase'2664 =
      fun nv_ ->
        CNone'1691
    in
    match
      Obj.magic
        v_X'1907
    with
    | CInfixP'1833 v_x'2665 ->
        (match
           Obj.magic
             (let v__target'2666 =
                Obj.magic
                  Obj.magic
                  v_X'1907
              in
              let
                CRec'2461 ({linput = v_input'2667})
              =
                Obj.magic
                  Obj.magic
                  v__target'2666
              in
              match
                Obj.magic
                  Obj.magic
                  v_input'2667
              with
              | CInfixI'1827 v__n'2668 ->
                  (let
                     CRec'2476 ({lrightAllow = v_rightAllow'2669})
                   =
                     Obj.magic
                       Obj.magic
                       v_input'2667
                   in
                   Option.Some (v_rightAllow'2669, v__target'2666))
              | _ ->
                  (Obj.magic
                     Obj.magic
                     (Option.None)))
         with
         | Option.Some (v_allows'1908, v_r'1909) ->
             (CSome'1690 (Obj.repr
                 (CRec'2499 { l0 =
                      (Obj.repr
                        (let
                           CRec'2461 ({lrightChildAlts = v_X'1910})
                         =
                           Obj.magic
                             v_r'1909
                         in
                         Obj.magic
                           v_X'1910));
                    l1 =
                      (Obj.repr
                        v_allows'1908) })))
         | Option.None ->
             (Obj.magic
                (Obj.magic
                   v_defaultCase'2664
                   ())))
    | CPrefixP'1834 v_x'2670 ->
        (Obj.magic
           (match
              Obj.magic
                (let v__target'2671 =
                   Obj.magic
                     Obj.magic
                     v_X'1907
                 in
                 let
                   CRec'2462 ({linput = v_input'2672})
                 =
                   Obj.magic
                     Obj.magic
                     v__target'2671
                 in
                 match
                   Obj.magic
                     Obj.magic
                     v_input'2672
                 with
                 | CPrefixI'1828 v__n'2673 ->
                     (let
                        CRec'2475 ({lrightAllow = v_rightAllow'2674})
                      =
                        Obj.magic
                          Obj.magic
                          v_input'2672
                      in
                      Option.Some (v_rightAllow'2674, v__target'2671))
                 | _ ->
                     (Obj.magic
                        Obj.magic
                        (Option.None)))
            with
            | Option.Some (v_allows'1911, v_r'1912) ->
                (CSome'1690 (Obj.repr
                    (CRec'2499 { l0 =
                         (Obj.repr
                           (let
                              CRec'2462 ({lrightChildAlts = v_X'1913})
                            =
                              Obj.magic
                                v_r'1912
                            in
                            Obj.magic
                              v_X'1913));
                       l1 =
                         (Obj.repr
                           v_allows'1911) })))
            | Option.None ->
                (Obj.magic
                   (Obj.magic
                      v_defaultCase'2664
                      ()))))
    | _ ->
        (Obj.magic
           (v_defaultCase'2664
              ()));;
let v__brokenIdxesP =
  let rec v_work'1915 =
      fun v_isWhitelist'1916 ->
        fun v_p'1917 ->
          if
            Obj.magic
              (Obj.magic
                 v__isBrokenEdge
                 v_isWhitelist'1916
                 v_p'1917)
          then
            let v_l'1920 =
              match
                Obj.magic
                  (let v__target'2675 =
                     Obj.magic
                       v__leftStuffP
                       v_p'1917
                   in
                   match
                     Obj.magic
                       Obj.magic
                       v__target'2675
                   with
                   | CSome'1690 v__n'2676 ->
                       (let
                          CRec'2499 ({l0 = v_0'2677;l1 = v_1'2678})
                        =
                          Obj.magic
                            Obj.magic
                            v__n'2676
                        in
                        Option.Some (v_0'2677, v_1'2678))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None)))
              with
              | Option.Some (v_children'1918, v_allows'1919) ->
                  (Obj.magic
                     v_join
                     (Obj.magic
                        Boot.Intrinsics.Mseq.map
                        (Obj.magic
                           v_work'1915
                           (Obj.magic
                              v__isWhitelist
                              v_allows'1919))
                        v_children'1918))
              | Option.None ->
                  (Obj.magic
                     (Obj.magic
                        Boot.Intrinsics.Mseq.Helpers.of_array
                        [|  |]))
            in
            let v_r'1923 =
              match
                Obj.magic
                  (let v__target'2679 =
                     Obj.magic
                       v__rightStuffP
                       v_p'1917
                   in
                   match
                     Obj.magic
                       Obj.magic
                       v__target'2679
                   with
                   | CSome'1690 v__n'2680 ->
                       (let
                          CRec'2499 ({l0 = v_0'2681;l1 = v_1'2682})
                        =
                          Obj.magic
                            Obj.magic
                            v__n'2680
                        in
                        Option.Some (v_0'2681, v_1'2682))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None)))
              with
              | Option.Some (v_children'1921, v_allows'1922) ->
                  (Obj.magic
                     v_join
                     (Obj.magic
                        Boot.Intrinsics.Mseq.map
                        (Obj.magic
                           v_work'1915
                           (Obj.magic
                              v__isWhitelist
                              v_allows'1922))
                        v_children'1921))
              | Option.None ->
                  (Obj.magic
                     (Obj.magic
                        Boot.Intrinsics.Mseq.Helpers.of_array
                        [|  |]))
            in
            Obj.magic
              v_join
              (Obj.magic
                 Boot.Intrinsics.Mseq.Helpers.of_array
                 [| (Obj.magic
                     v_l'1920);
                   (Obj.magic
                     (Obj.magic
                        Boot.Intrinsics.Mseq.Helpers.of_array
                        [| (Obj.magic
                            (Obj.magic
                               v__opIdxP
                               v_p'1917)) |]));
                   (Obj.magic
                     v_r'1923) |])
          else
            Obj.magic
              (Obj.magic
                 Boot.Intrinsics.Mseq.Helpers.of_array
                 [|  |])
  in Obj.magic
    v_work'1915
    true;;
let v__brokenChildrenP =
  let rec v_work'1925 =
      fun v_isWhitelist'1926 ->
        fun v_p'1927 ->
          if
            Obj.magic
              (Obj.magic
                 v__isBrokenEdge
                 v_isWhitelist'1926
                 v_p'1927)
          then
            let v_l'1930 =
              match
                Obj.magic
                  (let v__target'2683 =
                     Obj.magic
                       v__leftStuffP
                       v_p'1927
                   in
                   match
                     Obj.magic
                       Obj.magic
                       v__target'2683
                   with
                   | CSome'1690 v__n'2684 ->
                       (let
                          CRec'2499 ({l0 = v_0'2685;l1 = v_1'2686})
                        =
                          Obj.magic
                            Obj.magic
                            v__n'2684
                        in
                        Option.Some (v_0'2685, v_1'2686))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None)))
              with
              | Option.Some (v_children'1928, v_allows'1929) ->
                  (Obj.magic
                     v_join
                     (Obj.magic
                        Boot.Intrinsics.Mseq.map
                        (Obj.magic
                           v_work'1925
                           (Obj.magic
                              v__isWhitelist
                              v_allows'1929))
                        v_children'1928))
              | Option.None ->
                  (Obj.magic
                     (Obj.magic
                        Boot.Intrinsics.Mseq.Helpers.of_array
                        [|  |]))
            in
            let v_r'1933 =
              match
                Obj.magic
                  (let v__target'2687 =
                     Obj.magic
                       v__rightStuffP
                       v_p'1927
                   in
                   match
                     Obj.magic
                       Obj.magic
                       v__target'2687
                   with
                   | CSome'1690 v__n'2688 ->
                       (let
                          CRec'2499 ({l0 = v_0'2689;l1 = v_1'2690})
                        =
                          Obj.magic
                            Obj.magic
                            v__n'2688
                        in
                        Option.Some (v_0'2689, v_1'2690))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None)))
              with
              | Option.Some (v_children'1931, v_allows'1932) ->
                  (Obj.magic
                     v_join
                     (Obj.magic
                        Boot.Intrinsics.Mseq.map
                        (Obj.magic
                           v_work'1925
                           (Obj.magic
                              v__isWhitelist
                              v_allows'1932))
                        v_children'1931))
              | Option.None ->
                  (Obj.magic
                     (Obj.magic
                        Boot.Intrinsics.Mseq.Helpers.of_array
                        [|  |]))
            in
            Obj.magic
              Boot.Intrinsics.Mseq.concat
              v_l'1930
              v_r'1933
          else
            Obj.magic
              (Obj.magic
                 Boot.Intrinsics.Mseq.Helpers.of_array
                 [| (Obj.magic
                     v_p'1927) |])
  in Obj.magic
    v_work'1925
    true;;
let v_breakableInAllowSet =
  fun v_id'1935 ->
    fun v_set'1936 ->
      let v_defaultCase'2691 =
        fun nv_ ->
          failwith
            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 412:4-412:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
      in
      match
        Obj.magic
          v_set'1936
      with
      | CAllowSet'1808 v_x'2692 ->
          (let v_s'1937 =
             Obj.magic
               Obj.magic
               v_x'2692
           in
           Obj.magic
             Boot.Intrinsics.Mmap.mem
             v_id'1935
             v_s'1937)
      | CDisallowSet'1809 v_x'2693 ->
          (Obj.magic
             (let v_s'1938 =
                Obj.magic
                  Obj.magic
                  v_x'2693
              in
              Obj.magic
                v_not
                (Obj.magic
                   Boot.Intrinsics.Mmap.mem
                   v_id'1935
                   v_s'1938)))
      | _ ->
          (Obj.magic
             (v_defaultCase'2691
                ()));;
let v_breakableInsertAllowSet =
  fun v_id'1940 ->
    fun v_set'1941 ->
      let v_defaultCase'2694 =
        fun nv_ ->
          failwith
            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 421:4-421:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
      in
      match
        Obj.magic
          v_set'1941
      with
      | CAllowSet'1808 v_x'2695 ->
          (let v_s'1942 =
             Obj.magic
               Obj.magic
               v_x'2695
           in
           CAllowSet'1808 (Obj.repr
              (Obj.magic
                 Boot.Intrinsics.Mmap.insert
                 v_id'1940
                 ()
                 v_s'1942)))
      | CDisallowSet'1809 v_x'2696 ->
          (Obj.magic
             (let v_s'1943 =
                Obj.magic
                  Obj.magic
                  v_x'2696
              in
              CDisallowSet'1809 (Obj.repr
                 (Obj.magic
                    Boot.Intrinsics.Mmap.remove
                    v_id'1940
                    v_s'1943))))
      | _ ->
          (Obj.magic
             (v_defaultCase'2694
                ()));;
let v_breakableRemoveAllowSet =
  fun v_id'1945 ->
    fun v_set'1946 ->
      let v_defaultCase'2697 =
        fun nv_ ->
          failwith
            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 430:4-430:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
      in
      match
        Obj.magic
          v_set'1946
      with
      | CAllowSet'1808 v_x'2698 ->
          (let v_s'1947 =
             Obj.magic
               Obj.magic
               v_x'2698
           in
           CAllowSet'1808 (Obj.repr
              (Obj.magic
                 Boot.Intrinsics.Mmap.remove
                 v_id'1945
                 v_s'1947)))
      | CDisallowSet'1809 v_x'2699 ->
          (Obj.magic
             (let v_s'1948 =
                Obj.magic
                  Obj.magic
                  v_x'2699
              in
              CDisallowSet'1809 (Obj.repr
                 (Obj.magic
                    Boot.Intrinsics.Mmap.insert
                    v_id'1945
                    ()
                    v_s'1948))))
      | _ ->
          (Obj.magic
             (v_defaultCase'2697
                ()));;
let v_breakableMapAllowSet =
  fun v_f'1950 ->
    fun v_newCmp'1951 ->
      fun v_s'1952 ->
        let v_convert'1956 =
          fun v_s'1953 ->
            Obj.magic
              v_mapFromSeq
              v_newCmp'1951
              (Obj.magic
                 Boot.Intrinsics.Mseq.map
                 (fun v_x'1954 ->
                    CRec'2499 { l0 =
                        (Obj.repr
                          (Obj.magic
                             v_f'1950
                             (let
                                CRec'2499 ({l0 = v_X'1955})
                              =
                                Obj.magic
                                  v_x'1954
                              in
                              Obj.magic
                                v_X'1955)));
                      l1 =
                        (Obj.repr
                          ()) })
                 (Obj.magic
                    Boot.Intrinsics.Mmap.bindings
                    v_s'1953))
        in
        let v_defaultCase'2700 =
          fun nv_ ->
            failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 441:4-441:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
        in
        match
          Obj.magic
            v_s'1952
        with
        | CAllowSet'1808 v_x'2701 ->
            (let v_s'1957 =
               Obj.magic
                 Obj.magic
                 v_x'2701
             in
             CAllowSet'1808 (Obj.repr
                (Obj.magic
                   v_convert'1956
                   v_s'1957)))
        | CDisallowSet'1809 v_x'2702 ->
            (Obj.magic
               (let v_s'1958 =
                  Obj.magic
                    Obj.magic
                    v_x'2702
                in
                CDisallowSet'1809 (Obj.repr
                   (Obj.magic
                      v_convert'1956
                      v_s'1958))))
        | _ ->
            (Obj.magic
               (v_defaultCase'2700
                  ()));;
let v_breakableGenGrammar =
  fun v_cmp'1960 ->
    fun v_grammar'1961 ->
      let v_nOpId'1962 =
        Obj.magic
          ref
          v__firstOpId
      in
      let v_newOpId'1966 =
        fun v_'1963 ->
          let v_res'1964 =
            Obj.magic
              (!)
              v_nOpId'1962
          in
          let v_'1965 =
            Obj.magic
              (:=)
              v_nOpId'1962
              (Obj.magic
                 v__nextOpId
                 v_res'1964)
          in
          v_res'1964
      in
      let v_label'1972 =
        fun v_prod'1967 ->
          let v_defaultCase'2703 =
            fun nv_ ->
              failwith
                "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 462:8-462:13 ERROR: Reached a never term, which should be impossible in a well-typed program."
          in
          match
            Obj.magic
              v_prod'1967
          with
          | CBreakableAtom'1813 v_x'2704 ->
              (match
                 Obj.magic
                   (let v__target'2705 =
                      Obj.magic
                        Obj.magic
                        v_prod'1967
                    in
                    let
                      CRec'2448 ({llabel = v_label'2706})
                    =
                      Obj.magic
                        Obj.magic
                        v__target'2705
                    in
                    Option.Some (v_label'2706))
               with
               | Option.Some (v_label'1968) ->
                   v_label'1968
               | Option.None ->
                   (Obj.magic
                      (Obj.magic
                         v_defaultCase'2703
                         ())))
          | CBreakableInfix'1814 v_x'2707 ->
              (Obj.magic
                 (match
                    Obj.magic
                      (let v__target'2708 =
                         Obj.magic
                           Obj.magic
                           v_prod'1967
                       in
                       let
                         CRec'2449 ({llabel = v_label'2709})
                       =
                         Obj.magic
                           Obj.magic
                           v__target'2708
                       in
                       Option.Some (v_label'2709))
                  with
                  | Option.Some (v_label'1970) ->
                      v_label'1970
                  | Option.None ->
                      (Obj.magic
                         (Obj.magic
                            v_defaultCase'2703
                            ()))))
          | CBreakablePrefix'1815 v_x'2710 ->
              (Obj.magic
                 (match
                    Obj.magic
                      (let v__target'2711 =
                         Obj.magic
                           Obj.magic
                           v_prod'1967
                       in
                       let
                         CRec'2450 ({llabel = v_label'2712})
                       =
                         Obj.magic
                           Obj.magic
                           v__target'2711
                       in
                       Option.Some (v_label'2712))
                  with
                  | Option.Some (v_label'1969) ->
                      v_label'1969
                  | Option.None ->
                      (Obj.magic
                         (Obj.magic
                            v_defaultCase'2703
                            ()))))
          | CBreakablePostfix'1816 v_x'2713 ->
              (Obj.magic
                 (match
                    Obj.magic
                      (let v__target'2714 =
                         Obj.magic
                           Obj.magic
                           v_prod'1967
                       in
                       let
                         CRec'2451 ({llabel = v_label'2715})
                       =
                         Obj.magic
                           Obj.magic
                           v__target'2714
                       in
                       Option.Some (v_label'2715))
                  with
                  | Option.Some (v_label'1971) ->
                      v_label'1971
                  | Option.None ->
                      (Obj.magic
                         (Obj.magic
                            v_defaultCase'2703
                            ()))))
          | _ ->
              (Obj.magic
                 (v_defaultCase'2703
                    ()))
      in
      let v_prodLabelToOpId'1975 =
        Obj.magic
          v_mapFromSeq
          v_cmp'1960
          (Obj.magic
             Boot.Intrinsics.Mseq.map
             (fun v_prod'1973 ->
                CRec'2499 { l0 =
                    (Obj.repr
                      (Obj.magic
                         v_label'1972
                         v_prod'1973));
                  l1 =
                    (Obj.repr
                      (Obj.magic
                         v_newOpId'1966
                         ())) })
             (let
                CRec'2498 ({lproductions = v_X'1974})
              =
                Obj.magic
                  v_grammar'1961
              in
              Obj.magic
                v_X'1974))
      in
      let v_toOpId'1977 =
        fun v_label'1976 ->
          Obj.magic
            Boot.Intrinsics.Mmap.find
            v_label'1976
            v_prodLabelToOpId'1975
      in
      let v_groupingByRightOp'1988 =
        Obj.magic
          Boot.Intrinsics.Mseq.Helpers.fold_left
          (fun v_acc'1978 ->
             fun v_grouping'1979 ->
               match
                 Obj.magic
                   (let v__target'2716 =
                      v_grouping'1979
                    in
                    let
                      CRec'2499 ({l0 = v_0'2717;l1 = v_1'2718})
                    =
                      Obj.magic
                        Obj.magic
                        v__target'2716
                    in
                    let
                      CRec'2499 ({l0 = v_0'2719;l1 = v_1'2720})
                    =
                      Obj.magic
                        Obj.magic
                        v_0'2717
                    in
                    Option.Some (v_0'2719, v_1'2720, v_1'2718))
               with
               | Option.Some (v_lplab'1980, v_rplab'1981, v_grouping'1982) ->
                   (let v_lid'1983 =
                      Obj.magic
                        v_toOpId'1977
                        v_lplab'1980
                    in
                    let v_rid'1984 =
                      Obj.magic
                        v_toOpId'1977
                        v_rplab'1981
                    in
                    let v_prev'1986 =
                      match
                        Obj.magic
                          (let v__target'2721 =
                             Obj.magic
                               v_mapLookup
                               v_rid'1984
                               v_acc'1978
                           in
                           match
                             Obj.magic
                               Obj.magic
                               v__target'2721
                           with
                           | CSome'1690 v__n'2722 ->
                               (Option.Some (v__n'2722))
                           | _ ->
                               (Obj.magic
                                  Obj.magic
                                  (Option.None)))
                      with
                      | Option.Some (v_prev'1985) ->
                          v_prev'1985
                      | Option.None ->
                          (Obj.magic
                             (Obj.magic
                                Boot.Intrinsics.Mmap.empty
                                v__cmpOpId))
                    in
                    Obj.magic
                      Boot.Intrinsics.Mmap.insert
                      v_rid'1984
                      (Obj.magic
                         Boot.Intrinsics.Mmap.insert
                         v_lid'1983
                         v_grouping'1982
                         v_prev'1986)
                      v_acc'1978)
               | Option.None ->
                   (Obj.magic
                      (failwith
                         "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 484:15-484:20 ERROR: Reached a never term, which should be impossible in a well-typed program.")))
          (Obj.magic
             Boot.Intrinsics.Mmap.empty
             v__cmpOpId)
          (let
             CRec'2498 ({lprecedences = v_X'1987})
           =
             Obj.magic
               v_grammar'1961
           in
           Obj.magic
             v_X'1987)
      in
      let v_getGroupingByRight'1991 =
        fun v_opid'1989 ->
          match
            Obj.magic
              (let v__target'2723 =
                 Obj.magic
                   v_mapLookup
                   v_opid'1989
                   v_groupingByRightOp'1988
               in
               match
                 Obj.magic
                   Obj.magic
                   v__target'2723
               with
               | CSome'1690 v__n'2724 ->
                   (Option.Some (v__n'2724))
               | _ ->
                   (Obj.magic
                      Obj.magic
                      (Option.None)))
          with
          | Option.Some (v_res'1990) ->
              v_res'1990
          | Option.None ->
              (Obj.magic
                 (Obj.magic
                    Boot.Intrinsics.Mmap.empty
                    v__cmpOpId))
      in
      let v_atoms'1992 =
        Obj.magic
          ref
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |])
      in
      let v_prefixes'1993 =
        Obj.magic
          ref
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |])
      in
      let v_infixes'1994 =
        Obj.magic
          ref
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |])
      in
      let v_postfixes'1995 =
        Obj.magic
          ref
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [|  |])
      in
      let v_updateRef'1998 =
        fun v_ref'1996 ->
          fun v_f'1997 ->
            Obj.magic
              (:=)
              v_ref'1996
              (Obj.magic
                 v_f'1997
                 (Obj.magic
                    (!)
                    v_ref'1996))
      in
      let v_isTopAllowed'2002 =
        let v_topAllowed'2000 =
          Obj.magic
            v_breakableMapAllowSet
            v_toOpId'1977
            v__cmpOpId
            (let
               CRec'2498 ({ltopAllowed = v_X'1999})
             =
               Obj.magic
                 v_grammar'1961
             in
             Obj.magic
               v_X'1999)
        in
        fun v_id'2001 ->
          Obj.magic
            v_breakableInAllowSet
            v_id'2001
            v_topAllowed'2000
      in
      let v_'2021 =
        Obj.magic
          v_for_
          (let
             CRec'2498 ({lproductions = v_X'2003})
           =
             Obj.magic
               v_grammar'1961
           in
           Obj.magic
             v_X'2003)
          (fun v_prod'2004 ->
             let v_label'2005 =
               Obj.magic
                 v_label'1972
                 v_prod'2004
             in
             let v_id'2006 =
               Obj.magic
                 v_toOpId'1977
                 v_label'2005
             in
             let v_defaultCase'2725 =
               fun nv_ ->
                 failwith
                   "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 522:13-522:18 ERROR: Reached a never term, which should be impossible in a well-typed program."
             in
             match
               Obj.magic
                 v_prod'2004
             with
             | CBreakableAtom'1813 v_x'2726 ->
                 (match
                    Obj.magic
                      (let v__target'2727 =
                         Obj.magic
                           Obj.magic
                           v_prod'2004
                       in
                       let
                         CRec'2448 ({lconstruct = v_construct'2728})
                       =
                         Obj.magic
                           Obj.magic
                           v__target'2727
                       in
                       Option.Some (v_construct'2728))
                  with
                  | Option.Some (v_construct'2007) ->
                      (Obj.magic
                         v_updateRef'1998
                         v_atoms'1992
                         (Obj.magic
                            Boot.Intrinsics.Mseq.cons
                            (CRec'2499 { l0 =
                                 (Obj.repr
                                   v_label'2005);
                               l1 =
                                 (Obj.repr
                                   (CAtomI'1826 { lconstruct =
                                        (Obj.repr
                                          v_construct'2007);
                                      lid =
                                        (Obj.repr
                                          v_id'2006);
                                      lallowedTop =
                                        (Obj.repr
                                          (Obj.magic
                                             v_isTopAllowed'2002
                                             v_id'2006)) })) })))
                  | Option.None ->
                      (Obj.magic
                         (Obj.magic
                            v_defaultCase'2725
                            ())))
             | CBreakableInfix'1814 v_x'2729 ->
                 (Obj.magic
                    (match
                       Obj.magic
                         (let v__target'2730 =
                            Obj.magic
                              Obj.magic
                              v_prod'2004
                          in
                          let
                            CRec'2449 ({lconstruct = v_construct'2731;lleftAllow = v_leftAllow'2732;lrightAllow = v_rightAllow'2733})
                          =
                            Obj.magic
                              Obj.magic
                              v__target'2730
                          in
                          Option.Some (v_construct'2731, v_leftAllow'2732, v_rightAllow'2733))
                     with
                     | Option.Some (v_c'2011, v_l'2012, v_r'2013) ->
                         (let v_l'2014 =
                            Obj.magic
                              v_breakableMapAllowSet
                              v_toOpId'1977
                              v__cmpOpId
                              v_l'2012
                          in
                          let v_r'2015 =
                            Obj.magic
                              v_breakableMapAllowSet
                              v_toOpId'1977
                              v__cmpOpId
                              v_r'2013
                          in
                          let v_p'2016 =
                            Obj.magic
                              v_getGroupingByRight'1991
                              v_id'2006
                          in
                          Obj.magic
                            v_updateRef'1998
                            v_infixes'1994
                            (Obj.magic
                               Boot.Intrinsics.Mseq.cons
                               (CRec'2499 { l0 =
                                    (Obj.repr
                                      v_label'2005);
                                  l1 =
                                    (Obj.repr
                                      (CInfixI'1827 { lconstruct =
                                           (Obj.repr
                                             v_c'2011);
                                         lleftAllow =
                                           (Obj.repr
                                             v_l'2014);
                                         lrightAllow =
                                           (Obj.repr
                                             v_r'2015);
                                         lid =
                                           (Obj.repr
                                             v_id'2006);
                                         lallowedTop =
                                           (Obj.repr
                                             (Obj.magic
                                                v_isTopAllowed'2002
                                                v_id'2006));
                                         lprecWhenThisIsRight =
                                           (Obj.repr
                                             v_p'2016) })) })))
                     | Option.None ->
                         (Obj.magic
                            (Obj.magic
                               v_defaultCase'2725
                               ()))))
             | CBreakablePrefix'1815 v_x'2734 ->
                 (Obj.magic
                    (match
                       Obj.magic
                         (let v__target'2735 =
                            Obj.magic
                              Obj.magic
                              v_prod'2004
                          in
                          let
                            CRec'2450 ({lconstruct = v_construct'2736;lrightAllow = v_rightAllow'2737})
                          =
                            Obj.magic
                              Obj.magic
                              v__target'2735
                          in
                          Option.Some (v_construct'2736, v_rightAllow'2737))
                     with
                     | Option.Some (v_c'2008, v_r'2009) ->
                         (let v_r'2010 =
                            Obj.magic
                              v_breakableMapAllowSet
                              v_toOpId'1977
                              v__cmpOpId
                              v_r'2009
                          in
                          Obj.magic
                            v_updateRef'1998
                            v_prefixes'1993
                            (Obj.magic
                               Boot.Intrinsics.Mseq.cons
                               (CRec'2499 { l0 =
                                    (Obj.repr
                                      v_label'2005);
                                  l1 =
                                    (Obj.repr
                                      (CPrefixI'1828 { lconstruct =
                                           (Obj.repr
                                             v_c'2008);
                                         lrightAllow =
                                           (Obj.repr
                                             v_r'2010);
                                         lid =
                                           (Obj.repr
                                             v_id'2006);
                                         lallowedTop =
                                           (Obj.repr
                                             (Obj.magic
                                                v_isTopAllowed'2002
                                                v_id'2006)) })) })))
                     | Option.None ->
                         (Obj.magic
                            (Obj.magic
                               v_defaultCase'2725
                               ()))))
             | CBreakablePostfix'1816 v_x'2738 ->
                 (Obj.magic
                    (match
                       Obj.magic
                         (let v__target'2739 =
                            Obj.magic
                              Obj.magic
                              v_prod'2004
                          in
                          let
                            CRec'2451 ({lconstruct = v_construct'2740;lleftAllow = v_leftAllow'2741})
                          =
                            Obj.magic
                              Obj.magic
                              v__target'2739
                          in
                          Option.Some (v_construct'2740, v_leftAllow'2741))
                     with
                     | Option.Some (v_c'2017, v_l'2018) ->
                         (let v_l'2019 =
                            Obj.magic
                              v_breakableMapAllowSet
                              v_toOpId'1977
                              v__cmpOpId
                              v_l'2018
                          in
                          let v_p'2020 =
                            Obj.magic
                              v_getGroupingByRight'1991
                              v_id'2006
                          in
                          Obj.magic
                            v_updateRef'1998
                            v_postfixes'1995
                            (Obj.magic
                               Boot.Intrinsics.Mseq.cons
                               (CRec'2499 { l0 =
                                    (Obj.repr
                                      v_label'2005);
                                  l1 =
                                    (Obj.repr
                                      (CPostfixI'1829 { lconstruct =
                                           (Obj.repr
                                             v_c'2017);
                                         lleftAllow =
                                           (Obj.repr
                                             v_l'2019);
                                         lid =
                                           (Obj.repr
                                             v_id'2006);
                                         lallowedTop =
                                           (Obj.repr
                                             (Obj.magic
                                                v_isTopAllowed'2002
                                                v_id'2006));
                                         lprecWhenThisIsRight =
                                           (Obj.repr
                                             v_p'2020) })) })))
                     | Option.None ->
                         (Obj.magic
                            (Obj.magic
                               v_defaultCase'2725
                               ()))))
             | _ ->
                 (Obj.magic
                    (v_defaultCase'2725
                       ())))
      in
      CRec'2459 { latoms =
          (Obj.repr
            (Obj.magic
               v_mapFromSeq
               v_cmp'1960
               (Obj.magic
                  (!)
                  v_atoms'1992)));
        lprefixes =
          (Obj.repr
            (Obj.magic
               v_mapFromSeq
               v_cmp'1960
               (Obj.magic
                  (!)
                  v_prefixes'1993)));
        linfixes =
          (Obj.repr
            (Obj.magic
               v_mapFromSeq
               v_cmp'1960
               (Obj.magic
                  (!)
                  v_infixes'1994)));
        lpostfixes =
          (Obj.repr
            (Obj.magic
               v_mapFromSeq
               v_cmp'1960
               (Obj.magic
                  (!)
                  v_postfixes'1995))) };;
let v_breakableInitState =
  fun v_'2023 ->
    let v_timestep'2024 =
      Obj.magic
        ref
        v__firstTimeStep
    in
    let v_nextIdx'2025 =
      Obj.magic
        ref
        0
    in
    let v_addedLeft'2026 =
      Obj.magic
        ref
        (CRec'2499 { l0 =
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
    let v_addedRight'2027 =
      Obj.magic
        ref
        (CRec'2499 { l0 =
             (Obj.repr
               v__firstTimeStep);
           l1 =
             (Obj.repr
               (Obj.magic
                  Boot.Intrinsics.Mseq.Helpers.of_array
                  [|  |])) })
    in
    CRec'2469 { ltimestep =
        (Obj.repr
          v_timestep'2024);
      lnextIdx =
        (Obj.repr
          v_nextIdx'2025);
      lfrontier =
        (Obj.repr
          (Obj.magic
             Boot.Intrinsics.Mseq.Helpers.of_array
             [| (Obj.magic
                 (CTentativeRoot'1843 { laddedNodesLeftChildren =
                      (Obj.repr
                        v_addedLeft'2026);
                    laddedNodesRightChildren =
                      (Obj.repr
                        v_addedRight'2027) })) |])) };;
let rec v__maxDistanceFromRoot =
    fun v_n'2030 ->
      let v_defaultCase'2742 =
        fun nv_ ->
          let v_'2034 =
            Obj.magic
              v_dprintLn
              v_n'2030
          in
          failwith
            "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 550:4-550:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
      in
      match
        Obj.magic
          v_n'2030
      with
      | CTentativeLeaf'1841 v_x'2743 ->
          (match
             Obj.magic
               (let v__target'2744 =
                  Obj.magic
                    Obj.magic
                    v_n'2030
                in
                let
                  CRec'2491 ({lparents = v_parents'2745})
                =
                  Obj.magic
                    Obj.magic
                    v__target'2744
                in
                Option.Some (v_parents'2745))
           with
           | Option.Some (v_parents'2032) ->
               (Obj.magic
                  v_maxOrElse
                  (fun v_'2033 ->
                     0)
                  Int.sub
                  (Obj.magic
                     Boot.Intrinsics.Mseq.map
                     v__maxDistanceFromRoot
                     v_parents'2032))
           | Option.None ->
               (Obj.magic
                  (Obj.magic
                     v_defaultCase'2742
                     ())))
      | CTentativeMid'1842 v_x'2746 ->
          (Obj.magic
             (match
                Obj.magic
                  (let v__target'2747 =
                     Obj.magic
                       Obj.magic
                       v_n'2030
                   in
                   let
                     CRec'2489 ({lmaxDistanceFromRoot = v_maxDistanceFromRoot'2748})
                   =
                     Obj.magic
                       Obj.magic
                       v__target'2747
                   in
                   Option.Some (v_maxDistanceFromRoot'2748))
              with
              | Option.Some (v_r'2031) ->
                  v_r'2031
              | Option.None ->
                  (Obj.magic
                     (Obj.magic
                        v_defaultCase'2742
                        ()))))
      | CTentativeRoot'1843 v_x'2749 ->
          (Obj.magic
             0)
      | _ ->
          (Obj.magic
             (v_defaultCase'2742
                ()));;
let v__shallowAllowedLeft =
  fun v_parent'2035 ->
    fun v_child'2036 ->
      match
        Obj.magic
          (let v__target'2750 =
             v_child'2036
           in
           match
             Obj.magic
               Obj.magic
               v__target'2750
           with
           | CTentativeLeaf'1841 v__n'2751 ->
               (let
                  CRec'2491 ({lnode = v_node'2752})
                =
                  Obj.magic
                    Obj.magic
                    v__target'2750
                in
                Option.Some (v_node'2752))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_node'2037) ->
          (match
             Obj.magic
               (let v__target'2753 =
                  v_parent'2035
                in
                match
                  match
                    match
                      Obj.magic
                        Obj.magic
                        v__target'2753
                    with
                    | CInfixI'1827 v__n'2754 ->
                        (let
                           CRec'2476 ({lleftAllow = v_leftAllow'2755})
                         =
                           Obj.magic
                             Obj.magic
                             v__target'2753
                         in
                         Option.Some (v_leftAllow'2755))
                    | _ ->
                        (Obj.magic
                           Obj.magic
                           (Option.None))
                  with
                  | Option.Some v__x'2758 ->
                      (Option.Some v__x'2758)
                  | Option.None ->
                      (Obj.magic
                         Obj.magic
                         (match
                            Obj.magic
                              Obj.magic
                              v__target'2753
                          with
                          | CPostfixI'1829 v__n'2756 ->
                              (let
                                 CRec'2477 ({lleftAllow = v_leftAllow'2757})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2753
                               in
                               Option.Some (v_leftAllow'2757))
                          | _ ->
                              (Obj.magic
                                 Obj.magic
                                 (Option.None))))
                with
                | Option.Some (v_s'2038) ->
                    (Option.Some (v_s'2038))
                | Option.None ->
                    (Obj.magic
                       Obj.magic
                       (Option.None)))
           with
           | Option.Some (v_s'2038) ->
               (if
                  Obj.magic
                    (Obj.magic
                       v_breakableInAllowSet
                       (Obj.magic
                          v__opIdP
                          v_node'2037)
                       v_s'2038)
                then
                  CSome'1690 (Obj.repr
                     v_node'2037)
                else
                  Obj.magic
                    CNone'1691)
           | Option.None ->
               (Obj.magic
                  (failwith
                     "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 561:11-561:16 ERROR: Reached a never term, which should be impossible in a well-typed program.")))
      | Option.None ->
          (Obj.magic
             (failwith
                "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 562:9-562:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__shallowAllowedRight =
  fun v_parent'2040 ->
    fun v_child'2041 ->
      match
        Obj.magic
          (let v__target'2759 =
             v_child'2041
           in
           match
             Obj.magic
               Obj.magic
               v__target'2759
           with
           | CTentativeLeaf'1841 v__n'2760 ->
               (let
                  CRec'2491 ({lnode = v_node'2761})
                =
                  Obj.magic
                    Obj.magic
                    v__target'2759
                in
                Option.Some (v_node'2761))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_node'2042) ->
          (let v_X'2043 =
             v_parent'2040
           in
           let v_defaultCase'2762 =
             fun nv_ ->
               failwith
                 "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 575:6-575:9 ERROR: Reached a never term, which should be impossible in a well-typed program."
           in
           match
             Obj.magic
               v_X'2043
           with
           | CTentativeMid'1842 v_x'2763 ->
               (match
                  Obj.magic
                    (let v__target'2764 =
                       Obj.magic
                         Obj.magic
                         v_X'2043
                     in
                     let
                       CRec'2489 ({ltentativeData = v_tentativeData'2765})
                     =
                       Obj.magic
                         Obj.magic
                         v__target'2764
                     in
                     match
                       match
                         match
                           Obj.magic
                             Obj.magic
                             v_tentativeData'2765
                         with
                         | CInfixT'1837 v__n'2766 ->
                             (let
                                CRec'2480 ({linput = v_input'2767})
                              =
                                Obj.magic
                                  Obj.magic
                                  v_tentativeData'2765
                              in
                              match
                                Obj.magic
                                  Obj.magic
                                  v_input'2767
                              with
                              | CInfixI'1827 v__n'2768 ->
                                  (let
                                     CRec'2476 ({lrightAllow = v_rightAllow'2769})
                                   =
                                     Obj.magic
                                       Obj.magic
                                       v_input'2767
                                   in
                                   Option.Some (v_rightAllow'2769))
                              | _ ->
                                  (Obj.magic
                                     Obj.magic
                                     (Option.None)))
                         | _ ->
                             (Obj.magic
                                Obj.magic
                                (Option.None))
                       with
                       | Option.Some v__x'2774 ->
                           (Option.Some v__x'2774)
                       | Option.None ->
                           (Obj.magic
                              Obj.magic
                              (match
                                 Obj.magic
                                   Obj.magic
                                   v_tentativeData'2765
                               with
                               | CPrefixT'1838 v__n'2770 ->
                                   (let
                                      CRec'2488 ({linput = v_input'2771})
                                    =
                                      Obj.magic
                                        Obj.magic
                                        v_tentativeData'2765
                                    in
                                    match
                                      Obj.magic
                                        Obj.magic
                                        v_input'2771
                                    with
                                    | CPrefixI'1828 v__n'2772 ->
                                        (let
                                           CRec'2475 ({lrightAllow = v_rightAllow'2773})
                                         =
                                           Obj.magic
                                             Obj.magic
                                             v_input'2771
                                         in
                                         Option.Some (v_rightAllow'2773))
                                    | _ ->
                                        (Obj.magic
                                           Obj.magic
                                           (Option.None)))
                               | _ ->
                                   (Obj.magic
                                      Obj.magic
                                      (Option.None))))
                     with
                     | Option.Some (v_s'2044) ->
                         (Option.Some (v_s'2044))
                     | Option.None ->
                         (Obj.magic
                            Obj.magic
                            (Option.None)))
                with
                | Option.Some (v_s'2044) ->
                    (if
                       Obj.magic
                         (Obj.magic
                            v_breakableInAllowSet
                            (Obj.magic
                               v__opIdP
                               v_node'2042)
                            v_s'2044)
                     then
                       CSome'1690 (Obj.repr
                          v_node'2042)
                     else
                       Obj.magic
                         CNone'1691)
                | Option.None ->
                    (Obj.magic
                       (Obj.magic
                          v_defaultCase'2762
                          ())))
           | CTentativeRoot'1843 v_x'2775 ->
               (Obj.magic
                  (if
                     Obj.magic
                       (Obj.magic
                          v__isTopAllowedP
                          v_node'2042)
                   then
                     CSome'1690 (Obj.repr
                        v_node'2042)
                   else
                     Obj.magic
                       CNone'1691))
           | _ ->
               (Obj.magic
                  (v_defaultCase'2762
                     ())))
      | Option.None ->
          (Obj.magic
             (failwith
                "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 576:9-576:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__addRightChildren =
  fun v_st'2046 ->
    fun v_parent'2047 ->
      fun v_children'2048 ->
        let v_defaultCase'2776 =
          fun nv_ ->
            failwith
              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 595:9-595:14 ERROR: Reached a never term, which should be impossible in a well-typed program."
        in
        match
          Obj.magic
            v_parent'2047
        with
        | CTentativeMid'1842 v_x'2777 ->
            (match
               Obj.magic
                 (let v__target'2778 =
                    Obj.magic
                      Obj.magic
                      v_parent'2047
                  in
                  let
                    CRec'2489 ({lparents = v_parents'2779;ltentativeData = v_tentativeData'2780})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2778
                  in
                  Option.Some (v_parents'2779, v_tentativeData'2780))
             with
             | Option.Some (v_parents'2049, v_data'2050) ->
                 (let v_id'2051 =
                    Obj.magic
                      v__uniqueID
                      ()
                  in
                  let v_node'2059 =
                    let v_defaultCase'2781 =
                      fun nv_ ->
                        failwith
                          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 591:13-591:18 ERROR: Reached a never term, which should be impossible in a well-typed program."
                    in
                    match
                      Obj.magic
                        v_data'2050
                    with
                    | CInfixT'1837 v_x'2782 ->
                        (match
                           Obj.magic
                             (let v__target'2783 =
                                Obj.magic
                                  Obj.magic
                                  v_data'2050
                              in
                              let
                                CRec'2480 ({lidx = v_idx'2784;linput = v_input'2785;lself = v_self'2786;lleftChildAlts = v_leftChildAlts'2787})
                              =
                                Obj.magic
                                  Obj.magic
                                  v__target'2783
                              in
                              Option.Some (v_idx'2784, v_input'2785, v_self'2786, v_leftChildAlts'2787))
                         with
                         | Option.Some (v_idx'2052, v_input'2053, v_self'2054, v_l'2055) ->
                             (CInfixP'1833 { lid =
                                  (Obj.repr
                                    v_id'2051);
                                lidx =
                                  (Obj.repr
                                    v_idx'2052);
                                linput =
                                  (Obj.repr
                                    v_input'2053);
                                lself =
                                  (Obj.repr
                                    v_self'2054);
                                lleftChildAlts =
                                  (Obj.repr
                                    v_l'2055);
                                lrightChildAlts =
                                  (Obj.repr
                                    v_children'2048) })
                         | Option.None ->
                             (Obj.magic
                                (Obj.magic
                                   v_defaultCase'2781
                                   ())))
                    | CPrefixT'1838 v_x'2788 ->
                        (Obj.magic
                           (match
                              Obj.magic
                                (let v__target'2789 =
                                   Obj.magic
                                     Obj.magic
                                     v_data'2050
                                 in
                                 let
                                   CRec'2488 ({lidx = v_idx'2790;linput = v_input'2791;lself = v_self'2792})
                                 =
                                   Obj.magic
                                     Obj.magic
                                     v__target'2789
                                 in
                                 Option.Some (v_idx'2790, v_input'2791, v_self'2792))
                            with
                            | Option.Some (v_idx'2056, v_input'2057, v_self'2058) ->
                                (CPrefixP'1834 { lid =
                                     (Obj.repr
                                       v_id'2051);
                                   lidx =
                                     (Obj.repr
                                       v_idx'2056);
                                   linput =
                                     (Obj.repr
                                       v_input'2057);
                                   lself =
                                     (Obj.repr
                                       v_self'2058);
                                   lrightChildAlts =
                                     (Obj.repr
                                       v_children'2048) })
                            | Option.None ->
                                (Obj.magic
                                   (Obj.magic
                                      v_defaultCase'2781
                                      ()))))
                    | _ ->
                        (Obj.magic
                           (v_defaultCase'2781
                              ()))
                  in
                  CTentativeLeaf'1841 { lparents =
                      (Obj.repr
                        v_parents'2049);
                    lnode =
                      (Obj.repr
                        v_node'2059) })
             | Option.None ->
                 (Obj.magic
                    (Obj.magic
                       v_defaultCase'2776
                       ())))
        | CTentativeRoot'1843 v_x'2793 ->
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
               (v_defaultCase'2776
                  ()));;
let v__addLeftChildren =
  fun v_st'2061 ->
    fun v_input'2062 ->
      fun v_self'2063 ->
        fun v_leftChildren'2064 ->
          fun v_parents'2065 ->
            let v_idx'2067 =
              Obj.magic
                (!)
                (let
                   CRec'2469 ({lnextIdx = v_X'2066})
                 =
                   Obj.magic
                     v_st'2061
                 in
                 Obj.magic
                   v_X'2066)
            in
            let v_defaultCase'2794 =
              fun nv_ ->
                failwith
                  "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 623:9-623:14 ERROR: Reached a never term, which should be impossible in a well-typed program."
            in
            match
              Obj.magic
                v_input'2062
            with
            | CInfixI'1827 v_x'2795 ->
                (let v_time'2069 =
                   Obj.magic
                     (!)
                     (let
                        CRec'2469 ({ltimestep = v_X'2068})
                      =
                        Obj.magic
                          v_st'2061
                      in
                      Obj.magic
                        v_X'2068)
                 in
                 let v_addedLeft'2070 =
                   Obj.magic
                     ref
                     (CRec'2499 { l0 =
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
                 let v_addedRight'2071 =
                   Obj.magic
                     ref
                     (CRec'2499 { l0 =
                          (Obj.repr
                            v__firstTimeStep);
                        l1 =
                          (Obj.repr
                            (Obj.magic
                               Boot.Intrinsics.Mseq.Helpers.of_array
                               [|  |])) })
                 in
                 CTentativeMid'1842 { lparents =
                     (Obj.repr
                       v_parents'2065);
                   laddedNodesLeftChildren =
                     (Obj.repr
                       v_addedLeft'2070);
                   laddedNodesRightChildren =
                     (Obj.repr
                       v_addedRight'2071);
                   ltentativeData =
                     (Obj.repr
                       (CInfixT'1837 { lidx =
                            (Obj.repr
                              v_idx'2067);
                          linput =
                            (Obj.repr
                              v_input'2062);
                          lself =
                            (Obj.repr
                              v_self'2063);
                          lleftChildAlts =
                            (Obj.repr
                              v_leftChildren'2064) }));
                   lmaxDistanceFromRoot =
                     (Obj.repr
                       (Obj.magic
                          Int.add
                          1
                          (Obj.magic
                             v_maxOrElse
                             (fun v_'2072 ->
                                0)
                             Int.sub
                             (Obj.magic
                                Boot.Intrinsics.Mseq.map
                                v__maxDistanceFromRoot
                                v_parents'2065)))) })
            | CPostfixI'1829 v_x'2796 ->
                (Obj.magic
                   (let v_id'2073 =
                      Obj.magic
                        v__uniqueID
                        ()
                    in
                    CTentativeLeaf'1841 { lparents =
                        (Obj.repr
                          v_parents'2065);
                      lnode =
                        (Obj.repr
                          (CPostfixP'1835 { lid =
                               (Obj.repr
                                 v_id'2073);
                             lidx =
                               (Obj.repr
                                 v_idx'2067);
                             linput =
                               (Obj.repr
                                 v_input'2062);
                             lself =
                               (Obj.repr
                                 v_self'2063);
                             lleftChildAlts =
                               (Obj.repr
                                 v_leftChildren'2064) })) }))
            | _ ->
                (Obj.magic
                   (v_defaultCase'2794
                      ()));;
let v__addRightChildToParent =
  fun v_time'2075 ->
    fun v_child'2076 ->
      fun v_parent'2077 ->
        let v_target'2078 =
          Obj.magic
            v__addedNodesRightChildren
            v_parent'2077
        in
        match
          Obj.magic
            (let v__target'2797 =
               Obj.magic
                 (!)
                 v_target'2078
             in
             let
               CRec'2499 ({l0 = v_0'2798;l1 = v_1'2799})
             =
               Obj.magic
                 Obj.magic
                 v__target'2797
             in
             Option.Some (v_0'2798, v_1'2799))
        with
        | Option.Some (v_lastUpdate'2079, v_prev'2080) ->
            (if
               Obj.magic
                 (Obj.magic
                    v__isBefore
                    v_lastUpdate'2079
                    v_time'2075)
             then
               let v_'2081 =
                 Obj.magic
                   (:=)
                   v_target'2078
                   (CRec'2499 { l0 =
                        (Obj.repr
                          v_time'2075);
                      l1 =
                        (Obj.repr
                          (Obj.magic
                             Boot.Intrinsics.Mseq.Helpers.of_array
                             [| (Obj.magic
                                 v_child'2076) |])) })
               in
               CSome'1690 (Obj.repr
                  v_parent'2077)
             else
               Obj.magic
                 (let v_'2082 =
                    Obj.magic
                      (:=)
                      v_target'2078
                      (CRec'2499 { l0 =
                           (Obj.repr
                             v_time'2075);
                         l1 =
                           (Obj.repr
                             (Obj.magic
                                Boot.Intrinsics.Mseq.cons
                                v_child'2076
                                v_prev'2080)) })
                  in
                  CNone'1691))
        | Option.None ->
            (Obj.magic
               (failwith
                  "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 639:9-639:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__addLeftChildToParent =
  fun v_time'2084 ->
    fun v_child'2085 ->
      fun v_parents'2086 ->
        match
          Obj.magic
            (let v__target'2800 =
               v_parents'2086
             in
             if
               Obj.magic
                 ((<) : int -> int -> bool)
                 (Obj.magic
                    Boot.Intrinsics.Mseq.length
                    v__target'2800)
                 1
             then
               Option.None
             else
               Obj.magic
                 Obj.magic
                 (let
                    (v__prefix'2801, v__splitTemp'2802)
                  =
                    Obj.magic
                      Boot.Intrinsics.Mseq.split_at
                      v__target'2800
                      1
                  in
                  let
                    (v__middle'2803, v__postfix'2804)
                  =
                    Obj.magic
                      Boot.Intrinsics.Mseq.split_at
                      v__splitTemp'2802
                      (Obj.magic
                         Int.sub
                         (Obj.magic
                            Boot.Intrinsics.Mseq.length
                            v__splitTemp'2802)
                         0)
                  in
                  let v__seqElem'2805 =
                    Obj.magic
                      Boot.Intrinsics.Mseq.get
                      v__prefix'2801
                      0
                  in
                  Option.Some (v__seqElem'2805)))
        with
        | Option.Some (v_p'2087) ->
            (let v_target'2088 =
               Obj.magic
                 v__addedNodesLeftChildren
                 v_p'2087
             in
             match
               Obj.magic
                 (let v__target'2806 =
                    Obj.magic
                      (!)
                      v_target'2088
                  in
                  let
                    CRec'2499 ({l0 = v_0'2807;l1 = v_1'2808})
                  =
                    Obj.magic
                      Obj.magic
                      v__target'2806
                  in
                  Option.Some (v_0'2807, v_1'2808))
             with
             | Option.Some (v_lastUpdate'2089, v_prev'2090) ->
                 (if
                    Obj.magic
                      (Obj.magic
                         v__isBefore
                         v_lastUpdate'2089
                         v_time'2084)
                  then
                    let v_leftChildrenHere'2091 =
                      Obj.magic
                        ref
                        (Obj.magic
                           Boot.Intrinsics.Mseq.Helpers.of_array
                           [| (Obj.magic
                               v_child'2085) |])
                    in
                    let v_'2093 =
                      Obj.magic
                        v_for_
                        v_parents'2086
                        (fun v_p'2092 ->
                           Obj.magic
                             (:=)
                             (Obj.magic
                                v__addedNodesLeftChildren
                                v_p'2092)
                             (CRec'2499 { l0 =
                                  (Obj.repr
                                    v_time'2084);
                                l1 =
                                  (Obj.repr
                                    v_leftChildrenHere'2091) }))
                    in
                    CSome'1690 (Obj.repr
                       v_parents'2086)
                  else
                    Obj.magic
                      (let v_'2094 =
                         Obj.magic
                           (:=)
                           v_prev'2090
                           (Obj.magic
                              Boot.Intrinsics.Mseq.cons
                              v_child'2085
                              (Obj.magic
                                 (!)
                                 v_prev'2090))
                       in
                       CNone'1691))
             | Option.None ->
                 (Obj.magic
                    (failwith
                       "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 657:11-657:16 ERROR: Reached a never term, which should be impossible in a well-typed program.")))
        | Option.None ->
            (Obj.magic
               (failwith
                  "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 658:9-658:14 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v__getOpGroup =
  fun v_input'2096 ->
    fun v_id'2097 ->
      if
        Obj.magic
          (Obj.magic
             v__eqOpId
             v_id'2097
             v__rootID)
      then
        CRec'2452 { lmayGroupLeft =
            (Obj.repr
              false);
          lmayGroupRight =
            (Obj.repr
              true) }
      else
        Obj.magic
          (match
             Obj.magic
               (let v__target'2809 =
                  v_input'2096
                in
                match
                  match
                    match
                      Obj.magic
                        Obj.magic
                        v__target'2809
                    with
                    | CInfixI'1827 v__n'2810 ->
                        (let
                           CRec'2476 ({lprecWhenThisIsRight = v_precWhenThisIsRight'2811})
                         =
                           Obj.magic
                             Obj.magic
                             v__target'2809
                         in
                         Option.Some (v_precWhenThisIsRight'2811))
                    | _ ->
                        (Obj.magic
                           Obj.magic
                           (Option.None))
                  with
                  | Option.Some v__x'2814 ->
                      (Option.Some v__x'2814)
                  | Option.None ->
                      (Obj.magic
                         Obj.magic
                         (match
                            Obj.magic
                              Obj.magic
                              v__target'2809
                          with
                          | CPostfixI'1829 v__n'2812 ->
                              (let
                                 CRec'2477 ({lprecWhenThisIsRight = v_precWhenThisIsRight'2813})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__target'2809
                               in
                               Option.Some (v_precWhenThisIsRight'2813))
                          | _ ->
                              (Obj.magic
                                 Obj.magic
                                 (Option.None))))
                with
                | Option.Some (v_prec'2098) ->
                    (Option.Some (v_prec'2098))
                | Option.None ->
                    (Obj.magic
                       Obj.magic
                       (Option.None)))
           with
           | Option.Some (v_prec'2098) ->
               (match
                  Obj.magic
                    (let v__target'2815 =
                       Obj.magic
                         v_mapLookup
                         v_id'2097
                         v_prec'2098
                     in
                     match
                       Obj.magic
                         Obj.magic
                         v__target'2815
                     with
                     | CSome'1690 v__n'2816 ->
                         (Option.Some (v__n'2816))
                     | _ ->
                         (Obj.magic
                            Obj.magic
                            (Option.None)))
                with
                | Option.Some (v_res'2099) ->
                    v_res'2099
                | Option.None ->
                    (Obj.magic
                       (CRec'2452 { lmayGroupLeft =
                            (Obj.repr
                              true);
                          lmayGroupRight =
                            (Obj.repr
                              true) })))
           | Option.None ->
               (Obj.magic
                  (failwith
                     "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 670:9-670:14 ERROR: Reached a never term, which should be impossible in a well-typed program.")));;
let v__mayGroupRight =
  fun v_l'2101 ->
    fun v_r'2102 ->
      let
        CRec'2452 ({lmayGroupRight = v_X'2103})
      =
        Obj.magic
          (Obj.magic
             v__getOpGroup
             v_r'2102
             (Obj.magic
                v__opIdT
                v_l'2101))
      in
      Obj.magic
        v_X'2103;;
let v__mayGroupLeft =
  fun v_l'2105 ->
    fun v_r'2106 ->
      let
        CRec'2452 ({lmayGroupLeft = v_X'2107})
      =
        Obj.magic
          (Obj.magic
             v__getOpGroup
             v_r'2106
             (Obj.magic
                v__opIdT
                v_l'2105))
      in
      Obj.magic
        v_X'2107;;
let v__newQueueFromFrontier =
  fun v_frontier'2110 ->
    Obj.magic
      Boot.Intrinsics.Mseq.create
      (Obj.magic
         Int.add
         1
         (Obj.magic
            v_maxOrElse
            (fun v_'2111 ->
               0)
            Int.sub
            (Obj.magic
               Boot.Intrinsics.Mseq.map
               v__maxDistanceFromRoot
               v_frontier'2110)))
      (fun v_'2112 ->
         Obj.magic
           ref
           (Obj.magic
              Boot.Intrinsics.Mseq.Helpers.of_array
              [|  |]));;
let v__addToQueue =
  fun v_node'2114 ->
    fun v_queue'2115 ->
      let v_dist'2116 =
        Obj.magic
          v__maxDistanceFromRoot
          v_node'2114
      in
      let v_target'2117 =
        Obj.magic
          Boot.Intrinsics.Mseq.get
          v_queue'2115
          v_dist'2116
      in
      Obj.magic
        (:=)
        v_target'2117
        (Obj.magic
           Boot.Intrinsics.Mseq.snoc
           (Obj.magic
              (!)
              v_target'2117)
           v_node'2114);;
let rec v__popFromQueue =
    fun v_queue'2120 ->
      match
        Obj.magic
          (let v__target'2817 =
             v_queue'2120
           in
           if
             Obj.magic
               ((<) : int -> int -> bool)
               (Obj.magic
                  Boot.Intrinsics.Mseq.length
                  v__target'2817)
               1
           then
             Option.None
           else
             Obj.magic
               Obj.magic
               (let
                  (v__prefix'2818, v__splitTemp'2819)
                =
                  Obj.magic
                    Boot.Intrinsics.Mseq.split_at
                    v__target'2817
                    0
                in
                let
                  (v__middle'2820, v__postfix'2821)
                =
                  Obj.magic
                    Boot.Intrinsics.Mseq.split_at
                    v__splitTemp'2819
                    (Obj.magic
                       Int.sub
                       (Obj.magic
                          Boot.Intrinsics.Mseq.length
                          v__splitTemp'2819)
                       1)
                in
                let v__seqElem'2822 =
                  Obj.magic
                    Boot.Intrinsics.Mseq.get
                    v__postfix'2821
                    0
                in
                Option.Some (v__middle'2820, v__seqElem'2822)))
      with
      | Option.Some (v_queue'2121, v_target'2122) ->
          (let v_nodes'2123 =
             Obj.magic
               (!)
               v_target'2122
           in
           match
             Obj.magic
               (let v__target'2823 =
                  v_nodes'2123
                in
                if
                  Obj.magic
                    ((<) : int -> int -> bool)
                    (Obj.magic
                       Boot.Intrinsics.Mseq.length
                       v__target'2823)
                    1
                then
                  Option.None
                else
                  Obj.magic
                    Obj.magic
                    (let
                       (v__prefix'2824, v__splitTemp'2825)
                     =
                       Obj.magic
                         Boot.Intrinsics.Mseq.split_at
                         v__target'2823
                         1
                     in
                     let
                       (v__middle'2826, v__postfix'2827)
                     =
                       Obj.magic
                         Boot.Intrinsics.Mseq.split_at
                         v__splitTemp'2825
                         (Obj.magic
                            Int.sub
                            (Obj.magic
                               Boot.Intrinsics.Mseq.length
                               v__splitTemp'2825)
                            0)
                     in
                     let v__seqElem'2828 =
                       Obj.magic
                         Boot.Intrinsics.Mseq.get
                         v__prefix'2824
                         0
                     in
                     Option.Some (v__seqElem'2828, v__middle'2826)))
           with
           | Option.Some (v_node'2124, v_nodes'2125) ->
               (let v_'2126 =
                  Obj.magic
                    (:=)
                    v_target'2122
                    v_nodes'2125
                in
                CSome'1690 (Obj.repr
                   v_node'2124))
           | Option.None ->
               (Obj.magic
                  (Obj.magic
                     v__popFromQueue
                     v_queue'2121)))
      | Option.None ->
          (Obj.magic
             CNone'1691);;
let v__addLOpen =
  fun v_input'2127 ->
    fun v_self'2128 ->
      fun v_st'2129 ->
        let v_time'2131 =
          Obj.magic
            Int.add
            1
            (Obj.magic
               (!)
               (let
                  CRec'2469 ({ltimestep = v_X'2130})
                =
                  Obj.magic
                    v_st'2129
                in
                Obj.magic
                  v_X'2130))
        in
        let v_'2133 =
          Obj.magic
            (:=)
            (let
               CRec'2469 ({ltimestep = v_X'2132})
             =
               Obj.magic
                 v_st'2129
             in
             Obj.magic
               v_X'2132)
            v_time'2131
        in
        let v_makeNewParents'2140 =
          fun v_parents'2134 ->
            match
              Obj.magic
                (let v__target'2829 =
                   v_parents'2134
                 in
                 if
                   Obj.magic
                     ((<) : int -> int -> bool)
                     (Obj.magic
                        Boot.Intrinsics.Mseq.length
                        v__target'2829)
                     1
                 then
                   Option.None
                 else
                   Obj.magic
                     Obj.magic
                     (let
                        (v__prefix'2830, v__splitTemp'2831)
                      =
                        Obj.magic
                          Boot.Intrinsics.Mseq.split_at
                          v__target'2829
                          1
                      in
                      let
                        (v__middle'2832, v__postfix'2833)
                      =
                        Obj.magic
                          Boot.Intrinsics.Mseq.split_at
                          v__splitTemp'2831
                          (Obj.magic
                             Int.sub
                             (Obj.magic
                                Boot.Intrinsics.Mseq.length
                                v__splitTemp'2831)
                             0)
                      in
                      let v__seqElem'2834 =
                        Obj.magic
                          Boot.Intrinsics.Mseq.get
                          v__prefix'2830
                          0
                      in
                      Option.Some (v__seqElem'2834)))
            with
            | Option.Some (v_p'2135) ->
                (let v_snd'2138 =
                   fun v_x'2136 ->
                     let
                       CRec'2499 ({l1 = v_X'2137})
                     =
                       Obj.magic
                         v_x'2136
                     in
                     Obj.magic
                       v_X'2137
                 in
                 let v_cs'2139 =
                   Obj.magic
                     (!)
                     (Obj.magic
                        v_snd'2138
                        (Obj.magic
                           (!)
                           (Obj.magic
                              v__addedNodesLeftChildren
                              v_p'2135)))
                 in
                 match
                   Obj.magic
                     (let v__target'2835 =
                        v_cs'2139
                      in
                      if
                        Obj.magic
                          ((<) : int -> int -> bool)
                          (Obj.magic
                             Boot.Intrinsics.Mseq.length
                             v__target'2835)
                          1
                      then
                        Option.None
                      else
                        Obj.magic
                          Obj.magic
                          (let
                             (v__prefix'2836, v__splitTemp'2837)
                           =
                             Obj.magic
                               Boot.Intrinsics.Mseq.split_at
                               v__target'2835
                               1
                           in
                           let
                             (v__middle'2838, v__postfix'2839)
                           =
                             Obj.magic
                               Boot.Intrinsics.Mseq.split_at
                               v__splitTemp'2837
                               (Obj.magic
                                  Int.sub
                                  (Obj.magic
                                     Boot.Intrinsics.Mseq.length
                                     v__splitTemp'2837)
                                  0)
                           in
                           let v__seqElem'2840 =
                             Obj.magic
                               Boot.Intrinsics.Mseq.get
                               v__prefix'2836
                               0
                           in
                           Option.Some ()))
                 with
                 | Option.Some () ->
                     (Obj.magic
                        v__addLeftChildren
                        v_st'2129
                        v_input'2127
                        v_self'2128
                        v_cs'2139
                        v_parents'2134)
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
                      "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 738:13-738:18 ERROR: Reached a never term, which should be impossible in a well-typed program."))
        in
        let v_handleLeaf'2158 =
          fun v_queue'2141 ->
            fun v_child'2142 ->
              match
                Obj.magic
                  (let v__target'2841 =
                     Obj.magic
                       v__getParents
                       v_child'2142
                   in
                   match
                     Obj.magic
                       Obj.magic
                       v__target'2841
                   with
                   | CSome'1690 v__n'2842 ->
                       (Option.Some (v__n'2842))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None)))
              with
              | Option.Some (v_parents'2143) ->
                  (let v_shallowRight'2144 =
                     Obj.magic
                       v__shallowAllowedLeft
                       v_input'2127
                       v_child'2142
                   in
                   let v_f'2154 =
                     fun v_parent'2145 ->
                       let v_shallowLeft'2146 =
                         Obj.magic
                           v__shallowAllowedRight
                           v_parent'2145
                           v_child'2142
                       in
                       let v_precLeft'2147 =
                         Obj.magic
                           v__mayGroupLeft
                           v_parent'2145
                           v_input'2127
                       in
                       let v_precRight'2148 =
                         Obj.magic
                           v__mayGroupRight
                           v_parent'2145
                           v_input'2127
                       in
                       let v_config'2149 =
                         CRec'2486 { l0 =
                             (Obj.repr
                               v_shallowLeft'2146);
                           l1 =
                             (Obj.repr
                               v_shallowRight'2144);
                           l2 =
                             (Obj.repr
                               v_precLeft'2147);
                           l3 =
                             (Obj.repr
                               v_precRight'2148) }
                       in
                       let v_'2152 =
                         match
                           Obj.magic
                             (let v__target'2843 =
                                v_config'2149
                              in
                              match
                                match
                                  let
                                    CRec'2486 ({l0 = v_0'2844;l1 = v_1'2845;l2 = v_2'2846;l3 = v_3'2847})
                                  =
                                    Obj.magic
                                      Obj.magic
                                      v__target'2843
                                  in
                                  match
                                    Obj.magic
                                      Obj.magic
                                      v_0'2844
                                  with
                                  | CSome'1690 v__n'2848 ->
                                      (match
                                         Obj.magic
                                           Obj.magic
                                           v_1'2845
                                       with
                                       | CNone'1691 ->
                                           (Option.Some (v__n'2848))
                                       | _ ->
                                           (Obj.magic
                                              Obj.magic
                                              (Option.None)))
                                  | _ ->
                                      (Obj.magic
                                         Obj.magic
                                         (Option.None))
                                with
                                | Option.Some v__x'2855 ->
                                    (Option.Some v__x'2855)
                                | Option.None ->
                                    (Obj.magic
                                       Obj.magic
                                       (let
                                          CRec'2486 ({l0 = v_0'2850;l1 = v_1'2851;l2 = v_2'2852;l3 = v_3'2853})
                                        =
                                          Obj.magic
                                            Obj.magic
                                            v__target'2843
                                        in
                                        match
                                          Obj.magic
                                            Obj.magic
                                            v_0'2850
                                        with
                                        | CSome'1690 v__n'2854 ->
                                            (if
                                               Obj.magic
                                                 Obj.magic
                                                 v_2'2852
                                             then
                                               Option.Some (v__n'2854)
                                             else
                                               Obj.magic
                                                 Obj.magic
                                                 (Option.None))
                                        | _ ->
                                            (Obj.magic
                                               Obj.magic
                                               (Option.None))))
                              with
                              | Option.Some (v_child'2150) ->
                                  (Option.Some (v_child'2150))
                              | Option.None ->
                                  (Obj.magic
                                     Obj.magic
                                     (Option.None)))
                         with
                         | Option.Some (v_child'2150) ->
                             (match
                                Obj.magic
                                  (let v__target'2856 =
                                     Obj.magic
                                       v__addRightChildToParent
                                       v_time'2131
                                       v_child'2150
                                       v_parent'2145
                                   in
                                   match
                                     Obj.magic
                                       Obj.magic
                                       v__target'2856
                                   with
                                   | CSome'1690 v__n'2857 ->
                                       (Option.Some (v__n'2857))
                                   | _ ->
                                       (Obj.magic
                                          Obj.magic
                                          (Option.None)))
                              with
                              | Option.Some (v_parent'2151) ->
                                  (Obj.magic
                                     v__addToQueue
                                     v_parent'2151
                                     v_queue'2141)
                              | Option.None ->
                                  (Obj.magic
                                     ()))
                         | Option.None ->
                             (Obj.magic
                                ())
                       in
                       match
                         Obj.magic
                           (let v__target'2858 =
                              v_config'2149
                            in
                            match
                              match
                                let
                                  CRec'2486 ({l0 = v_0'2859;l1 = v_1'2860;l2 = v_2'2861;l3 = v_3'2862})
                                =
                                  Obj.magic
                                    Obj.magic
                                    v__target'2858
                                in
                                match
                                  Obj.magic
                                    Obj.magic
                                    v_0'2859
                                with
                                | CNone'1691 ->
                                    (match
                                       Obj.magic
                                         Obj.magic
                                         v_1'2860
                                     with
                                     | CSome'1690 v__n'2864 ->
                                         (Option.Some (v__n'2864))
                                     | _ ->
                                         (Obj.magic
                                            Obj.magic
                                            (Option.None)))
                                | _ ->
                                    (Obj.magic
                                       Obj.magic
                                       (Option.None))
                              with
                              | Option.Some v__x'2870 ->
                                  (Option.Some v__x'2870)
                              | Option.None ->
                                  (Obj.magic
                                     Obj.magic
                                     (let
                                        CRec'2486 ({l0 = v_0'2865;l1 = v_1'2866;l2 = v_2'2867;l3 = v_3'2868})
                                      =
                                        Obj.magic
                                          Obj.magic
                                          v__target'2858
                                      in
                                      match
                                        Obj.magic
                                          Obj.magic
                                          v_1'2866
                                      with
                                      | CSome'1690 v__n'2869 ->
                                          (if
                                             Obj.magic
                                               Obj.magic
                                               v_3'2868
                                           then
                                             Option.Some (v__n'2869)
                                           else
                                             Obj.magic
                                               Obj.magic
                                               (Option.None))
                                      | _ ->
                                          (Obj.magic
                                             Obj.magic
                                             (Option.None))))
                            with
                            | Option.Some (v_child'2153) ->
                                (Option.Some (v_child'2153))
                            | Option.None ->
                                (Obj.magic
                                   Obj.magic
                                   (Option.None)))
                       with
                       | Option.Some (v_child'2153) ->
                           true
                       | Option.None ->
                           (Obj.magic
                              false)
                   in
                   let v_parentsThatAllowRight'2155 =
                     Obj.magic
                       v_filter
                       v_f'2154
                       v_parents'2143
                   in
                   match
                     Obj.magic
                       (let v__target'2871 =
                          CRec'2499 { l0 =
                              (Obj.repr
                                v_shallowRight'2144);
                            l1 =
                              (Obj.repr
                                v_parentsThatAllowRight'2155) }
                        in
                        let
                          CRec'2499 ({l0 = v_0'2872;l1 = v_1'2873})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2871
                        in
                        match
                          Obj.magic
                            Obj.magic
                            v_0'2872
                        with
                        | CSome'1690 v__n'2874 ->
                            (if
                               Obj.magic
                                 ((<) : int -> int -> bool)
                                 (Obj.magic
                                    Boot.Intrinsics.Mseq.length
                                    v_1'2873)
                                 1
                             then
                               Option.None
                             else
                               Obj.magic
                                 Obj.magic
                                 (let
                                    (v__prefix'2875, v__splitTemp'2876)
                                  =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.split_at
                                      v_1'2873
                                      1
                                  in
                                  let
                                    (v__middle'2877, v__postfix'2878)
                                  =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.split_at
                                      v__splitTemp'2876
                                      (Obj.magic
                                         Int.sub
                                         (Obj.magic
                                            Boot.Intrinsics.Mseq.length
                                            v__splitTemp'2876)
                                         0)
                                  in
                                  let v__seqElem'2879 =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.get
                                      v__prefix'2875
                                      0
                                  in
                                  Option.Some (v__n'2874, v_1'2873)))
                        | _ ->
                            (Obj.magic
                               Obj.magic
                               (Option.None)))
                   with
                   | Option.Some (v_child'2156, v_parents'2157) ->
                       (Obj.magic
                          v__addLeftChildToParent
                          v_time'2131
                          v_child'2156
                          v_parents'2157)
                   | Option.None ->
                       (Obj.magic
                          CNone'1691))
              | Option.None ->
                  (Obj.magic
                     (failwith
                        "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 766:13-766:18 ERROR: Reached a never term, which should be impossible in a well-typed program."))
        in
        let rec v_work'2159 =
            fun v_queue'2160 ->
              fun v_acc'2161 ->
                match
                  Obj.magic
                    (let v__target'2880 =
                       Obj.magic
                         v__popFromQueue
                         v_queue'2160
                     in
                     match
                       Obj.magic
                         Obj.magic
                         v__target'2880
                     with
                     | CSome'1690 v__n'2881 ->
                         (match
                            Obj.magic
                              Obj.magic
                              v__n'2881
                          with
                          | CTentativeMid'1842 v__n'2882 ->
                              (let
                                 CRec'2489 ({laddedNodesRightChildren = v_addedNodesRightChildren'2883})
                               =
                                 Obj.magic
                                   Obj.magic
                                   v__n'2881
                               in
                               Option.Some (v__n'2881, v_addedNodesRightChildren'2883))
                          | _ ->
                              (Obj.magic
                                 Obj.magic
                                 (Option.None)))
                     | _ ->
                         (Obj.magic
                            Obj.magic
                            (Option.None)))
                with
                | Option.Some (v_parent'2162, v_addedRight'2163) ->
                    (match
                       Obj.magic
                         (let v__target'2884 =
                            Obj.magic
                              (!)
                              v_addedRight'2163
                          in
                          let
                            CRec'2499 ({l0 = v_0'2885;l1 = v_1'2886})
                          =
                            Obj.magic
                              Obj.magic
                              v__target'2884
                          in
                          if
                            Obj.magic
                              ((<) : int -> int -> bool)
                              (Obj.magic
                                 Boot.Intrinsics.Mseq.length
                                 v_1'2886)
                              1
                          then
                            Option.None
                          else
                            Obj.magic
                              Obj.magic
                              (let
                                 (v__prefix'2887, v__splitTemp'2888)
                               =
                                 Obj.magic
                                   Boot.Intrinsics.Mseq.split_at
                                   v_1'2886
                                   1
                               in
                               let
                                 (v__middle'2889, v__postfix'2890)
                               =
                                 Obj.magic
                                   Boot.Intrinsics.Mseq.split_at
                                   v__splitTemp'2888
                                   (Obj.magic
                                      Int.sub
                                      (Obj.magic
                                         Boot.Intrinsics.Mseq.length
                                         v__splitTemp'2888)
                                      0)
                               in
                               let v__seqElem'2891 =
                                 Obj.magic
                                   Boot.Intrinsics.Mseq.get
                                   v__prefix'2887
                                   0
                               in
                               Option.Some (v_1'2886)))
                     with
                     | Option.Some (v_children'2164) ->
                         (let v_acc'2166 =
                            match
                              Obj.magic
                                (let v__target'2892 =
                                   Obj.magic
                                     v_handleLeaf'2158
                                     v_queue'2160
                                     (Obj.magic
                                        v__addRightChildren
                                        v_st'2129
                                        v_parent'2162
                                        v_children'2164)
                                 in
                                 match
                                   Obj.magic
                                     Obj.magic
                                     v__target'2892
                                 with
                                 | CSome'1690 v__n'2893 ->
                                     (Option.Some (v__n'2893))
                                 | _ ->
                                     (Obj.magic
                                        Obj.magic
                                        (Option.None)))
                            with
                            | Option.Some (v_n'2165) ->
                                (Obj.magic
                                   Boot.Intrinsics.Mseq.cons
                                   v_n'2165
                                   v_acc'2161)
                            | Option.None ->
                                (Obj.magic
                                   v_acc'2161)
                          in
                          Obj.magic
                            v_work'2159
                            v_queue'2160
                            v_acc'2166)
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
                       v_acc'2161)
        in let v_frontier'2168 =
          let
            CRec'2469 ({lfrontier = v_X'2167})
          =
            Obj.magic
              v_st'2129
          in
          Obj.magic
            v_X'2167
        in
        let v_queue'2169 =
          Obj.magic
            v__newQueueFromFrontier
            v_frontier'2168
        in
        let v_newParents'2170 =
          Obj.magic
            v_mapOption
            (Obj.magic
               v_handleLeaf'2158
               v_queue'2169)
            v_frontier'2168
        in
        let v_newParents'2171 =
          Obj.magic
            v_work'2159
            v_queue'2169
            v_newParents'2170
        in
        match
          Obj.magic
            (let v__target'2894 =
               Obj.magic
                 Boot.Intrinsics.Mseq.map
                 v_makeNewParents'2140
                 v_newParents'2171
             in
             if
               Obj.magic
                 ((<) : int -> int -> bool)
                 (Obj.magic
                    Boot.Intrinsics.Mseq.length
                    v__target'2894)
                 1
             then
               Option.None
             else
               Obj.magic
                 Obj.magic
                 (let
                    (v__prefix'2895, v__splitTemp'2896)
                  =
                    Obj.magic
                      Boot.Intrinsics.Mseq.split_at
                      v__target'2894
                      1
                  in
                  let
                    (v__middle'2897, v__postfix'2898)
                  =
                    Obj.magic
                      Boot.Intrinsics.Mseq.split_at
                      v__splitTemp'2896
                      (Obj.magic
                         Int.sub
                         (Obj.magic
                            Boot.Intrinsics.Mseq.length
                            v__splitTemp'2896)
                         0)
                  in
                  let v__seqElem'2899 =
                    Obj.magic
                      Boot.Intrinsics.Mseq.get
                      v__prefix'2895
                      0
                  in
                  Option.Some (v__target'2894)))
        with
        | Option.Some (v_frontier'2172) ->
            (CSome'1690 (Obj.repr
                (let
                   CRec'2469 v_rec'2900
                 =
                   Obj.magic
                     v_st'2129
                 in
                 CRec'2469 { v_rec'2900
                   with
                   lfrontier =
                     Obj.repr
                       v_frontier'2172 })))
        | Option.None ->
            (Obj.magic
               CNone'1691);;
let v_breakableAddPrefix =
  fun v_input'2174 ->
    fun v_self'2175 ->
      fun v_st'2176 ->
        let v_frontier'2178 =
          let
            CRec'2469 ({lfrontier = v_X'2177})
          =
            Obj.magic
              v_st'2176
          in
          Obj.magic
            v_X'2177
        in
        let v_time'2180 =
          Obj.magic
            (!)
            (let
               CRec'2469 ({ltimestep = v_X'2179})
             =
               Obj.magic
                 v_st'2176
             in
             Obj.magic
               v_X'2179)
        in
        let v_idx'2182 =
          Obj.magic
            (!)
            (let
               CRec'2469 ({lnextIdx = v_X'2181})
             =
               Obj.magic
                 v_st'2176
             in
             Obj.magic
               v_X'2181)
        in
        let v_'2184 =
          Obj.magic
            (:=)
            (let
               CRec'2469 ({lnextIdx = v_X'2183})
             =
               Obj.magic
                 v_st'2176
             in
             Obj.magic
               v_X'2183)
            (Obj.magic
               Int.add
               1
               v_idx'2182)
        in
        let v_addedLeft'2185 =
          Obj.magic
            ref
            (CRec'2499 { l0 =
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
        let v_addedRight'2186 =
          Obj.magic
            ref
            (CRec'2499 { l0 =
                 (Obj.repr
                   v__firstTimeStep);
               l1 =
                 (Obj.repr
                   (Obj.magic
                      Boot.Intrinsics.Mseq.Helpers.of_array
                      [|  |])) })
        in
        let
          CRec'2469 v_rec'2901
        =
          Obj.magic
            v_st'2176
        in
        CRec'2469 { v_rec'2901
          with
          lfrontier =
            Obj.repr
              (Obj.magic
                 Boot.Intrinsics.Mseq.Helpers.of_array
                 [| (Obj.magic
                     (CTentativeMid'1842 { lparents =
                          (Obj.repr
                            v_frontier'2178);
                        laddedNodesLeftChildren =
                          (Obj.repr
                            v_addedLeft'2185);
                        laddedNodesRightChildren =
                          (Obj.repr
                            v_addedRight'2186);
                        ltentativeData =
                          (Obj.repr
                            (CPrefixT'1838 { lidx =
                                 (Obj.repr
                                   v_idx'2182);
                               linput =
                                 (Obj.repr
                                   v_input'2174);
                               lself =
                                 (Obj.repr
                                   v_self'2175) }));
                        lmaxDistanceFromRoot =
                          (Obj.repr
                            (Obj.magic
                               Int.add
                               1
                               (Obj.magic
                                  v_maxOrElse
                                  (fun v_'2187 ->
                                     0)
                                  Int.sub
                                  (Obj.magic
                                     Boot.Intrinsics.Mseq.map
                                     v__maxDistanceFromRoot
                                     v_frontier'2178)))) })) |]) };;
let v_breakableAddInfix =
  fun v_input'2189 ->
    fun v_self'2190 ->
      fun v_st'2191 ->
        let v_res'2192 =
          Obj.magic
            v__addLOpen
            v_input'2189
            v_self'2190
            v_st'2191
        in
        let v_'2195 =
          Obj.magic
            (:=)
            (let
               CRec'2469 ({lnextIdx = v_X'2193})
             =
               Obj.magic
                 v_st'2191
             in
             Obj.magic
               v_X'2193)
            (Obj.magic
               Int.add
               1
               (Obj.magic
                  (!)
                  (let
                     CRec'2469 ({lnextIdx = v_X'2194})
                   =
                     Obj.magic
                       v_st'2191
                   in
                   Obj.magic
                     v_X'2194)))
        in
        v_res'2192;;
let v_breakableAddPostfix =
  fun v_input'2197 ->
    fun v_self'2198 ->
      fun v_st'2199 ->
        let v_res'2200 =
          Obj.magic
            v__addLOpen
            v_input'2197
            v_self'2198
            v_st'2199
        in
        let v_'2203 =
          Obj.magic
            (:=)
            (let
               CRec'2469 ({lnextIdx = v_X'2201})
             =
               Obj.magic
                 v_st'2199
             in
             Obj.magic
               v_X'2201)
            (Obj.magic
               Int.add
               1
               (Obj.magic
                  (!)
                  (let
                     CRec'2469 ({lnextIdx = v_X'2202})
                   =
                     Obj.magic
                       v_st'2199
                   in
                   Obj.magic
                     v_X'2202)))
        in
        v_res'2200;;
let v_breakableAddAtom =
  fun v_input'2205 ->
    fun v_self'2206 ->
      fun v_st'2207 ->
        let v_idx'2209 =
          Obj.magic
            (!)
            (let
               CRec'2469 ({lnextIdx = v_X'2208})
             =
               Obj.magic
                 v_st'2207
             in
             Obj.magic
               v_X'2208)
        in
        let v_'2211 =
          Obj.magic
            (:=)
            (let
               CRec'2469 ({lnextIdx = v_X'2210})
             =
               Obj.magic
                 v_st'2207
             in
             Obj.magic
               v_X'2210)
            (Obj.magic
               Int.add
               1
               v_idx'2209)
        in
        let v_id'2212 =
          Obj.magic
            v__uniqueID
            ()
        in
        let
          CRec'2469 v_rec'2902
        =
          Obj.magic
            v_st'2207
        in
        CRec'2469 { v_rec'2902
          with
          lfrontier =
            Obj.repr
              (Obj.magic
                 Boot.Intrinsics.Mseq.Helpers.of_array
                 [| (Obj.magic
                     (CTentativeLeaf'1841 { lparents =
                          (Obj.repr
                            (let
                               CRec'2469 ({lfrontier = v_X'2213})
                             =
                               Obj.magic
                                 v_st'2207
                             in
                             Obj.magic
                               v_X'2213));
                        lnode =
                          (Obj.repr
                            (CAtomP'1832 { lid =
                                 (Obj.repr
                                   v_id'2212);
                               lidx =
                                 (Obj.repr
                                   v_idx'2209);
                               linput =
                                 (Obj.repr
                                   v_input'2205);
                               lself =
                                 (Obj.repr
                                   v_self'2206) })) })) |]) };;
let v_breakableFinalizeParse =
  fun v_st'2215 ->
    let v_time'2217 =
      Obj.magic
        Int.add
        1
        (Obj.magic
           (!)
           (let
              CRec'2469 ({ltimestep = v_X'2216})
            =
              Obj.magic
                v_st'2215
            in
            Obj.magic
              v_X'2216))
    in
    let v_'2219 =
      Obj.magic
        (:=)
        (let
           CRec'2469 ({ltimestep = v_X'2218})
         =
           Obj.magic
             v_st'2215
         in
         Obj.magic
           v_X'2218)
        v_time'2217
    in
    let v_handleLeaf'2226 =
      fun v_queue'2220 ->
        fun v_child'2221 ->
          match
            Obj.magic
              (let v__target'2903 =
                 Obj.magic
                   v__getParents
                   v_child'2221
               in
               match
                 Obj.magic
                   Obj.magic
                   v__target'2903
               with
               | CSome'1690 v__n'2904 ->
                   (Option.Some (v__n'2904))
               | _ ->
                   (Obj.magic
                      Obj.magic
                      (Option.None)))
          with
          | Option.Some (v_parents'2222) ->
              (Obj.magic
                 v_for_
                 v_parents'2222
                 (fun v_parent'2223 ->
                    match
                      Obj.magic
                        (let v__target'2905 =
                           Obj.magic
                             v__shallowAllowedRight
                             v_parent'2223
                             v_child'2221
                         in
                         match
                           Obj.magic
                             Obj.magic
                             v__target'2905
                         with
                         | CSome'1690 v__n'2906 ->
                             (Option.Some (v__n'2906))
                         | _ ->
                             (Obj.magic
                                Obj.magic
                                (Option.None)))
                    with
                    | Option.Some (v_child'2224) ->
                        (match
                           Obj.magic
                             (let v__target'2907 =
                                Obj.magic
                                  v__addRightChildToParent
                                  v_time'2217
                                  v_child'2224
                                  v_parent'2223
                              in
                              match
                                Obj.magic
                                  Obj.magic
                                  v__target'2907
                              with
                              | CSome'1690 v__n'2908 ->
                                  (Option.Some (v__n'2908))
                              | _ ->
                                  (Obj.magic
                                     Obj.magic
                                     (Option.None)))
                         with
                         | Option.Some (v_parent'2225) ->
                             (Obj.magic
                                v__addToQueue
                                v_parent'2225
                                v_queue'2220)
                         | Option.None ->
                             (Obj.magic
                                ()))
                    | Option.None ->
                        (Obj.magic
                           ())))
          | Option.None ->
              (Obj.magic
                 (failwith
                    "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 882:13-882:18 ERROR: Reached a never term, which should be impossible in a well-typed program."))
    in
    let rec v_work'2227 =
        fun v_queue'2228 ->
          match
            Obj.magic
              (let v__target'2909 =
                 Obj.magic
                   v__popFromQueue
                   v_queue'2228
               in
               match
                 Obj.magic
                   Obj.magic
                   v__target'2909
               with
               | CSome'1690 v__n'2910 ->
                   (Option.Some (v__n'2910))
               | _ ->
                   (Obj.magic
                      Obj.magic
                      (Option.None)))
          with
          | Option.Some (v_p'2229) ->
              (let v_snd'2232 =
                 fun v_x'2230 ->
                   let
                     CRec'2499 ({l1 = v_X'2231})
                   =
                     Obj.magic
                       v_x'2230
                   in
                   Obj.magic
                     v_X'2231
               in
               let v_children'2233 =
                 Obj.magic
                   v_snd'2232
                   (Obj.magic
                      (!)
                      (Obj.magic
                         v__addedNodesRightChildren
                         v_p'2229))
               in
               let v_defaultCase'2911 =
                 fun nv_ ->
                   match
                     Obj.magic
                       (let v__target'2912 =
                          CRec'2499 { l0 =
                              (Obj.repr
                                v_p'2229);
                            l1 =
                              (Obj.repr
                                v_children'2233) }
                        in
                        let
                          CRec'2499 ({l0 = v_0'2913;l1 = v_1'2914})
                        =
                          Obj.magic
                            Obj.magic
                            v__target'2912
                        in
                        match
                          Obj.magic
                            Obj.magic
                            v_0'2913
                        with
                        | CTentativeMid'1842 v__n'2915 ->
                            (if
                               Obj.magic
                                 ((<) : int -> int -> bool)
                                 (Obj.magic
                                    Boot.Intrinsics.Mseq.length
                                    v_1'2914)
                                 1
                             then
                               Option.None
                             else
                               Obj.magic
                                 Obj.magic
                                 (let
                                    (v__prefix'2916, v__splitTemp'2917)
                                  =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.split_at
                                      v_1'2914
                                      1
                                  in
                                  let
                                    (v__middle'2918, v__postfix'2919)
                                  =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.split_at
                                      v__splitTemp'2917
                                      (Obj.magic
                                         Int.sub
                                         (Obj.magic
                                            Boot.Intrinsics.Mseq.length
                                            v__splitTemp'2917)
                                         0)
                                  in
                                  let v__seqElem'2920 =
                                    Obj.magic
                                      Boot.Intrinsics.Mseq.get
                                      v__prefix'2916
                                      0
                                  in
                                  Option.Some ()))
                        | _ ->
                            (Obj.magic
                               Obj.magic
                               (Option.None)))
                   with
                   | Option.Some () ->
                       (let v_'2234 =
                          Obj.magic
                            v_handleLeaf'2226
                            v_queue'2228
                            (Obj.magic
                               v__addRightChildren
                               v_st'2215
                               v_p'2229
                               v_children'2233)
                        in
                        Obj.magic
                          v_work'2227
                          v_queue'2228)
                   | Option.None ->
                       (Obj.magic
                          (match
                             Obj.magic
                               (let v__target'2921 =
                                  v_p'2229
                                in
                                match
                                  Obj.magic
                                    Obj.magic
                                    v__target'2921
                                with
                                | CTentativeMid'1842 v__n'2922 ->
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
                                     "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 898:15-898:20 ERROR: Reached a never term, which should be impossible in a well-typed program."))))
               in
               match
                 Obj.magic
                   v_p'2229
               with
               | CTentativeRoot'1843 v_x'2923 ->
                   v_children'2233
               | _ ->
                   (Obj.magic
                      (v_defaultCase'2911
                         ())))
          | Option.None ->
              (Obj.magic
                 (Obj.magic
                    Boot.Intrinsics.Mseq.Helpers.of_array
                    [|  |]))
    in let v_frontier'2236 =
      let
        CRec'2469 ({lfrontier = v_X'2235})
      =
        Obj.magic
          v_st'2215
      in
      Obj.magic
        v_X'2235
    in
    let v_queue'2237 =
      Obj.magic
        v__newQueueFromFrontier
        v_frontier'2236
    in
    let v_'2238 =
      Obj.magic
        Boot.Intrinsics.Mseq.iter
        (Obj.magic
           v_handleLeaf'2226
           v_queue'2237)
        v_frontier'2236
    in
    match
      Obj.magic
        (let v__target'2924 =
           Obj.magic
             v_work'2227
             v_queue'2237
         in
         if
           Obj.magic
             ((<) : int -> int -> bool)
             (Obj.magic
                Boot.Intrinsics.Mseq.length
                v__target'2924)
             1
         then
           Option.None
         else
           Obj.magic
             Obj.magic
             (let
                (v__prefix'2925, v__splitTemp'2926)
              =
                Obj.magic
                  Boot.Intrinsics.Mseq.split_at
                  v__target'2924
                  1
              in
              let
                (v__middle'2927, v__postfix'2928)
              =
                Obj.magic
                  Boot.Intrinsics.Mseq.split_at
                  v__splitTemp'2926
                  (Obj.magic
                     Int.sub
                     (Obj.magic
                        Boot.Intrinsics.Mseq.length
                        v__splitTemp'2926)
                     0)
              in
              let v__seqElem'2929 =
                Obj.magic
                  Boot.Intrinsics.Mseq.get
                  v__prefix'2925
                  0
              in
              Option.Some (v__target'2924)))
    with
    | Option.Some (v_res'2239) ->
        (CSome'1690 (Obj.repr
            v_res'2239))
    | Option.None ->
        (Obj.magic
           CNone'1691);;
let v_breakableConstructResult =
  fun v_selfToTok'2244 ->
    fun v_lpar'2245 ->
      fun v_rpar'2246 ->
        fun v_elided'2247 ->
          fun v_parInput'2248 ->
            fun v_nodes'2249 ->
              let v_parId'2250 =
                Obj.magic
                  v__opIdI
                  v_parInput'2248
              in
              let rec v_range'2251 =
                  fun v_node'2252 ->
                    let v_defaultCase'2930 =
                      fun nv_ ->
                        failwith
                          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 944:13-944:18 ERROR: Reached a never term, which should be impossible in a well-typed program."
                    in
                    match
                      Obj.magic
                        v_node'2252
                    with
                    | CAtomP'1832 v_x'2931 ->
                        (match
                           Obj.magic
                             (let v__target'2932 =
                                Obj.magic
                                  Obj.magic
                                  v_node'2252
                              in
                              let
                                CRec'2490 ({lself = v_self'2933})
                              =
                                Obj.magic
                                  Obj.magic
                                  v__target'2932
                              in
                              Option.Some (v_self'2933))
                         with
                         | Option.Some (v_self'2253) ->
                             (CRec'2493 { lfirst =
                                  (Obj.repr
                                    v_self'2253);
                                llast =
                                  (Obj.repr
                                    v_self'2253) })
                         | Option.None ->
                             (Obj.magic
                                (Obj.magic
                                   v_defaultCase'2930
                                   ())))
                    | CInfixP'1833 v_x'2934 ->
                        (Obj.magic
                           (match
                              Obj.magic
                                (let v__target'2935 =
                                   Obj.magic
                                     Obj.magic
                                     v_node'2252
                                 in
                                 let
                                   CRec'2461 ({lleftChildAlts = v_leftChildAlts'2936;lrightChildAlts = v_rightChildAlts'2937})
                                 =
                                   Obj.magic
                                     Obj.magic
                                     v__target'2935
                                 in
                                 if
                                   Obj.magic
                                     ((<) : int -> int -> bool)
                                     (Obj.magic
                                        Boot.Intrinsics.Mseq.length
                                        v_leftChildAlts'2936)
                                     1
                                 then
                                   Option.None
                                 else
                                   Obj.magic
                                     Obj.magic
                                     (let
                                        (v__prefix'2938, v__splitTemp'2939)
                                      =
                                        Obj.magic
                                          Boot.Intrinsics.Mseq.split_at
                                          v_leftChildAlts'2936
                                          1
                                      in
                                      let
                                        (v__middle'2940, v__postfix'2941)
                                      =
                                        Obj.magic
                                          Boot.Intrinsics.Mseq.split_at
                                          v__splitTemp'2939
                                          (Obj.magic
                                             Int.sub
                                             (Obj.magic
                                                Boot.Intrinsics.Mseq.length
                                                v__splitTemp'2939)
                                             0)
                                      in
                                      let v__seqElem'2942 =
                                        Obj.magic
                                          Boot.Intrinsics.Mseq.get
                                          v__prefix'2938
                                          0
                                      in
                                      if
                                        Obj.magic
                                          ((<) : int -> int -> bool)
                                          (Obj.magic
                                             Boot.Intrinsics.Mseq.length
                                             v_rightChildAlts'2937)
                                          1
                                      then
                                        Option.None
                                      else
                                        Obj.magic
                                          Obj.magic
                                          (let
                                             (v__prefix'2943, v__splitTemp'2944)
                                           =
                                             Obj.magic
                                               Boot.Intrinsics.Mseq.split_at
                                               v_rightChildAlts'2937
                                               1
                                           in
                                           let
                                             (v__middle'2945, v__postfix'2946)
                                           =
                                             Obj.magic
                                               Boot.Intrinsics.Mseq.split_at
                                               v__splitTemp'2944
                                               (Obj.magic
                                                  Int.sub
                                                  (Obj.magic
                                                     Boot.Intrinsics.Mseq.length
                                                     v__splitTemp'2944)
                                                  0)
                                           in
                                           let v__seqElem'2947 =
                                             Obj.magic
                                               Boot.Intrinsics.Mseq.get
                                               v__prefix'2943
                                               0
                                           in
                                           Option.Some (v__seqElem'2942, v__seqElem'2947))))
                            with
                            | Option.Some (v_l'2254, v_r'2255) ->
                                (CRec'2493 { lfirst =
                                     (Obj.repr
                                       (let
                                          CRec'2493 ({lfirst = v_X'2256})
                                        =
                                          Obj.magic
                                            (Obj.magic
                                               v_range'2251
                                               v_l'2254)
                                        in
                                        Obj.magic
                                          v_X'2256));
                                   llast =
                                     (Obj.repr
                                       (let
                                          CRec'2493 ({llast = v_X'2257})
                                        =
                                          Obj.magic
                                            (Obj.magic
                                               v_range'2251
                                               v_r'2255)
                                        in
                                        Obj.magic
                                          v_X'2257)) })
                            | Option.None ->
                                (Obj.magic
                                   (Obj.magic
                                      v_defaultCase'2930
                                      ()))))
                    | CPrefixP'1834 v_x'2948 ->
                        (Obj.magic
                           (match
                              Obj.magic
                                (let v__target'2949 =
                                   Obj.magic
                                     Obj.magic
                                     v_node'2252
                                 in
                                 let
                                   CRec'2462 ({lself = v_self'2950;lrightChildAlts = v_rightChildAlts'2951})
                                 =
                                   Obj.magic
                                     Obj.magic
                                     v__target'2949
                                 in
                                 if
                                   Obj.magic
                                     ((<) : int -> int -> bool)
                                     (Obj.magic
                                        Boot.Intrinsics.Mseq.length
                                        v_rightChildAlts'2951)
                                     1
                                 then
                                   Option.None
                                 else
                                   Obj.magic
                                     Obj.magic
                                     (let
                                        (v__prefix'2952, v__splitTemp'2953)
                                      =
                                        Obj.magic
                                          Boot.Intrinsics.Mseq.split_at
                                          v_rightChildAlts'2951
                                          1
                                      in
                                      let
                                        (v__middle'2954, v__postfix'2955)
                                      =
                                        Obj.magic
                                          Boot.Intrinsics.Mseq.split_at
                                          v__splitTemp'2953
                                          (Obj.magic
                                             Int.sub
                                             (Obj.magic
                                                Boot.Intrinsics.Mseq.length
                                                v__splitTemp'2953)
                                             0)
                                      in
                                      let v__seqElem'2956 =
                                        Obj.magic
                                          Boot.Intrinsics.Mseq.get
                                          v__prefix'2952
                                          0
                                      in
                                      Option.Some (v_self'2950, v__seqElem'2956)))
                            with
                            | Option.Some (v_self'2258, v_r'2259) ->
                                (CRec'2493 { lfirst =
                                     (Obj.repr
                                       v_self'2258);
                                   llast =
                                     (Obj.repr
                                       (let
                                          CRec'2493 ({llast = v_X'2260})
                                        =
                                          Obj.magic
                                            (Obj.magic
                                               v_range'2251
                                               v_r'2259)
                                        in
                                        Obj.magic
                                          v_X'2260)) })
                            | Option.None ->
                                (Obj.magic
                                   (Obj.magic
                                      v_defaultCase'2930
                                      ()))))
                    | CPostfixP'1835 v_x'2957 ->
                        (Obj.magic
                           (match
                              Obj.magic
                                (let v__target'2958 =
                                   Obj.magic
                                     Obj.magic
                                     v_node'2252
                                 in
                                 let
                                   CRec'2482 ({lself = v_self'2959;lleftChildAlts = v_leftChildAlts'2960})
                                 =
                                   Obj.magic
                                     Obj.magic
                                     v__target'2958
                                 in
                                 if
                                   Obj.magic
                                     ((<) : int -> int -> bool)
                                     (Obj.magic
                                        Boot.Intrinsics.Mseq.length
                                        v_leftChildAlts'2960)
                                     1
                                 then
                                   Option.None
                                 else
                                   Obj.magic
                                     Obj.magic
                                     (let
                                        (v__prefix'2961, v__splitTemp'2962)
                                      =
                                        Obj.magic
                                          Boot.Intrinsics.Mseq.split_at
                                          v_leftChildAlts'2960
                                          1
                                      in
                                      let
                                        (v__middle'2963, v__postfix'2964)
                                      =
                                        Obj.magic
                                          Boot.Intrinsics.Mseq.split_at
                                          v__splitTemp'2962
                                          (Obj.magic
                                             Int.sub
                                             (Obj.magic
                                                Boot.Intrinsics.Mseq.length
                                                v__splitTemp'2962)
                                             0)
                                      in
                                      let v__seqElem'2965 =
                                        Obj.magic
                                          Boot.Intrinsics.Mseq.get
                                          v__prefix'2961
                                          0
                                      in
                                      Option.Some (v_self'2959, v__seqElem'2965)))
                            with
                            | Option.Some (v_self'2261, v_l'2262) ->
                                (CRec'2493 { lfirst =
                                     (Obj.repr
                                       (let
                                          CRec'2493 ({lfirst = v_X'2263})
                                        =
                                          Obj.magic
                                            (Obj.magic
                                               v_range'2251
                                               v_l'2262)
                                        in
                                        Obj.magic
                                          v_X'2263));
                                   llast =
                                     (Obj.repr
                                       v_self'2261) })
                            | Option.None ->
                                (Obj.magic
                                   (Obj.magic
                                      v_defaultCase'2930
                                      ()))))
                    | _ ->
                        (Obj.magic
                           (v_defaultCase'2930
                              ()))
              in let rec v_flattenOne'2264 =
                  fun v_node'2266 ->
                    let v_X'2267 =
                      v_node'2266
                    in
                    let v_defaultCase'2966 =
                      fun nv_ ->
                        failwith
                          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 957:8-957:11 ERROR: Reached a never term, which should be impossible in a well-typed program."
                    in
                    match
                      Obj.magic
                        v_X'2267
                    with
                    | CAtomP'1832 v_x'2967 ->
                        (match
                           Obj.magic
                             (let v__target'2968 =
                                Obj.magic
                                  Obj.magic
                                  v_X'2267
                              in
                              let
                                CRec'2490 ({lself = v_self'2969})
                              =
                                Obj.magic
                                  Obj.magic
                                  v__target'2968
                              in
                              Option.Some (v_self'2969))
                         with
                         | Option.Some (v_self'2268) ->
                             (Obj.magic
                                Boot.Intrinsics.Mseq.Helpers.of_array
                                [| (Obj.magic
                                    (Obj.magic
                                       v_selfToTok'2244
                                       v_self'2268)) |])
                         | Option.None ->
                             (Obj.magic
                                (Obj.magic
                                   v_defaultCase'2966
                                   ())))
                    | CInfixP'1833 v_x'2970 ->
                        (Obj.magic
                           (let v_p'2269 =
                              Obj.magic
                                Obj.magic
                                v_X'2267
                            in
                            Obj.magic
                              v_join
                              (Obj.magic
                                 Boot.Intrinsics.Mseq.Helpers.of_array
                                 [| (Obj.magic
                                     (Obj.magic
                                        v_flattenMany'2265
                                        (let
                                           CRec'2461 ({lleftChildAlts = v_X'2270})
                                         =
                                           Obj.magic
                                             v_p'2269
                                         in
                                         Obj.magic
                                           v_X'2270)));
                                   (Obj.magic
                                     (Obj.magic
                                        Boot.Intrinsics.Mseq.Helpers.of_array
                                        [| (Obj.magic
                                            (Obj.magic
                                               v_selfToTok'2244
                                               (let
                                                  CRec'2461 ({lself = v_X'2271})
                                                =
                                                  Obj.magic
                                                    v_p'2269
                                                in
                                                Obj.magic
                                                  v_X'2271))) |]));
                                   (Obj.magic
                                     (Obj.magic
                                        v_flattenMany'2265
                                        (let
                                           CRec'2461 ({lrightChildAlts = v_X'2272})
                                         =
                                           Obj.magic
                                             v_p'2269
                                         in
                                         Obj.magic
                                           v_X'2272))) |])))
                    | CPrefixP'1834 v_x'2971 ->
                        (Obj.magic
                           (let v_p'2273 =
                              Obj.magic
                                Obj.magic
                                v_X'2267
                            in
                            Obj.magic
                              Boot.Intrinsics.Mseq.cons
                              (Obj.magic
                                 v_selfToTok'2244
                                 (let
                                    CRec'2462 ({lself = v_X'2274})
                                  =
                                    Obj.magic
                                      v_p'2273
                                  in
                                  Obj.magic
                                    v_X'2274))
                              (Obj.magic
                                 v_flattenMany'2265
                                 (let
                                    CRec'2462 ({lrightChildAlts = v_X'2275})
                                  =
                                    Obj.magic
                                      v_p'2273
                                  in
                                  Obj.magic
                                    v_X'2275))))
                    | CPostfixP'1835 v_x'2972 ->
                        (Obj.magic
                           (let v_p'2276 =
                              Obj.magic
                                Obj.magic
                                v_X'2267
                            in
                            Obj.magic
                              Boot.Intrinsics.Mseq.snoc
                              (Obj.magic
                                 v_flattenMany'2265
                                 (let
                                    CRec'2482 ({lleftChildAlts = v_X'2277})
                                  =
                                    Obj.magic
                                      v_p'2276
                                  in
                                  Obj.magic
                                    v_X'2277))
                              (Obj.magic
                                 v_selfToTok'2244
                                 (let
                                    CRec'2482 ({lself = v_X'2278})
                                  =
                                    Obj.magic
                                      v_p'2276
                                  in
                                  Obj.magic
                                    v_X'2278))))
                    | _ ->
                        (Obj.magic
                           (v_defaultCase'2966
                              ()))
              and v_flattenMany'2265 =
                  fun v_nodes'2279 ->
                    match
                      Obj.magic
                        (let v__target'2973 =
                           v_nodes'2279
                         in
                         if
                           Obj.magic
                             ((<) : int -> int -> bool)
                             (Obj.magic
                                Boot.Intrinsics.Mseq.length
                                v__target'2973)
                             1
                         then
                           Option.None
                         else
                           Obj.magic
                             Obj.magic
                             (let
                                (v__prefix'2974, v__splitTemp'2975)
                              =
                                Obj.magic
                                  Boot.Intrinsics.Mseq.split_at
                                  v__target'2973
                                  1
                              in
                              let
                                (v__middle'2976, v__postfix'2977)
                              =
                                Obj.magic
                                  Boot.Intrinsics.Mseq.split_at
                                  v__splitTemp'2975
                                  (Obj.magic
                                     Int.sub
                                     (Obj.magic
                                        Boot.Intrinsics.Mseq.length
                                        v__splitTemp'2975)
                                     0)
                              in
                              let v__seqElem'2978 =
                                Obj.magic
                                  Boot.Intrinsics.Mseq.get
                                  v__prefix'2974
                                  0
                              in
                              Option.Some (v__seqElem'2978)))
                    with
                    | Option.Some (v_n'2280) ->
                        (Obj.magic
                           v_flattenOne'2264
                           v_n'2280)
                    | Option.None ->
                        (Obj.magic
                           (failwith
                              "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 961:13-961:18 ERROR: Reached a never term, which should be impossible in a well-typed program."))
              in let rec v_resolveTopOne'2281 =
                  fun v_topIdxs'2283 ->
                    fun v_p'2284 ->
                      let v_idx'2285 =
                        Obj.magic
                          v__opIdxP
                          v_p'2284
                      in
                      let v_l'2288 =
                        match
                          Obj.magic
                            (let v__target'2979 =
                               Obj.magic
                                 v__leftStuffP
                                 v_p'2284
                             in
                             match
                               Obj.magic
                                 Obj.magic
                                 v__target'2979
                             with
                             | CSome'1690 v__n'2980 ->
                                 (let
                                    CRec'2499 ({l0 = v_0'2981;l1 = v_1'2982})
                                  =
                                    Obj.magic
                                      Obj.magic
                                      v__n'2980
                                  in
                                  Option.Some (v_0'2981, v_1'2982))
                             | _ ->
                                 (Obj.magic
                                    Obj.magic
                                    (Option.None)))
                        with
                        | Option.Some (v_children'2286, v_allows'2287) ->
                            (Obj.magic
                               v_resolveTopMany'2282
                               (Obj.magic
                                  v_filter
                                  (Obj.magic
                                     ((>) : int -> int -> bool)
                                     v_idx'2285)
                                  v_topIdxs'2283)
                               (Obj.magic
                                  v__isWhitelist
                                  v_allows'2287)
                               v_children'2286)
                        | Option.None ->
                            (Obj.magic
                               (Obj.magic
                                  Boot.Intrinsics.Mseq.Helpers.of_array
                                  [| (Obj.magic
                                      (Obj.magic
                                         Boot.Intrinsics.Mseq.Helpers.of_array
                                         [|  |])) |]))
                      in
                      let v_r'2291 =
                        match
                          Obj.magic
                            (let v__target'2983 =
                               Obj.magic
                                 v__rightStuffP
                                 v_p'2284
                             in
                             match
                               Obj.magic
                                 Obj.magic
                                 v__target'2983
                             with
                             | CSome'1690 v__n'2984 ->
                                 (let
                                    CRec'2499 ({l0 = v_0'2985;l1 = v_1'2986})
                                  =
                                    Obj.magic
                                      Obj.magic
                                      v__n'2984
                                  in
                                  Option.Some (v_0'2985, v_1'2986))
                             | _ ->
                                 (Obj.magic
                                    Obj.magic
                                    (Option.None)))
                        with
                        | Option.Some (v_children'2289, v_allows'2290) ->
                            (Obj.magic
                               v_resolveTopMany'2282
                               (Obj.magic
                                  v_filter
                                  (Obj.magic
                                     ((<) : int -> int -> bool)
                                     v_idx'2285)
                                  v_topIdxs'2283)
                               (Obj.magic
                                  v__isWhitelist
                                  v_allows'2290)
                               v_children'2289)
                        | Option.None ->
                            (Obj.magic
                               (Obj.magic
                                  Boot.Intrinsics.Mseq.Helpers.of_array
                                  [| (Obj.magic
                                      (Obj.magic
                                         Boot.Intrinsics.Mseq.Helpers.of_array
                                         [|  |])) |]))
                      in
                      let v_here'2292 =
                        Obj.magic
                          Boot.Intrinsics.Mseq.Helpers.of_array
                          [| (Obj.magic
                              (Obj.magic
                                 v_selfToTok'2244
                                 (Obj.magic
                                    v__selfP
                                    v_p'2284))) |]
                      in
                      Obj.magic
                        v_seqLiftA2
                        (fun v_l'2293 ->
                           fun v_r'2294 ->
                             Obj.magic
                               v_join
                               (Obj.magic
                                  Boot.Intrinsics.Mseq.Helpers.of_array
                                  [| (Obj.magic
                                      v_l'2293);
                                    (Obj.magic
                                      v_here'2292);
                                    (Obj.magic
                                      v_r'2294) |]))
                        v_l'2288
                        v_r'2291
              and v_resolveTopMany'2282 =
                  fun v_topIdxs'2295 ->
                    fun v_isWhitelist'2296 ->
                      fun v_ps'2297 ->
                        match
                          Obj.magic
                            (let v__target'2987 =
                               Obj.magic
                                 v_partition
                                 (Obj.magic
                                    v__isBrokenEdge
                                    v_isWhitelist'2296)
                                 v_ps'2297
                             in
                             let
                               CRec'2499 ({l0 = v_0'2988;l1 = v_1'2989})
                             =
                               Obj.magic
                                 Obj.magic
                                 v__target'2987
                             in
                             Option.Some (v_0'2988, v_1'2989))
                        with
                        | Option.Some (v_broken'2298, v_whole'2299) ->
                            (let v_broken'2300 =
                               Obj.magic
                                 v_join
                                 (Obj.magic
                                    Boot.Intrinsics.Mseq.map
                                    (Obj.magic
                                       v_resolveTopOne'2281
                                       v_topIdxs'2295)
                                    v_broken'2298)
                             in
                             let v_whole'2302 =
                               if
                                 Obj.magic
                                   (Obj.magic
                                      Boot.Intrinsics.Mseq.null
                                      v_whole'2299)
                               then
                                 Obj.magic
                                   Boot.Intrinsics.Mseq.Helpers.of_array
                                   [|  |]
                               else
                                 Obj.magic
                                   (let v_flattened'2301 =
                                      Obj.magic
                                        v_flattenMany'2265
                                        v_whole'2299
                                    in
                                    if
                                      Obj.magic
                                        (Obj.magic
                                           Boot.Intrinsics.Mseq.null
                                           v_topIdxs'2295)
                                    then
                                      Obj.magic
                                        Boot.Intrinsics.Mseq.Helpers.of_array
                                        [| (Obj.magic
                                            v_flattened'2301) |]
                                    else
                                      Obj.magic
                                        (Obj.magic
                                           Boot.Intrinsics.Mseq.Helpers.of_array
                                           [| (Obj.magic
                                               (Obj.magic
                                                  Boot.Intrinsics.Mseq.snoc
                                                  (Obj.magic
                                                     Boot.Intrinsics.Mseq.cons
                                                     v_lpar'2245
                                                     v_flattened'2301)
                                                  v_rpar'2246)) |]))
                             in
                             Obj.magic
                               Boot.Intrinsics.Mseq.concat
                               v_broken'2300
                               v_whole'2302)
                        | Option.None ->
                            (Obj.magic
                               (failwith
                                  "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 986:15-986:20 ERROR: Reached a never term, which should be impossible in a well-typed program."))
              in let v_ambiguities'2303 =
                Obj.magic
                  ref
                  (Obj.magic
                     Boot.Intrinsics.Mseq.Helpers.of_array
                     [|  |])
              in
              let rec v_workMany'2304 =
                  fun v_brokenParent'2306 ->
                    fun v_isWhitelist'2307 ->
                      fun v_tops'2308 ->
                        match
                          Obj.magic
                            (let v__target'2990 =
                               v_tops'2308
                             in
                             if
                               Obj.magic
                                 Int.equal
                                 (Obj.magic
                                    Boot.Intrinsics.Mseq.length
                                    v__target'2990)
                                 1
                             then
                               let v__seqElem'2991 =
                                 Obj.magic
                                   Boot.Intrinsics.Mseq.get
                                   v__target'2990
                                   0
                               in
                               Option.Some (v__seqElem'2991)
                             else
                               Obj.magic
                                 Obj.magic
                                 (Option.None))
                        with
                        | Option.Some (v_n'2309) ->
                            (Obj.magic
                               v_workOne'2305
                               (if
                                  Obj.magic
                                    (Obj.magic
                                       v__isBrokenEdge
                                       v_isWhitelist'2307
                                       v_n'2309)
                                then
                                  CSome'1690 (Obj.repr
                                     v_brokenParent'2306)
                                else
                                  Obj.magic
                                    CNone'1691)
                               v_n'2309)
                        | Option.None ->
                            (Obj.magic
                               (match
                                  Obj.magic
                                    (let v__target'2992 =
                                       v_tops'2308
                                     in
                                     if
                                       Obj.magic
                                         ((<) : int -> int -> bool)
                                         (Obj.magic
                                            Boot.Intrinsics.Mseq.length
                                            v__target'2992)
                                         1
                                     then
                                       Option.None
                                     else
                                       Obj.magic
                                         Obj.magic
                                         (let
                                            (v__prefix'2993, v__splitTemp'2994)
                                          =
                                            Obj.magic
                                              Boot.Intrinsics.Mseq.split_at
                                              v__target'2992
                                              1
                                          in
                                          let
                                            (v__middle'2995, v__postfix'2996)
                                          =
                                            Obj.magic
                                              Boot.Intrinsics.Mseq.split_at
                                              v__splitTemp'2994
                                              (Obj.magic
                                                 Int.sub
                                                 (Obj.magic
                                                    Boot.Intrinsics.Mseq.length
                                                    v__splitTemp'2994)
                                                 0)
                                          in
                                          let v__seqElem'2997 =
                                            Obj.magic
                                              Boot.Intrinsics.Mseq.get
                                              v__prefix'2993
                                              0
                                          in
                                          Option.Some (v__seqElem'2997)))
                                with
                                | Option.Some (v_n'2310) ->
                                    (let v_x'2312 =
                                       match
                                         Obj.magic
                                           (let v__target'2998 =
                                              CRec'2499 { l0 =
                                                  (Obj.repr
                                                    (Obj.magic
                                                       v_any
                                                       (Obj.magic
                                                          v__isBrokenEdge
                                                          v_isWhitelist'2307)
                                                       v_tops'2308));
                                                l1 =
                                                  (Obj.repr
                                                    v_brokenParent'2306) }
                                            in
                                            let
                                              CRec'2499 ({l0 = v_0'2999;l1 = v_1'3000})
                                            =
                                              Obj.magic
                                                Obj.magic
                                                v__target'2998
                                            in
                                            if
                                              Obj.magic
                                                Obj.magic
                                                v_0'2999
                                            then
                                              match
                                                Obj.magic
                                                  Obj.magic
                                                  v_1'3000
                                              with
                                              | CSome'1690 v__n'3001 ->
                                                  (Option.Some (v__n'3001))
                                              | _ ->
                                                  (Obj.magic
                                                     Obj.magic
                                                     (Option.None))
                                            else
                                              Obj.magic
                                                Obj.magic
                                                (Option.None))
                                       with
                                       | Option.Some (v_parent'2311) ->
                                           (CRec'2499 { l0 =
                                                (Obj.repr
                                                  (Obj.magic
                                                     Boot.Intrinsics.Mseq.Helpers.of_array
                                                     [| (Obj.magic
                                                         v_parent'2311) |]));
                                              l1 =
                                                (Obj.repr
                                                  (Obj.magic
                                                     v_range'2251
                                                     v_parent'2311)) })
                                       | Option.None ->
                                           (Obj.magic
                                              (CRec'2499 { l0 =
                                                   (Obj.repr
                                                     v_tops'2308);
                                                 l1 =
                                                   (Obj.repr
                                                     (Obj.magic
                                                        v_range'2251
                                                        v_n'2310)) }))
                                     in
                                     let v_tops'2314 =
                                       let
                                         CRec'2499 ({l0 = v_X'2313})
                                       =
                                         Obj.magic
                                           v_x'2312
                                       in
                                       Obj.magic
                                         v_X'2313
                                     in
                                     let v_range'2316 =
                                       let
                                         CRec'2499 ({l1 = v_X'2315})
                                       =
                                         Obj.magic
                                           v_x'2312
                                       in
                                       Obj.magic
                                         v_X'2315
                                     in
                                     let v_topIdxs'2317 =
                                       Obj.magic
                                         v_setOfSeq
                                         Int.sub
                                         (Obj.magic
                                            v_join
                                            (Obj.magic
                                               Boot.Intrinsics.Mseq.map
                                               v__brokenIdxesP
                                               v_tops'2314))
                                     in
                                     let rec v_addChildMaybe'2318 =
                                         fun v_acc'2319 ->
                                           fun v_c'2320 ->
                                             let v_idxs'2321 =
                                               Obj.magic
                                                 v__brokenIdxesP
                                                 v_c'2320
                                             in
                                             let v_acc'2325 =
                                               if
                                                 Obj.magic
                                                   (Obj.magic
                                                      v_any
                                                      (fun v_x'2322 ->
                                                         Obj.magic
                                                           v_setMem
                                                           v_x'2322
                                                           v_topIdxs'2317)
                                                      v_idxs'2321)
                                               then
                                                 Obj.magic
                                                   Boot.Intrinsics.Mseq.Helpers.fold_left
                                                   (fun v_acc'2323 ->
                                                      fun v_x'2324 ->
                                                        Obj.magic
                                                          v_setInsert
                                                          v_x'2324
                                                          v_acc'2323)
                                                   v_acc'2319
                                                   v_idxs'2321
                                               else
                                                 Obj.magic
                                                   v_acc'2319
                                             in
                                             Obj.magic
                                               Boot.Intrinsics.Mseq.Helpers.fold_left
                                               v_addChildMaybe'2318
                                               v_acc'2325
                                               (Obj.magic
                                                  v__brokenChildrenP
                                                  v_c'2320)
                                     in let v_addChildrenMaybe'2328 =
                                       fun v_acc'2326 ->
                                         fun v_top'2327 ->
                                           Obj.magic
                                             Boot.Intrinsics.Mseq.Helpers.fold_left
                                             v_addChildMaybe'2318
                                             v_acc'2326
                                             (Obj.magic
                                                v__brokenChildrenP
                                                v_top'2327)
                                     in
                                     let v_mergeRootIdxs'2329 =
                                       Obj.magic
                                         Boot.Intrinsics.Mseq.Helpers.fold_left
                                         v_addChildrenMaybe'2328
                                         (Obj.magic
                                            v_setEmpty
                                            Int.sub)
                                         v_tops'2314
                                     in
                                     let v_idxesToCover'2330 =
                                       Obj.magic
                                         v_setToSeq
                                         (Obj.magic
                                            v_setUnion
                                            v_mergeRootIdxs'2329
                                            v_topIdxs'2317)
                                     in
                                     let v_resolutions'2331 =
                                       Obj.magic
                                         v_resolveTopMany'2282
                                         v_idxesToCover'2330
                                         true
                                         v_tops'2314
                                     in
                                     let v_err'2334 =
                                       CRec'2492 { lfirst =
                                           (Obj.repr
                                             (let
                                                CRec'2493 ({lfirst = v_X'2332})
                                              =
                                                Obj.magic
                                                  v_range'2316
                                              in
                                              Obj.magic
                                                v_X'2332));
                                         llast =
                                           (Obj.repr
                                             (let
                                                CRec'2493 ({llast = v_X'2333})
                                              =
                                                Obj.magic
                                                  v_range'2316
                                              in
                                              Obj.magic
                                                v_X'2333));
                                         lpartialResolutions =
                                           (Obj.repr
                                             v_resolutions'2331) }
                                     in
                                     let v_'2335 =
                                       Obj.magic
                                         (:=)
                                         v_ambiguities'2303
                                         (Obj.magic
                                            Boot.Intrinsics.Mseq.cons
                                            v_err'2334
                                            (Obj.magic
                                               (!)
                                               v_ambiguities'2303))
                                     in
                                     CNone'1691)
                                | Option.None ->
                                    (Obj.magic
                                       (let v_'2336 =
                                          Obj.magic
                                            v_dprintLn
                                            v_tops'2308
                                        in
                                        failwith
                                          "FILE \"/home/vipa/.local/lib/mcore/stdlib/parser/breakable.mc\" 1053:30-1053:35 ERROR: Reached a never term, which should be impossible in a well-typed program."))))
              and v_workOne'2305 =
                  fun v_brokenParent'2337 ->
                    fun v_node'2338 ->
                      let v_l'2341 =
                        match
                          Obj.magic
                            (let v__target'3002 =
                               Obj.magic
                                 v__leftStuffP
                                 v_node'2338
                             in
                             match
                               Obj.magic
                                 Obj.magic
                                 v__target'3002
                             with
                             | CSome'1690 v__n'3003 ->
                                 (let
                                    CRec'2499 ({l0 = v_0'3004;l1 = v_1'3005})
                                  =
                                    Obj.magic
                                      Obj.magic
                                      v__n'3003
                                  in
                                  Option.Some (v_0'3004, v_1'3005))
                             | _ ->
                                 (Obj.magic
                                    Obj.magic
                                    (Option.None)))
                        with
                        | Option.Some (v_children'2339, v_allows'2340) ->
                            (Obj.magic
                               v_workMany'2304
                               (Obj.magic
                                  v_optionOr
                                  v_brokenParent'2337
                                  (CSome'1690 (Obj.repr
                                      v_node'2338)))
                               (Obj.magic
                                  v__isWhitelist
                                  v_allows'2340)
                               v_children'2339)
                        | Option.None ->
                            (Obj.magic
                               CNone'1691)
                      in
                      let v_r'2344 =
                        match
                          Obj.magic
                            (let v__target'3006 =
                               Obj.magic
                                 v__rightStuffP
                                 v_node'2338
                             in
                             match
                               Obj.magic
                                 Obj.magic
                                 v__target'3006
                             with
                             | CSome'1690 v__n'3007 ->
                                 (let
                                    CRec'2499 ({l0 = v_0'3008;l1 = v_1'3009})
                                  =
                                    Obj.magic
                                      Obj.magic
                                      v__n'3007
                                  in
                                  Option.Some (v_0'3008, v_1'3009))
                             | _ ->
                                 (Obj.magic
                                    Obj.magic
                                    (Option.None)))
                        with
                        | Option.Some (v_children'2342, v_allows'2343) ->
                            (Obj.magic
                               v_workMany'2304
                               (Obj.magic
                                  v_optionOr
                                  v_brokenParent'2337
                                  (CSome'1690 (Obj.repr
                                      v_node'2338)))
                               (Obj.magic
                                  v__isWhitelist
                                  v_allows'2343)
                               v_children'2342)
                        | Option.None ->
                            (Obj.magic
                               CNone'1691)
                      in
                      let v_X'2345 =
                        CRec'2497 { l0 =
                            (Obj.repr
                              v_node'2338);
                          l1 =
                            (Obj.repr
                              v_l'2341);
                          l2 =
                            (Obj.repr
                              v_r'2344) }
                      in
                      match
                        Obj.magic
                          (let v__target'3010 =
                             v_X'2345
                           in
                           let
                             CRec'2497 ({l0 = v_0'3011;l1 = v_1'3012;l2 = v_2'3013})
                           =
                             Obj.magic
                               Obj.magic
                               v__target'3010
                           in
                           match
                             Obj.magic
                               Obj.magic
                               v_0'3011
                           with
                           | CAtomP'1832 v__n'3014 ->
                               (let
                                  CRec'2490 ({linput = v_input'3015;lself = v_self'3016})
                                =
                                  Obj.magic
                                    Obj.magic
                                    v_0'3011
                                in
                                match
                                  Obj.magic
                                    Obj.magic
                                    v_input'3015
                                with
                                | CAtomI'1826 v__n'3017 ->
                                    (let
                                       CRec'2473 ({lconstruct = v_construct'3018})
                                     =
                                       Obj.magic
                                         Obj.magic
                                         v_input'3015
                                     in
                                     Option.Some (v_construct'3018, v_self'3016))
                                | _ ->
                                    (Obj.magic
                                       Obj.magic
                                       (Option.None)))
                           | _ ->
                               (Obj.magic
                                  Obj.magic
                                  (Option.None)))
                      with
                      | Option.Some (v_c'2346, v_self'2347) ->
                          (CSome'1690 (Obj.repr
                              (Obj.magic
                                 v_c'2346
                                 v_self'2347)))
                      | Option.None ->
                          (Obj.magic
                             (match
                                Obj.magic
                                  (let v__target'3019 =
                                     v_X'2345
                                   in
                                   let
                                     CRec'2497 ({l0 = v_0'3020;l1 = v_1'3021;l2 = v_2'3022})
                                   =
                                     Obj.magic
                                       Obj.magic
                                       v__target'3019
                                   in
                                   match
                                     Obj.magic
                                       Obj.magic
                                       v_0'3020
                                   with
                                   | CPrefixP'1834 v__n'3023 ->
                                       (let
                                          CRec'2462 ({linput = v_input'3024;lself = v_self'3025})
                                        =
                                          Obj.magic
                                            Obj.magic
                                            v_0'3020
                                        in
                                        match
                                          Obj.magic
                                            Obj.magic
                                            v_input'3024
                                        with
                                        | CPrefixI'1828 v__n'3026 ->
                                            (let
                                               CRec'2475 ({lconstruct = v_construct'3027})
                                             =
                                               Obj.magic
                                                 Obj.magic
                                                 v_input'3024
                                             in
                                             match
                                               Obj.magic
                                                 Obj.magic
                                                 v_2'3022
                                             with
                                             | CSome'1690 v__n'3028 ->
                                                 (Option.Some (v_construct'3027, v_self'3025, v__n'3028))
                                             | _ ->
                                                 (Obj.magic
                                                    Obj.magic
                                                    (Option.None)))
                                        | _ ->
                                            (Obj.magic
                                               Obj.magic
                                               (Option.None)))
                                   | _ ->
                                       (Obj.magic
                                          Obj.magic
                                          (Option.None)))
                              with
                              | Option.Some (v_c'2348, v_self'2349, v_r'2350) ->
                                  (CSome'1690 (Obj.repr
                                      (Obj.magic
                                         v_c'2348
                                         v_self'2349
                                         v_r'2350)))
                              | Option.None ->
                                  (Obj.magic
                                     (match
                                        Obj.magic
                                          (let v__target'3029 =
                                             v_X'2345
                                           in
                                           let
                                             CRec'2497 ({l0 = v_0'3030;l1 = v_1'3031;l2 = v_2'3032})
                                           =
                                             Obj.magic
                                               Obj.magic
                                               v__target'3029
                                           in
                                           match
                                             Obj.magic
                                               Obj.magic
                                               v_0'3030
                                           with
                                           | CPostfixP'1835 v__n'3033 ->
                                               (let
                                                  CRec'2482 ({linput = v_input'3034;lself = v_self'3035})
                                                =
                                                  Obj.magic
                                                    Obj.magic
                                                    v_0'3030
                                                in
                                                match
                                                  Obj.magic
                                                    Obj.magic
                                                    v_input'3034
                                                with
                                                | CPostfixI'1829 v__n'3036 ->
                                                    (let
                                                       CRec'2477 ({lconstruct = v_construct'3037})
                                                     =
                                                       Obj.magic
                                                         Obj.magic
                                                         v_input'3034
                                                     in
                                                     match
                                                       Obj.magic
                                                         Obj.magic
                                                         v_1'3031
                                                     with
                                                     | CSome'1690 v__n'3038 ->
                                                         (Option.Some (v_construct'3037, v_self'3035, v__n'3038))
                                                     | _ ->
                                                         (Obj.magic
                                                            Obj.magic
                                                            (Option.None)))
                                                | _ ->
                                                    (Obj.magic
                                                       Obj.magic
                                                       (Option.None)))
                                           | _ ->
                                               (Obj.magic
                                                  Obj.magic
                                                  (Option.None)))
                                      with
                                      | Option.Some (v_c'2351, v_self'2352, v_l'2353) ->
                                          (CSome'1690 (Obj.repr
                                              (Obj.magic
                                                 v_c'2351
                                                 v_self'2352
                                                 v_l'2353)))
                                      | Option.None ->
                                          (Obj.magic
                                             (match
                                                Obj.magic
                                                  (let v__target'3039 =
                                                     v_X'2345
                                                   in
                                                   let
                                                     CRec'2497 ({l0 = v_0'3040;l1 = v_1'3041;l2 = v_2'3042})
                                                   =
                                                     Obj.magic
                                                       Obj.magic
                                                       v__target'3039
                                                   in
                                                   match
                                                     Obj.magic
                                                       Obj.magic
                                                       v_0'3040
                                                   with
                                                   | CInfixP'1833 v__n'3043 ->
                                                       (let
                                                          CRec'2461 ({linput = v_input'3044;lself = v_self'3045})
                                                        =
                                                          Obj.magic
                                                            Obj.magic
                                                            v_0'3040
                                                        in
                                                        match
                                                          Obj.magic
                                                            Obj.magic
                                                            v_input'3044
                                                        with
                                                        | CInfixI'1827 v__n'3046 ->
                                                            (let
                                                               CRec'2476 ({lconstruct = v_construct'3047})
                                                             =
                                                               Obj.magic
                                                                 Obj.magic
                                                                 v_input'3044
                                                             in
                                                             match
                                                               Obj.magic
                                                                 Obj.magic
                                                                 v_1'3041
                                                             with
                                                             | CSome'1690 v__n'3048 ->
                                                                 (match
                                                                    Obj.magic
                                                                      Obj.magic
                                                                      v_2'3042
                                                                  with
                                                                  | CSome'1690 v__n'3049 ->
                                                                      (Option.Some (v_construct'3047, v_self'3045, v__n'3048, v__n'3049))
                                                                  | _ ->
                                                                      (Obj.magic
                                                                         Obj.magic
                                                                         (Option.None)))
                                                             | _ ->
                                                                 (Obj.magic
                                                                    Obj.magic
                                                                    (Option.None)))
                                                        | _ ->
                                                            (Obj.magic
                                                               Obj.magic
                                                               (Option.None)))
                                                   | _ ->
                                                       (Obj.magic
                                                          Obj.magic
                                                          (Option.None)))
                                              with
                                              | Option.Some (v_c'2354, v_self'2355, v_l'2356, v_r'2357) ->
                                                  (CSome'1690 (Obj.repr
                                                      (Obj.magic
                                                         v_c'2354
                                                         v_self'2355
                                                         v_l'2356
                                                         v_r'2357)))
                                              | Option.None ->
                                                  (Obj.magic
                                                     CNone'1691)))))))
              in match
                Obj.magic
                  (let v__target'3050 =
                     Obj.magic
                       v_workMany'2304
                       CNone'1691
                       false
                       v_nodes'2249
                   in
                   match
                     Obj.magic
                       Obj.magic
                       v__target'3050
                   with
                   | CSome'1690 v__n'3051 ->
                       (Option.Some (v__n'3051))
                   | _ ->
                       (Obj.magic
                          Obj.magic
                          (Option.None)))
              with
              | Option.Some (v_res'2358) ->
                  (CRight'1800 (Obj.repr
                      v_res'2358))
              | Option.None ->
                  (Obj.magic
                     (CLeft'1799 (Obj.repr
                         (CAmbiguities'2243 (Obj.repr
                             (Obj.magic
                                (!)
                                v_ambiguities'2303))))));;
let v_allowAll =
  fun v_cmp'2360 ->
    CDisallowSet'1809 (Obj.repr
       (Obj.magic
          Boot.Intrinsics.Mmap.empty
          v_cmp'2360));;
let v_allowNone =
  fun v_cmp'2362 ->
    CAllowSet'1808 (Obj.repr
       (Obj.magic
          Boot.Intrinsics.Mmap.empty
          v_cmp'2362));;
let v_allowOneMore =
  fun v_label'2364 ->
    fun v_set'2365 ->
      Obj.magic
        v_breakableInsertAllowSet
        v_label'2364
        v_set'2365;;
let v_allowOneLess =
  fun v_label'2367 ->
    fun v_set'2368 ->
      Obj.magic
        v_breakableRemoveAllowSet
        v_label'2367
        v_set'2368;;
let v_atom =
  fun v_label'2370 ->
    fun v_construct'2371 ->
      CBreakableAtom'1813 { llabel =
          (Obj.repr
            v_label'2370);
        lconstruct =
          (Obj.repr
            v_construct'2371) };;
let v_prefix =
  fun v_label'2373 ->
    fun v_construct'2374 ->
      fun v_rightAllow'2375 ->
        CBreakablePrefix'1815 { llabel =
            (Obj.repr
              v_label'2373);
          lconstruct =
            (Obj.repr
              v_construct'2374);
          lrightAllow =
            (Obj.repr
              v_rightAllow'2375) };;
let v_postfix =
  fun v_label'2377 ->
    fun v_construct'2378 ->
      fun v_leftAllow'2379 ->
        CBreakablePostfix'1816 { llabel =
            (Obj.repr
              v_label'2377);
          lconstruct =
            (Obj.repr
              v_construct'2378);
          lleftAllow =
            (Obj.repr
              v_leftAllow'2379) };;
let v_infix =
  fun v_label'2381 ->
    fun v_construct'2382 ->
      fun v_leftAllow'2383 ->
        fun v_rightAllow'2384 ->
          CBreakableInfix'1814 { llabel =
              (Obj.repr
                v_label'2381);
            lconstruct =
              (Obj.repr
                v_construct'2382);
            lleftAllow =
              (Obj.repr
                v_leftAllow'2383);
            lrightAllow =
              (Obj.repr
                v_rightAllow'2384) };;
let v_emptyGrammar =
  fun v_topAllowed'2386 ->
    CRec'2498 { lproductions =
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
          v_topAllowed'2386) };;
let v_addProd =
  fun v_prod'2388 ->
    fun v_gram'2389 ->
      let
        CRec'2498 v_rec'3052
      =
        Obj.magic
          v_gram'2389
      in
      CRec'2498 { v_rec'3052
        with
        lproductions =
          Obj.repr
            (Obj.magic
               Boot.Intrinsics.Mseq.snoc
               (let
                  CRec'2498 ({lproductions = v_X'2390})
                =
                  Obj.magic
                    v_gram'2389
                in
                Obj.magic
                  v_X'2390)
               v_prod'2388) };;
let v_addPrec =
  fun v_l'2392 ->
    fun v_r'2393 ->
      fun v_mayL'2394 ->
        fun v_mayR'2395 ->
          fun v_gram'2396 ->
            let
              CRec'2498 v_rec'3053
            =
              Obj.magic
                v_gram'2396
            in
            CRec'2498 { v_rec'3053
              with
              lprecedences =
                Obj.repr
                  (Obj.magic
                     Boot.Intrinsics.Mseq.snoc
                     (let
                        CRec'2498 ({lprecedences = v_X'2397})
                      =
                        Obj.magic
                          v_gram'2396
                      in
                      Obj.magic
                        v_X'2397)
                     (CRec'2499 { l0 =
                          (Obj.repr
                            (CRec'2499 { l0 =
                                 (Obj.repr
                                   v_l'2392);
                               l1 =
                                 (Obj.repr
                                   v_r'2393) }));
                        l1 =
                          (Obj.repr
                            (CRec'2452 { lmayGroupLeft =
                                 (Obj.repr
                                   v_mayL'2394);
                               lmayGroupRight =
                                 (Obj.repr
                                   v_mayR'2395) })) })) };;
let v_finalize =
  v_breakableGenGrammar;;
let v_getAtom =
  fun v_gram'2400 ->
    fun v_label'2401 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find
        v_label'2401
        (let
           CRec'2459 ({latoms = v_X'2402})
         =
           Obj.magic
             v_gram'2400
         in
         Obj.magic
           v_X'2402);;
let v_getPrefix =
  fun v_gram'2404 ->
    fun v_label'2405 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find
        v_label'2405
        (let
           CRec'2459 ({lprefixes = v_X'2406})
         =
           Obj.magic
             v_gram'2404
         in
         Obj.magic
           v_X'2406);;
let v_getPostfix =
  fun v_gram'2408 ->
    fun v_label'2409 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find
        v_label'2409
        (let
           CRec'2459 ({lpostfixes = v_X'2410})
         =
           Obj.magic
             v_gram'2408
         in
         Obj.magic
           v_X'2410);;
let v_getInfix =
  fun v_gram'2412 ->
    fun v_label'2413 ->
      Obj.magic
        Boot.Intrinsics.Mmap.find
        v_label'2413
        (let
           CRec'2459 ({linfixes = v_X'2414})
         =
           Obj.magic
             v_gram'2412
         in
         Obj.magic
           v_X'2414);;
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
  fun v_none'2422 ->
    fun v_some'2423 ->
      fun v_opt'2424 ->
        match
          Obj.magic
            (let v__target'3054 =
               v_opt'2424
             in
             match
               Obj.magic
                 Obj.magic
                 v__target'3054
             with
             | CSome'1690 v__n'3055 ->
                 (Option.Some (v__n'3055))
             | _ ->
                 (Obj.magic
                    Obj.magic
                    (Option.None)))
        with
        | Option.Some (v_a'2425) ->
            (Obj.magic
               v_some'2423
               v_a'2425)
        | Option.None ->
            (Obj.magic
               (Obj.magic
                  v_none'2422
                  ()));;
let v_constructResult =
  v_breakableConstructResult;;
let v_either =
  fun v_left'2428 ->
    fun v_right'2429 ->
      fun v_either'2430 ->
        let v_X'2431 =
          v_either'2430
        in
        let v_defaultCase'3056 =
          fun nv_ ->
            failwith
              "FILE \"/home/vipa/Projects/static-resolvable/breakable-ml/breakable_impl.mc\" 165:4-165:7 ERROR: Reached a never term, which should be impossible in a well-typed program."
        in
        match
          Obj.magic
            v_X'2431
        with
        | CLeft'1799 v_x'3057 ->
            (let v_a'2432 =
               Obj.magic
                 Obj.magic
                 v_x'3057
             in
             Obj.magic
               v_left'2428
               v_a'2432)
        | CRight'1800 v_x'3058 ->
            (Obj.magic
               (let v_b'2433 =
                  Obj.magic
                    Obj.magic
                    v_x'3058
                in
                Obj.magic
                  v_right'2429
                  v_b'2433))
        | _ ->
            (Obj.magic
               (v_defaultCase'3056
                  ()));;
let v_foldError =
  fun v_amb'2435 ->
    fun v_err'2436 ->
      let v_X'2437 =
        v_err'2436
      in
      match
        Obj.magic
          (let v__target'3059 =
             v_X'2437
           in
           match
             Obj.magic
               Obj.magic
               v__target'3059
           with
           | CAmbiguities'2243 v__n'3060 ->
               (Option.Some (v__n'3060))
           | _ ->
               (Obj.magic
                  Obj.magic
                  (Option.None)))
      with
      | Option.Some (v_ambs'2438) ->
          (Obj.magic
             v_amb'2435
             v_ambs'2438)
      | Option.None ->
          (Obj.magic
             (failwith
                "FILE \"/home/vipa/Projects/static-resolvable/breakable-ml/breakable_impl.mc\" 174:4-174:7 ERROR: Reached a never term, which should be impossible in a well-typed program."));;
let v_seqFoldl =
  Boot.Intrinsics.Mseq.Helpers.fold_left;;
let v_ambiguity =
  fun v_f'2441 ->
    fun v_amb'2442 ->
      Obj.magic
        v_f'2441
        (let
           CRec'2492 ({lfirst = v_X'2443})
         =
           Obj.magic
             v_amb'2442
         in
         Obj.magic
           v_X'2443)
        (let
           CRec'2492 ({llast = v_X'2444})
         =
           Obj.magic
             v_amb'2442
         in
         Obj.magic
           v_X'2444)
        (let
           CRec'2492 ({lpartialResolutions = v_X'2445})
         =
           Obj.magic
             v_amb'2442
         in
         Obj.magic
           v_X'2445);;
CRec'2500 { l0 =
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
  type pos

  val lpar_tok : tokish
  val rpar_tok : tokish
  val elide_tok : tokish

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
  type pos

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

  val init : unit -> ropen state

  val addAtom
      : (lclosed, rclosed) input -> (pos * pos) * atom_self -> ropen state -> rclosed state
  val addPrefix
      : (lclosed, ropen) input -> (pos * pos) * prefix_self -> ropen state -> ropen state
  val addPostfix
      : (lopen, rclosed) input -> (pos * pos) * postfix_self -> rclosed state -> rclosed state option
  val addInfix
      : (lopen, ropen) input -> (pos * pos) * infix_self -> rclosed state -> ropen state option

  val finalizeParse : rclosed state -> permanent_node sequence option (* NonEmpty *)

  (* ## Querying the result *)
  type error
  type ambiguity
  type res =
    | Atom of (pos * pos) * atom_self
    | Infix of (pos * pos) * res * pos * infix_self * pos * res
    | Prefix of (pos * pos) * prefix_self * pos * res
    | Postfix of (pos * pos) * res * pos * postfix_self

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
      : (pos * pos -> tokish sequence sequence -> 'a)
        -> ambiguity
        -> 'a
end

module Make (S : Self) = struct
  include S
  open Breakable_impl

  type res =
    | Atom of (pos * pos) * atom_self
    | Infix of (pos * pos) * res * pos * infix_self * pos * res
    | Prefix of (pos * pos) * prefix_self * pos * res
    | Postfix of (pos * pos) * res * pos * postfix_self

  let pos_of_res = function
    | Atom (p, _) -> p
    | Infix (p, _, _, _, _, _) -> p
    | Prefix (p, _, _, _) -> p
    | Postfix (p, _, _, _) -> p

  type tagged_self =
    | AtomSelf of (pos * pos) * atom_self
    | InfixSelf of (pos * pos) * infix_self
    | PrefixSelf of (pos * pos) * prefix_self
    | PostfixSelf of (pos * pos) * postfix_self

  let mk_atom (s : tagged_self) : res = match s with
    | AtomSelf (p, s) -> Atom (p, s)
    | _ -> assert false
  let mk_infix (s : tagged_self) (l : res) (r : res) : res = match s with
    | InfixSelf ((p1, p2), s) -> Infix ((pos_of_res l |> fst, pos_of_res r |> snd), l, p1, s, p2, r)
    | _ -> assert false
  let mk_prefix (s : tagged_self) (r : res) : res = match s with
    | PrefixSelf ((p1, p2), s) -> Prefix ((p1, pos_of_res r |> snd), s, p2, r)
    | _ -> assert false
  let mk_postfix (s : tagged_self) (l : res)  : res = match s with
    | PostfixSelf ((p1, p2), s) -> Postfix ((pos_of_res l |> fst, p2), l, p1, s)
    | _ -> assert false

  let selfToStr = function
    | AtomSelf (_, s) -> atom_to_str s
    | InfixSelf (_, s) -> infix_to_str s
    | PrefixSelf (_, s) -> prefix_to_str s
    | PostfixSelf (_, s) -> postfix_to_str s

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

  let init () = Obj.magic v_init ()

  let addAtom input (p, self) st = Obj.magic v_addAtom input (AtomSelf (p, self)) st
  let addPrefix input (p, self) st = Obj.magic v_addPrefix input (PrefixSelf (p, self)) st
  let addPostfix input (p, self) st =
    Obj.magic v_addPostfix input (PostfixSelf (p, self)) st
    |> v_maybe (fun _ -> None) (fun x -> Some x)
  let addInfix input (p, self) st =
    Obj.magic v_addInfix input (InfixSelf (p, self)) st
    |> v_maybe (fun _ -> None) (fun x -> Some x)

  let finalizeParse st =
    Obj.magic v_finalizeParse st
    |> v_maybe (fun _ -> None) (fun x -> Some x)

  let constructResult parInput roots =
    Obj.magic v_constructResult selfToStr lpar_tok rpar_tok elide_tok parInput roots
    |> v_either Result.error Result.ok

  let foldError deconAmbiguities error = Obj.magic v_foldError deconAmbiguities error

  let seqFoldl = Obj.magic v_seqFoldl

  let pos_of_tagged = function
    | AtomSelf (p, _) -> p
    | InfixSelf (p, _) -> p
    | PrefixSelf (p, _) -> p
    | PostfixSelf (p, _) -> p

  let ambiguity deconAmbiguity ambiguity =
    let decon selfl selfr resolutions =
      let l = pos_of_tagged selfl |> fst in
      let r = pos_of_tagged selfr |> snd in
      deconAmbiguity (l, r) resolutions
    in Obj.magic v_ambiguity decon ambiguity
end
