(*
 * (c) 2014 Andreas Rossberg
 *)

module List =
struct
  let rec last = function
    | x::[] -> x
    | x::xs -> last xs
    | [] -> failwith "last"

  let rec take n xs =
    match n, xs with
    | 0, _ -> []
    | n, x::xs' when n > 0 -> x :: take (n - 1) xs'
    | _ -> failwith "drop"

  let rec drop n xs =
    match n, xs with
    | 0, _ -> xs
    | n, x::xs' when n > 0 -> drop (n - 1) xs'
    | _ -> failwith "drop"

  let for_alli p xs = List.for_all (fun b -> b) (List.mapi p xs)

  let rec insert_nodup x = function
    | [] -> [x]
    | x'::xs' as xs ->
      match compare x x' with
      | 0 -> xs
      | n when n < 0 -> x::xs
      | n -> x' :: insert_nodup x xs'

  let merge_nodup xs1 xs2 = List.fold_right insert_nodup xs1 xs2
end

module String =
struct
  let is_prefix s1 s2 =
    String.length s1 <= String.length s2 &&
    s1 = String.sub s2 0 (String.length s1)

  let split s n = (String.sub s 0 n, String.sub s n (String.length s - n))
end
