(* Copyright (C) 2006 SSH Communications Security, Helsinki, Finland
 *
 * This code is released under the MLton license, a BSD-style license.
 * See the LICENSE file or http://mlton.org/License for details.
 *)

structure Array : ARRAY = struct
   (* structure Common = MkSeqCommonExt (Array) *)
   structure Common = struct
      open Array
      fun empty () = tabulate (0, Basic.undefined)
      fun unfoldi fis (n, s) = let
         fun lp (i, s, xs) =
             if i = n then (fromList (rev xs), s)
             else case fis (i, s) of (x, s) => lp (i+1, s, x::xs)
      in if n < 0 orelse maxLen < n then raise Size else lp (0, s, [])
      end
      fun toList t = foldr op :: [] t
      val isoList = (toList, fromList)
      fun for xs ef = app ef xs
      fun fori xs ef = appi ef xs
   end
   open Common Array
   fun duplicate a = tabulate (length a, fn i => sub (a, i))
   val toVector = vector
   fun fromVector v = tabulate (Vector.length v, fn i => Vector.sub (v, i))
   val isoVector = (toVector, fromVector)
   fun map f a = tabulate (length a, fn i => f (sub (a, i)))
end
