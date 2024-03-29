(* Copyright (C) 2006 SSH Communications Security, Helsinki, Finland
 *
 * This code is released under the MLton license, a BSD-style license.
 * See the LICENSE file or http://mlton.org/License for details.
 *)

functor MkRealSane (R : REAL) = struct
   open R
   val fromDecimal' = Option.valOf o fromDecimal
   fun fromDecimal d = SOME (fromDecimal' d) handle _ => NONE
end
