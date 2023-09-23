(* Copyright (C) 2006-2008 SSH Communications Security, Helsinki, Finland
 *
 * This code is released under the MLton license, a BSD-style license.
 * See the LICENSE file or http://mlton.org/License for details.
 *)

structure With :> WITH = struct
   type 'a t = ('a, Unit.t) CPS.t

   infix >>=

   (* structure Monad = MkMonad (type 'a monad = 'a t open CPS) *)
   structure Monad : MONAD = struct
      type 'a monad = 'a t
      open CPS
      infix >> >>& >< >>* >>= >>@ oo =<<

      type 'a func = 'a monad
      type 'a monad_ex = 'a monad

      fun f =<< x = x >>= f

      fun pure f = return o f
      fun map f aM = aM >>= pure f
      fun thunk th = map th (return ())

      fun aM >> bM = aM >>= Fn.const bM

      local
         fun mk f (aM, bM) = aM >>= (fn a => bM >>= (fn b => return (f (a, b))))
      in
         fun op >>& ? = mk Product.& ?
         val op >< = op >>&
         fun op >>* ? = mk Fn.id ?
         fun op >>@ ? = mk Fn.\> ?
      end

      fun ignore m = map Effect.ignore m
      fun (y2zM oo x2yM) x = x2yM x >>= y2zM

      local
         fun mk fM b fin =
          fn []    => return (fin b)
           | x::xs => fM (x, b) >>= (fn b' => mk fM b' fin xs)
      in
         fun foldl fM b = mk fM b Fn.id
         fun foldr fM b = foldl fM b o rev

         fun seqWith x2yM = mk (fn (x, ys) => map (fn y => y::ys) (x2yM x)) [] rev
         fun appWith x2yM = foldl (ignore o x2yM o Pair.fst) ()

         fun seq xMs = seqWith Fn.id xMs
         fun app xMs = appWith Fn.id xMs

         fun seqWithPartial x2yM =
             mk (fn (x, ys) => map (fn SOME y => y::ys | NONE => ys) (x2yM x))
                [] rev
      end

      fun when b m = if b then m else return ()
      fun unless b = when (not b)

      local
         fun tabulateTail f n m ac =
             if n = m then
                return (rev ac)
             else
                f m >>= (fn x => tabulateTail f n (m + 1) (x::ac))
      in
         fun tabulate n f = tabulateTail f n 0 []
      end

      local
         fun pairFst x y = (y, x)
         fun pairSnd x y = (x, y)
      in
         fun mapFst x2yM (x, z) = map (pairFst z) (x2yM x)
         fun mapSnd x2yM (z, x) = map (pairSnd z) (x2yM x)
      end
   end
   open Monad

   val lift = Fn.id
   val for = Fn.id
   fun one aM f =
       case ref NONE
        of res => (aM (fn a => res := SOME (f a)) : Unit.t ; valOf (!res))

   fun alloc g a f = f (g a)
   fun free ef x f = (f x handle e => (ef x ; raise e)) before ef x

   fun around new del = alloc new () >>= free del
   fun entry ef = alloc ef ()
   fun exit ef = free ef ()
   local
      fun `f x () = f x
   in
      fun calling {entry, exit} v = around (`entry v) (`exit v)
      fun passing ef {entry, exit} = around (`ef entry) (`ef exit)
   end
end
