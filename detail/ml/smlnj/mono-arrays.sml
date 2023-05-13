(* Copyright (C) 2006 SSH Communications Security, Helsinki, Finland
 *
 * This code is released under the MLton license, a BSD-style license.
 * See the LICENSE file or http://mlton.org/License for details.
 *)

(** == Extended {MONO_ARRAY} modules for SML/NJ == *)

structure RealArray =
   MkMonoArrayExt (structure MonoArray = BasisRealArray
                   structure MonoVector = BasisRealVector)
structure Real64Array =
   MkMonoArrayExt (structure MonoArray = BasisReal64Array
                   structure MonoVector = BasisReal64Vector)
