(* Copyright (C) 2006 SSH Communications Security, Helsinki, Finland
 *
 * This code is released under the MLton license, a BSD-style license.
 * See the LICENSE file or http://mlton.org/License for details.
 *)

(** == Extended {MONO_ARRAY_SLICE} modules for SML/NJ == *)

structure RealArraySlice =
   MkMonoArraySliceExt (structure MonoArraySlice = BasisRealArraySlice)
structure Real64ArraySlice =
   MkMonoArraySliceExt (structure MonoArraySlice = BasisReal64ArraySlice)