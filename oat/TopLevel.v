(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import Vellvm.Classes.
Require Import Oat.OATIO.
Require Import Oat.StepSemantics.
Require Import Oat.Memory.


Definition run_with_memory prog : Trace dvalue :=
  's <- init_state prog;
  'm <- memD empty (SS.step_sem prog (Step s));
  mret m.