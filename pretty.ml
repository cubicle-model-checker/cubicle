(**************************************************************************)
(*                                                                        *)
(*                              Cubicle                                   *)
(*                                                                        *)
(*                       Copyright (C) 2011-2014                          *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                       Universite Paris-Sud 11                          *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open Format
open Ast
open Types
open Vertice
open Options
open Util

(* Set width of pretty printing boxes to number of columns *)
let vt_width =
  if js_mode () then 80
  else
    try
      let scol = syscall "tput cols" in
      let w = int_of_string (remove_trailing_whitespaces_end scol) in
      set_margin w;
      w
    with Not_found | Failure _ -> 80

let print_line = 
  let s = String.make vt_width '-' in
  fun fmt () -> fprintf fmt "%s@." s

let print_double_line = 
  let s = String.make vt_width '=' in
  fun fmt () -> fprintf fmt "%s@." s


let print_title fmt s =
  printf "%a" print_double_line ();
  printf "* @{<b>%s@}\n" s;
  printf "%a" print_line ()


type style =
  | User of int
  | Normal
  | Bold
  | Bold_off
  | Dim
  | Underline
  | Underline_off
  | Inverse
  | Inverse_off
  | Blink_off
  | FG_Black
  | FG_Red
  | FG_Green
  | FG_Yellow
  | FG_Blue
  | FG_Magenta
  | FG_Cyan
  | FG_Gray
  | FG_Default
  | BG_Black
  | BG_Red
  | BG_Green
  | BG_Yellow
  | BG_Blue
  | BG_Magenta
  | BG_Cyan
  | BG_Gray
  | BG_Default
  | FG_Black_B
  | FG_Red_B
  | FG_Green_B
  | FG_Yellow_B
  | FG_Blue_B
  | FG_Magenta_B
  | FG_Cyan_B
  | FG_Gray_B
  | FG_Default_B
  | BG_Black_B
  | BG_Red_B
  | BG_Green_B
  | BG_Yellow_B
  | BG_Blue_B
  | BG_Magenta_B
  | BG_Cyan_B
  | BG_Gray_B
  | BG_Default_B


let assoc_style =  function
  | User i  -> string_of_int i
  | Normal -> "0"
  | Bold -> "1"
  | Bold_off -> "22"
  | Dim ->  "2"
  | Underline -> "4"
  | Underline_off -> "24"
  | Inverse -> "7"
  | Inverse_off -> "27"
  | Blink_off -> "22"
  | FG_Black -> "30"
  | FG_Red -> "31"
  | FG_Green -> "32"
  | FG_Yellow -> "33"
  | FG_Blue -> "34"
  | FG_Magenta -> "35"
  | FG_Cyan -> "36"
  | FG_Gray -> "37"
  | FG_Default -> "39"
  | BG_Black -> "40"
  | BG_Red -> "41"
  | BG_Green -> "42"
  | BG_Yellow -> "43"
  | BG_Blue -> "44"
  | BG_Magenta -> "45"
  | BG_Cyan -> "46"
  | BG_Gray -> "47"
  | BG_Default -> "49"
  | FG_Black_B -> "90"
  | FG_Red_B -> "91"
  | FG_Green_B -> "92"
  | FG_Yellow_B -> "93"
  | FG_Blue_B -> "94"
  | FG_Magenta_B -> "95"
  | FG_Cyan_B -> "96"
  | FG_Gray_B -> "97"
  | FG_Default_B -> "99"
  | BG_Black_B -> "100"
  | BG_Red_B -> "101"
  | BG_Green_B -> "102"
  | BG_Yellow_B -> "103"
  | BG_Blue_B -> "104"
  | BG_Magenta_B -> "105"
  | BG_Cyan_B -> "106"
  | BG_Gray_B -> "107"
  | BG_Default_B -> "109"


let style_of_tag = function
  | "n" -> Normal
  | "b" -> Bold
  | "/b" -> Bold_off
  | "dim" -> Dim
  | "u" -> Underline
  | "/u" -> Underline_off
  | "i" -> Inverse
  | "/i" -> Inverse_off
  | "/bl" -> Blink_off
  | "fg_black" -> FG_Black
  | "fg_red" -> FG_Red
  | "fg_green" -> FG_Green
  | "fg_yellow" -> FG_Yellow
  | "fg_blue" -> FG_Blue
  | "fg_magenta" -> FG_Magenta
  | "fg_cyan" -> FG_Cyan
  | "fg_gray" -> FG_Gray
  | "fg_default" -> FG_Default
  | "bg_black" -> BG_Black
  | "bg_red" -> BG_Red
  | "bg_green" -> BG_Green
  | "bg_yellow" -> BG_Yellow
  | "bg_blue" -> BG_Blue
  | "bg_magenta" -> BG_Magenta
  | "bg_cyan" -> BG_Cyan
  | "bg_gray" -> BG_Gray
  | "bg_default" -> BG_Default
  | "fg_black_b" -> FG_Black_B
  | "fg_red_b" -> FG_Red_B
  | "fg_green_b" -> FG_Green_B
  | "fg_yellow_b" -> FG_Yellow_B
  | "fg_blue_b" -> FG_Blue_B
  | "fg_magenta_b" -> FG_Magenta_B
  | "fg_cyan_b" -> FG_Cyan_B
  | "fg_gray_b" -> FG_Gray_B
  | "fg_default_b" -> FG_Default_B
  | "bg_black_b" -> BG_Black_B
  | "bg_red_b" -> BG_Red_B
  | "bg_green_b" -> BG_Green_B
  | "bg_yellow_b" -> BG_Yellow_B
  | "bg_blue_b" -> BG_Blue_B
  | "bg_magenta_b" -> BG_Magenta_B
  | "bg_cyan_b" -> BG_Cyan_B
  | "bg_gray_b" -> BG_Gray_B
  | "bg_default_b" -> BG_Default_B
  | _ -> raise Not_found


let start_tag t = 
  try Printf.sprintf "[%sm" (assoc_style (style_of_tag t))
  with Not_found -> ""

let stop_tag t = 
  let st = match style_of_tag t with
    | Bold -> Bold_off
    | Underline -> Underline_off
    | Inverse -> Inverse_off

    | FG_Black | FG_Red | FG_Green | FG_Yellow | FG_Blue
    | FG_Magenta | FG_Cyan | FG_Gray | FG_Default -> FG_Default

    | BG_Black | BG_Red | BG_Green | BG_Yellow | BG_Blue 
    | BG_Magenta | BG_Cyan | BG_Gray | BG_Default -> BG_Default

    | FG_Black_B | FG_Red_B | FG_Green_B | FG_Yellow_B | FG_Blue_B 
    | FG_Magenta_B | FG_Cyan_B | FG_Gray_B | FG_Default_B -> FG_Default
 
    | BG_Black_B | BG_Red_B | BG_Green_B | BG_Yellow_B | BG_Blue_B
    | BG_Magenta_B | BG_Cyan_B | BG_Gray_B | BG_Default_B -> BG_Default

    | _ -> Normal
  in
  Printf.sprintf "[%sm" (assoc_style st)
        

let add_colors formatter =
  pp_set_tags formatter true;
  let old_fs = Format.pp_get_formatter_tag_functions formatter () in
  Format.pp_set_formatter_tag_functions formatter
    { old_fs with
      Format.mark_open_tag = start_tag;
      Format.mark_close_tag = stop_tag }

let _ =
  if not nocolor then begin
    add_colors std_formatter;
    add_colors err_formatter;
  end
