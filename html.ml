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

let template = Printf.sprintf {|<!doctype html>
<html lang="en" style="height: 100%%">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width,initial-scale=1">
    <meta name="theme-color" content="#000000"/>
    <meta name="description" content="Visualizer for cucicle using JavaScript an WebGL"/>
    <link rel="stylesheet" href="https://fonts.googleapis.com/css?family=Roboto:300,400,500,700&display=swap"/>
    <link rel="stylesheet" href="https://fonts.googleapis.com/icon?family=Material+Icons"/>
    <title>js_of_cubicle</title>
    <script type="text/javascript">
    window.__DOT_STR__ = '%s'
    </script>
</head>
<body style="height: 100%%">
    <noscript>You need to enable JavaScript to run this app.</noscript>
    <div id="root" style="height: 100%%"></div>
    %s
</body>
</html>|}

let get_html jsoc_path dot =
  let dot = dot
  |> String.split_on_char '\n'
  |> List.filter (fun s -> s <> "")
  |> String.concat "'+\n'"
  in
  template dot (Printf.sprintf {|<script defer="defer" src="%s"></script>|} jsoc_path)

let get_html_embedded jsoc_path dot =
  let dot = dot
  |> String.split_on_char '\n'
  |> List.filter (fun s -> s <> "")
  |> String.concat "'+\n'"
  in
  let ic = open_in jsoc_path in
  try
    let str = really_input_string ic (in_channel_length ic) in
    close_in ic;
    template dot (Printf.sprintf {|<script type="text/javascript">%s</script>|} str)
  with e ->
    close_in_noerr ic;
    raise e


let print_html outfile jsoc_path dot embedded =
  let html =
    if embedded then get_html_embedded jsoc_path dot
    else get_html jsoc_path dot in
  let oc = open_out outfile in
  try
    Printf.fprintf oc "%s" html;
    close_out oc
  with e ->
    close_out_noerr oc;
    raise e
