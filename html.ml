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
    <script defer="defer" src="%s"></script>
</head>
<body style="height: 100%%">
    <noscript>You need to enable JavaScript to run this app.</noscript>
    <div id="root" style="height: 100%%"></div>
</body>
</html>|}

let get_html jsoc_path dot =
  let dot = dot
  |> String.split_on_char '\n'
  |> List.filter (fun s -> s <> "")
  |> String.concat "'+\n'"
  in
  template dot jsoc_path

let print_html outfile jsoc_path dot =
  let html = get_html jsoc_path dot in
  let oc = open_out outfile in
  try
    Printf.fprintf oc "%s" html;
    close_out oc
  with e ->
    close_out_noerr oc;
    raise e
