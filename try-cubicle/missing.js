
//Provides: caml_ml_output
function caml_ml_output (x, s, p, l) {
  var o = document.getElementById("output");
  o.appendChild (document.createTextNode(s.toString().slice(p,p+l)));
  return 0;
}

//Provides: caml_ml_output_char
//Requires: caml_ml_output
function caml_ml_output_char (x, c) {
    return caml_ml_output (x, String.fromCharCode (c), 0, 1);
}

//Provides: caml_sys_getenv
//Requires: caml_raise_not_found, caml_global_data
function caml_sys_getenv (s) {
    caml_raise_not_found ();
}

//Provides: caml_raise_not_found
//Requires: caml_raise_constant, caml_global_data
function caml_raise_not_found () { caml_raise_constant(caml_global_data[7]); }

//Provides: caml_ml_close_channel
function caml_ml_close_channel () { }

//Provides: caml_sys_close
function caml_sys_close () { }

//Provides: caml_sys_system_command
function caml_sys_system_command () { }
