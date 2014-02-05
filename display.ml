open Tk
let top = openTk ();;
Wm.title_set top "Application 1";;
Wm.geometry_set top "200x50";;

bind ~events:[`Modified ([`Control], `KeyPressDetail "q")]
  ~action:(fun e ->
     flush stdout;
     closeTk();
     exit 0)
   top;;

let l = Label.create
    ~text:"This a message"
    top ;;

let b = Button.create
    ~text:"The end"
    ~command:(fun () ->
      closeTk () ;
      Printf.printf "Bye.\n" ;
      exit 0)
    top ;;
pack [b] ;;
pack [l] ;;

let _ = Printexc.print mainLoop ()
