const  ---- Configuration parameters ----
       
  PROC_NUM : 10;

type   ---- Type declarations ----

  PROC : scalarset(PROC_NUM);

  STATE : enum {Invalid, Shared, Exclusive};

  MSG : enum {Empty, Reqs, Reqe, Inv, InvAck, Gnts, Gnte};

var   ---- State variables ----

  Cache : array [PROC] of STATE;      -- Caches
  Chan1 : array [PROC] of MSG;        -- Channels for Req*
  Chan2 : array [PROC] of MSG;        -- Channels for Gnt* and Inv
  Chan3 : array [PROC] of MSG;        -- Channels for InvAck
  Invset : array [PROC] of boolean;   -- Set of nodes to be invalidated
  Shrset : array [PROC] of boolean;   -- Set of nodes having S or E copies
  Exgntd : boolean;                   -- E copy has been granted
  Flag : boolean;
  Curcmd : MSG;                       -- Current request command
  Curptr : array[PROC] of boolean;    -- Current request node

---- Initial states ----

startstate "Init"
  for i : PROC do
    Chan1[i] := Empty;
    Chan2[i] := Empty;
    Chan3[i] := Empty;
    Cache[i] := Invalid;
    Invset[i] := false;
    Shrset[i] := false;
    Curptr[i] := false;       
  end;
Exgntd := false;
Curcmd := Empty;
Flag := false;
end;
    
---- State transitions ----

ruleset i : PROC do rule "t1"
  Curcmd = Reqs & Curptr[i] = true & Chan2[i] = Empty & Exgntd = false &
  Flag = false
==>
  Chan2[i] := Gnts;
  Shrset[i] := true;
  Curcmd := Empty;
end end;

ruleset i : PROC do rule "t2"
  Curcmd = Reqe & Curptr[i] = true & Chan2[i] = Empty & Exgntd = false &
  Flag = false &
  forall j : PROC do Shrset[j] = false end
==>
  Chan2[i] := Gnte;
  Shrset[i] := true;
  Exgntd := true;
  Curcmd := Empty;
end end;


ruleset i : PROC do rule "t3"
  Curcmd = Empty & Chan1[i] = Reqs & Flag = false
==>
  Curcmd := Reqs;
  Chan1[i] := Empty;
  Flag := true;
  -- Invset[i] := Shrset[i];
  for j : PROC do
    Invset[j] := Shrset[j];
    if i = j then Curptr[j] := true else Curptr[j] := false end;
  end;
end end;


ruleset i : PROC do rule "t3bis"
  Curcmd = Empty & Chan1[i] = Reqe & Flag = false
==>
  Curcmd := Reqe;
  Chan1[i] := Empty;
  Flag := true;
  -- Invset[i] := Shrset[i];
  for j : PROC do
    Invset[j] := Shrset[j];
    if i = j then Curptr[j] := true else Curptr[j] := false end;
  end;
end end;



ruleset i : PROC do rule "t4"
  Flag = true & Shrset[i] = false
==>
  Invset[i] := false;
end end;

ruleset i : PROC do rule "t5"
  Flag = true & Shrset[i] = true
==>
  Invset[i] := true;
end end;

ruleset i : PROC do rule "t6"
  Flag = true & forall j : PROC do Invset[j] = Shrset[j] end
==>
  Flag := false;
end end;



ruleset i : PROC do rule "t7 t8"
  Chan2[i] = Empty & Invset[i] = true & Flag = false &
  ( Curcmd = Reqe | ( Curcmd = Reqs & Exgntd = true ) )
==>
  Chan2[i] := Inv; Invset[i] := false;
end end;



ruleset i : PROC do rule "t9"
  Chan3[i] = InvAck & Curcmd != Empty & Flag = false
==>
  Chan3[i] := Empty;
  Shrset[i] := false;
  Exgntd := false;
end end;




ruleset i : PROC do rule "t10"
  Chan1[i] = Empty & Cache[i] = Invalid & Flag = false
==>
  Chan1[i] := Reqs;
  Cache[i] := Invalid;
end end;


ruleset i : PROC do rule "t11"
  Chan1[i] = Empty & Cache[i] != Exclusive & Flag = false
==>
  Chan1[i] := Reqe;
end end;



ruleset i : PROC do rule "t12"
  Chan2[i] = Inv & Chan3[i] = Empty & Flag = false
==>
  Chan2[i] := Empty;
  Chan3[i] := InvAck;
  Cache[i] := Invalid;
end end;

ruleset i : PROC do rule "t13"
  Chan2[i] = Gnts & Flag = false
==>
  Cache[i] := Shared;
  Chan2[i] := Empty;
end end;

ruleset i : PROC do rule "Recv_Gnt_Exclusive"
  Chan2[i] = Gnte & Flag = false
==>
  Cache[i] := Exclusive;
  Chan2[i] := Empty;
end end;

---- Invariant properties ----

invariant "CntrlProp"
  forall i : PROC do forall j : PROC do
    i != j -> (Cache[i] = Exclusive -> Cache[j] = Invalid)
  end end;
