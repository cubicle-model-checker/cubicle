const  ---- Configuration parameters ----
       
  PROC_NUM : 4;

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
  Curcmd : MSG;                   -- Current request command
  CurClient : PROC;                      -- Current request node

---- Initial states ----

ruleset h : PROC do startstate "Init"
  for i : PROC do
    Chan1[i] := Empty; Chan2[i] := Empty; Chan3[i] := Empty;
    Cache[i] := Invalid; InvSet[i] := false; ShrSet[i] := false;
  end;
Exgntd := false; Curcmd := Empty; CurClient := h;
end end;
    
---- State transitions ----

ruleset i : PROC do rule "send_req_shared"
  Chan1[i] = Empty & Cache[i] = Invalid
==>
  Chan1[i] := Reqs;
end end;

ruleset i : PROC do rule "send_req_exclusive"
  Chan1[i] = Empty & (Cache[i] = Invalid | Cache[i] = Shared)
==>
  Chan1[i] := Reqe;
end end;

ruleset i : PROC do rule "recv_req_shqred"
  CurCmd = Empty & Chan1[i] = Reqs
==>
  CurCmd := Reqs; CurClient := i; Chan1[i] := Empty;
  for j : PROC do Invset[j] := Shrset[j] end;
end end;

ruleset i : PROC do rule "recv_req_exclusive"
  CurCmd = Empty & Chan1[i] = Reqe
==>
  CurCmd := Reqe; CurClient := i; Chan1[i] := Empty;
  for j : PROC do Invset[j] := Shrset[j] end;
end end;

ruleset i : PROC do rule "send_inv"
  Chan2[i] = Empty & InvSet[i] = true &
  ( CurCmd = Reqe | CurCmd = Reqs & Exgntd = true )
==>
  Chan2[i] := Inv; Invset[i] := false;
end end;

ruleset i : PROC do rule "send_invack"
  Chan2[i] = Inv & Chan3[i] = Empty
==>
  Chan2[i] := Empty;
  Chan3[i] := Invack;
  Cache[i] := Invalid;
end end;

ruleset i : PROC do rule "recv_invack"
  Chan3[i] = Invack & CurCmd != Empty
==>
  Chan3[i] := Empty;
  ShrSet[i] := false;
  Exgntd := false;
end end;

ruleset i : PROC do rule "send_gnt_shared"
  CurCmd = Reqs & CurClient = i & Chan2[i] = Empty & Exgntd = false
==>
  Chan2[i] := Gnts;
  Shrset[i] := true;
  CurCmd := Empty;
end end;

ruleset i : PROC do rule "send_gnt_exclusive"
  CurCmd = Reqe & CurClient = i & Chan2[i] = Empty & Exgntd = false &
  forall j : PROC do Shrset[j] = false end
==>
  Chan2[i] := Gnte;
  Shrset[i] := true;
  Exgntd := true;
  CurCmd := Empty;
end end;

ruleset i : PROC do rule "Recv_Gnt_Shared"
  Chan2[i] = Gnts
==>
  Cache[i] := Shared;
  Chan2[i] := Empty;
end end;

ruleset i : PROC do rule "Recv_Gnt_Exclusive"
  Chan2[i] = Gnte
==>
  Cache[i] := Exclusive;
  Chan2[i] := Empty;
end end;

---- Invariant properties ----

invariant "CntrlProp"
  forall i : PROC do forall j : PROC do
    i != j -> (Cache[i] = Exclusive -> Cache[j] = Invalid)
  end end;
