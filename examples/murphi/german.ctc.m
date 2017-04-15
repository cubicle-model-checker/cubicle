const  ---- Configuration parameters ----

  NODE_NUM : 2;
  DATA_NUM : 2;

type   ---- Type declarations ----

  NODE : scalarset(NODE_NUM);
  DATA : scalarset(DATA_NUM);

  ABS_NODE : union {NODE, enum{Other}};

  CACHE_STATE : enum {I, S, E};
  CACHE : record State : CACHE_STATE; Data : DATA; end;

  MSG_CMD : enum {Empty, ReqS, ReqE, Inv, InvAck, GntS, GntE};
  MSG : record Cmd : MSG_CMD; Data : DATA; end;

var   ---- State variables ----

  Cache : array [NODE] of CACHE;      -- Caches
  Chan1 : array [NODE] of MSG;        -- Channels for Req*
  Chan2 : array [NODE] of MSG;        -- Channels for Gnt* and Inv
  Chan3 : array [NODE] of MSG;        -- Channels for InvAck
  InvSet : array [NODE] of boolean;   -- Set of nodes to be invalidated
  ShrSet : array [NODE] of boolean;   -- Set of nodes having S or E copies
  ExGntd : boolean;                   -- E copy has been granted
  CurCmd : MSG_CMD;                   -- Current request command
  CurPtr : ABS_NODE;                  -- Current request node
  MemData : DATA;                     -- Memory data
  AuxData : DATA;                     -- Auxiliary variable for latest data

---- Initial states ----

ruleset d : DATA do startstate "Init"
  for i : NODE do
    Chan1[i].Cmd := Empty; Chan2[i].Cmd := Empty; Chan3[i].Cmd := Empty;
    Cache[i].State := I; InvSet[i] := false; ShrSet[i] := false;
  end;
  ExGntd := false; CurCmd := Empty; MemData := d; AuxData := d;
end end;

---- State transitions ----

ruleset i : NODE; d : DATA do rule "Store"
  Cache[i].State = E
==>
  Cache[i].Data := d; AuxData := d;
end end;

ruleset i : NODE do rule "SendReqS"
  Chan1[i].Cmd = Empty & Cache[i].State = I
==>
  Chan1[i].Cmd := ReqS;
end end;

ruleset i : NODE do rule "SendReqE"
  Chan1[i].Cmd = Empty & (Cache[i].State = I | Cache[i].State = S)
==>
  Chan1[i].Cmd := ReqE;
end end;

ruleset i : NODE do rule "RecvReqS"
  CurCmd = Empty & Chan1[i].Cmd = ReqS
==>
  CurCmd := ReqS; CurPtr := i; Chan1[i].Cmd := Empty;
  for j : NODE do InvSet[j] := ShrSet[j] end;
end end;

ruleset i : NODE do rule "RecvReqE"
  CurCmd = Empty & Chan1[i].Cmd = ReqE
==>
  CurCmd := ReqE; CurPtr := i; Chan1[i].Cmd := Empty;
  for j : NODE do InvSet[j] := ShrSet[j] end;
end end;

ruleset i : NODE do rule "SendInv"
  Chan2[i].Cmd = Empty & InvSet[i] = true &
  ( CurCmd = ReqE | CurCmd = ReqS & ExGntd = true )
==>
  Chan2[i].Cmd := Inv; InvSet[i] := false;
end end;

ruleset i : NODE do rule "SendInvAck"
  Chan2[i].Cmd = Inv & Chan3[i].Cmd = Empty
==>
  Chan2[i].Cmd := Empty; Chan3[i].Cmd := InvAck;
  if (Cache[i].State = E) then Chan3[i].Data := Cache[i].Data end;
  Cache[i].State := I; undefine Cache[i].Data;
end end;

ruleset i : NODE do rule "RecvInvAck"
  Chan3[i].Cmd = InvAck & CurCmd != Empty
==>
  Chan3[i].Cmd := Empty; ShrSet[i] := false;
  if (ExGntd = true)
  then ExGntd := false; MemData := Chan3[i].Data; undefine Chan3[i].Data end;
end end;

ruleset i : NODE do rule "SendGntS"
  CurCmd = ReqS & CurPtr = i & Chan2[i].Cmd = Empty & ExGntd = false
==>
  Chan2[i].Cmd := GntS; Chan2[i].Data := MemData; ShrSet[i] := true;
  CurCmd := Empty; undefine CurPtr;
end end;

ruleset i : NODE do rule "SendGntE"
  CurCmd = ReqE & CurPtr = i & Chan2[i].Cmd = Empty & ExGntd = false &
  forall j : NODE do ShrSet[j] = false end
==>
  Chan2[i].Cmd := GntE; Chan2[i].Data := MemData; ShrSet[i] := true;
  ExGntd := true; CurCmd := Empty; undefine CurPtr;
end end;

ruleset i : NODE do rule "RecvGntS"
  Chan2[i].Cmd = GntS
==>
  Cache[i].State := S; Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty; undefine Chan2[i].Data;
end end;

ruleset i : NODE do rule "RecvGntE"
  Chan2[i].Cmd = GntE
==>
  Cache[i].State := E; Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty; undefine Chan2[i].Data;
end end;

---- Invariant properties ----

invariant "CntrlProp"
  forall i : NODE do forall j : NODE do
    i != j -> (Cache[i].State = E -> Cache[j].State = I) &
              (Cache[i].State = S -> Cache[j].State = I | Cache[j].State = S)
  end end;

invariant "DataProp"
  ( ExGntd = false -> MemData = AuxData ) &
  forall i : NODE do Cache[i].State != I -> Cache[i].Data = AuxData end;
