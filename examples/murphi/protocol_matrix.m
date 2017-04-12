const

  L1Cnt:      1;
  ClusterCnt: 2;
  DataCnt:    1;

type

  L1Id:      scalarset(L1Cnt);
  CId: scalarset(ClusterCnt);
  Datas:     scalarset(DataCnt);

  ClusterRange: 0 .. ClusterCnt;

  CacheState: enum {Invld, Shrd, Excl};
  Commands: enum {None, Get, GetX, Putt, PutX, NAck, ShWb, 
		  Inv, InvAck, DxFer, WINV, WB};

  L1State: record
    State: CacheState;
    Data: Datas;
    Req: Commands;
  end;

  L2State: record
    State: CacheState;
    Data: Datas; 
    pending: boolean;
  end;

  ClusterState: record
    L1s: array [L1Id] of L1State;
    L2: L2State;
    OnlyCopy: boolean;

    ifInReq: boolean;
    ReqCmd: Commands;

    ifOutRpy: boolean;
    outRpy: record
      Cmd: Commands;
      Data: Datas;
    end;

    ifOutReq: boolean;
    outReq: record
      Cmd: Commands;
      Cluster: CId;
    end;

    ifInRpy: boolean;
    inRpy: record
      Cmd: Commands;
      Data: Datas;
      Dest: CId;
    end;

    WbReq: record
      Cmd: Commands;
      Data: Datas;
    end;

    RAC: record
      Cmd: Commands;
      -- InvCnt: ClusterRange;
      Inved: array [CId] of boolean;
      ToInv: array [CId] of boolean;
    end;
  end;

  GUni_Msg: record
    Cmd: Commands;
    Cluster: CId;
    Data: Datas;
    -- InvCnt: ClusterRange;
    ToInv: array [CId] of boolean;
  end;

  GInv_Msg: record
    Cmd: Commands;
    Cluster: CId;
  end;

  GShWb_Msg: record
    Cmd: Commands;
    Data: Datas;
    Cluster: CId;
  end;

  GWb_Msg: record
    Cmd: Commands;
    Cluster: CId;
    Data: Datas;
  end;

  DirState: record
    State: CacheState;
    ShrSet: array [CId] of boolean;
    Owner: CId;
    pending: boolean;
    Mem: Datas;
  end;

var

  Clusters: array [CId] of ClusterState;
  GUniMsg: array [CId] of GUni_Msg;
  GInvMsg: array [CId] of GInv_Msg;
  GShWbMsg: GShWb_Msg;
  GWbMsg: GWb_Msg;
  GDir:      DirState;
  SysData:  Datas;


ruleset d: Datas do
startstate "initializer"
  for c: CId do
    for i: L1Id do
      Clusters[c].L1s[i].State := Invld;
      undefine Clusters[c].L1s[i].Data;
      Clusters[c].L1s[i].Req := None;
    end;

    Clusters[c].L2.State := Invld;
    undefine Clusters[c].L2.Data;
    Clusters[c].L2.pending := false;
    Clusters[c].OnlyCopy := false;

    Clusters[c].ifInReq := false;
    Clusters[c].ReqCmd := None;
    Clusters[c].ifOutRpy := false;
    Clusters[c].outRpy.Cmd := None;
    undefine Clusters[c].outRpy.Data;

    Clusters[c].ifOutReq := false;
    Clusters[c].outReq.Cmd := None;
    undefine Clusters[c].outReq.Cluster;
    Clusters[c].ifInRpy := false;
    Clusters[c].inRpy.Cmd := None;
    undefine Clusters[c].inRpy.Data;
    undefine Clusters[c].inRpy.Dest;
    Clusters[c].WbReq.Cmd := None;
    undefine Clusters[c].WbReq.Data;

    Clusters[c].RAC.Cmd := None;
    for c2: CId do
      Clusters[c].RAC.Inved[c2] := false;
      Clusters[c].RAC.ToInv[c2] := false;
      GUniMsg[c].ToInv[c2] := false;
    end;

    GUniMsg[c].Cmd := None;
    undefine GUniMsg[c].Cluster;
    undefine GUniMsg[c].Data;
    -- GUniMsg[c].InvCnt := 0;

    GInvMsg[c].Cmd := None;
    undefine GInvMsg[c].Cluster;
  end;

  GShWbMsg.Cmd := None;
  undefine GShWbMsg.Data;
  undefine GShWbMsg.Cluster;
  GWbMsg.Cmd := None;
  undefine GWbMsg.Data;
  undefine GWbMsg.Cluster;

  SysData := d;

  GDir.State := Invld;
  GDir.Mem := d;
  undefine GDir.Owner;
  GDir.pending := false;
  for c: CId do
    GDir.ShrSet[c] := false;
  end;
end;
end;


ruleset c: CId; i: L1Id; d: Datas do
rule "1 L1 cache update cache"
  Clusters[c].L1s[i].State = Excl 
==>
  Clusters[c].L1s[i].Data := d;
  SysData := d;
end;
end;


ruleset c: CId; i: L1Id do
rule "2 L1 cache write back cache"
  Clusters[c].L1s[i].State = Excl
==>
  Clusters[c].L2.State := Excl;
  Clusters[c].L2.Data := Clusters[c].L1s[i].Data;

  Clusters[c].L1s[i].State := Invld;
  undefine Clusters[c].L1s[i].Data;
end;
end;


ruleset c: CId; i: L1Id do
rule "3 L1 req shrd copy"
  Clusters[c].L1s[i].State = Invld &
  Clusters[c].L1s[i].Req = None 
==>
  Clusters[c].L1s[i].Req := Get;
end;
end;


ruleset c: CId; i: L1Id do
rule "4 L1 req excl copy"
  (Clusters[c].L1s[i].State = Invld |
   Clusters[c].L1s[i].State = Shrd) &
  Clusters[c].L1s[i].Req = None 
==>
  Clusters[c].L1s[i].Req := GetX;
end;
end;


ruleset c: CId; i: L1Id do
rule "5 L1 req copy, cluster invld, fwd outside"
  (Clusters[c].L1s[i].Req = Get  |
   Clusters[c].L1s[i].Req = GetX) &
  forall j: L1Id do
    Clusters[c].L1s[j].State = Invld
  end &
  Clusters[c].L2.State = Invld &
  Clusters[c].L2.pending = false
==>
  Clusters[c].L2.pending := true;
  Clusters[c].ifInReq := true;
  Clusters[c].ReqCmd := Clusters[c].L1s[i].Req;

  Clusters[c].L1s[i].Req := None;
end;
end;


ruleset c: CId; i: L1Id do
rule "6 L1 req copy, cluster busy, NAck"
  (Clusters[c].L1s[i].Req = Get  |
   Clusters[c].L1s[i].Req = GetX) &
  Clusters[c].L2.pending = true
==>
  Clusters[c].L1s[i].Req := None;
end;
end;


ruleset c: CId; i: L1Id do
rule "7 L1 req shrd copy, L2 reply"
  Clusters[c].L1s[i].Req = Get &
  Clusters[c].L2.State = Shrd &
  Clusters[c].L2.pending = false
==>
  Clusters[c].L1s[i].State := Shrd;
  Clusters[c].L1s[i].Data := Clusters[c].L2.Data;
  Clusters[c].L1s[i].Req := None;
end;
end;


ruleset c: CId; i: L1Id; j: L1Id do
rule "8 L1 req shrd copy, another L1 reply"
  Clusters[c].L1s[i].Req = Get &
  Clusters[c].L1s[j].State = Shrd &
  Clusters[c].L2.State = Invld &
  Clusters[c].L2.pending = false
==>
  Clusters[c].L1s[i].State := Shrd;
  Clusters[c].L1s[i].Data := Clusters[c].L1s[j].Data;
  Clusters[c].L1s[i].Req := None;
end;
end;


ruleset c: CId; i: L1Id do
rule "9 L1 req excl copy, L2 reply"
  Clusters[c].L1s[i].Req = GetX &
  Clusters[c].L2.State = Excl &
  Clusters[c].L2.pending = false  
==>
  Clusters[c].L1s[i].State := Excl;
  Clusters[c].L1s[i].Data := Clusters[c].L2.Data;
  Clusters[c].L1s[i].Req := None;

  Clusters[c].L2.State := Invld;
  undefine Clusters[c].L2.Data;
end;
end;


ruleset c: CId; i: L1Id; j: L1Id do
rule "10 L1 req excl copy, another L1 reply"
  Clusters[c].L1s[i].Req = GetX &
  Clusters[c].L1s[j].State = Excl &
  Clusters[c].L2.State = Invld &
  Clusters[c].L2.pending = false
==>
  Clusters[c].L1s[i].State := Excl;
  Clusters[c].L1s[i].Data := Clusters[c].L1s[j].Data;
  Clusters[c].L1s[i].Req := None;

  Clusters[c].L1s[j].State := Invld;
  undefine Clusters[c].L1s[j].Data;
end;
end;


ruleset c: CId; i: L1Id do
rule "11 L1 req excl copy, L2 reply"
  Clusters[c].L1s[i].Req = GetX &
  Clusters[c].L2.State = Shrd &
  Clusters[c].OnlyCopy = true &
  Clusters[c].L2.pending = false  
==>
  for j: L1Id do
    if (i != j & Clusters[c].L1s[j].State = Shrd) then
      Clusters[c].L1s[j].State := Invld;
      undefine Clusters[c].L1s[j].Data;
    end;
  end;

  Clusters[c].L1s[i].State := Excl;
  Clusters[c].L1s[i].Data := Clusters[c].L2.Data;
  Clusters[c].L2.State := Invld;
  undefine Clusters[c].L2.Data;
end;
end;


ruleset c: CId; i: L1Id do
rule "12 L1 req excl copy, cluster fwd outside"
  Clusters[c].L1s[i].Req = GetX &
  Clusters[c].OnlyCopy = false &
  Clusters[c].L2.pending = false  
==>
  for j: L1Id do
    if Clusters[c].L1s[j].State = Shrd then
      Clusters[c].L1s[j].State := Invld;
      undefine Clusters[c].L1s[j].Data;
    end;
  end;

  Clusters[c].L2.State := Invld;
  undefine Clusters[c].L2.Data;

  Clusters[c].L2.pending := true;
  Clusters[c].ifInReq := true;
  Clusters[c].ReqCmd := Clusters[c].L1s[i].Req;
  Clusters[c].L1s[i].Req := None;
end;
end;


ruleset c: CId do
rule "13 Cluster sends req to global dir"
  Clusters[c].ifInReq = true &
  Clusters[c].RAC.Cmd = None &
  Clusters[c].WbReq.Cmd = None 
==>
  Clusters[c].RAC.Cmd := Clusters[c].ReqCmd;
  GUniMsg[c].Cmd := Clusters[c].ReqCmd;
  GUniMsg[c].Cluster := c;

  Clusters[c].ifInReq := false;
end;
end;


ruleset c: CId do
rule "14 global dir reply cluster shrd req"
  GUniMsg[c].Cmd = Get &
  GUniMsg[c].Cluster = c &
  (GDir.State = Shrd |
   GDir.State = Invld) &
  GDir.pending = false
==>
  GUniMsg[c].Cmd := Putt;
  GUniMsg[c].Data := GDir.Mem;
  GDir.ShrSet[c] := true;
  GDir.State := Shrd;
end;
end;


ruleset c: CId do
rule "15 global dir reply cluster excl req"
  GUniMsg[c].Cmd = GetX &
  GUniMsg[c].Cluster = c &
  GDir.State = Invld &
  GDir.pending = false
==>
  GUniMsg[c].Cmd := PutX;
  GUniMsg[c].Data := GDir.Mem;
  -- GUniMsg[c].InvCnt := 0;
  for c2: CId do
    GUniMsg[c].ToInv[c2] := false;
  end;
  GDir.Owner := c;
  GDir.State := Excl;
end;
end;


ruleset c: CId do
rule "16 global dir fwd req to owner cluster"
  (GUniMsg[c].Cmd = Get |
   GUniMsg[c].Cmd = GetX) &
  GUniMsg[c].Cluster = c &
  GDir.State = Excl &
  GDir.pending = false 
==>
if (c = GDir.Owner) then
  GUniMsg[c].Cmd := NAck;
  undefine GUniMsg[c].Cluster;
else 
  GDir.pending := true;

  GUniMsg[c].Cmd := GUniMsg[c].Cmd; 
  GUniMsg[c].Cluster := GDir.Owner;
end;
end;
end;


ruleset c1: CId; c2: CId do
rule "17 Cluster c2 busy, NAck c1's req"
  (GUniMsg[c1].Cmd = Get |
   GUniMsg[c1].Cmd = GetX) &
  GUniMsg[c1].Cluster = c2 &
  c1 != c2 &
  Clusters[c2].RAC.Cmd != None
==>
  GUniMsg[c1].Cmd := NAck;
  undefine GUniMsg[c1].Cluster;
  undefine GUniMsg[c1].Data;

  GShWbMsg.Cmd := NAck;
  undefine GShWbMsg.Cluster;
  undefine GShWbMsg.Data;
end;
end;


rule "18 Global dir receive NAck"
  GShWbMsg.Cmd = NAck &
  GDir.pending = true
==>
  GShWbMsg.Cmd := None;
  GDir.pending := false;
end;


ruleset c1: CId; c2: CId do
rule "19 Cluster c2 takes c1's req"
  (GUniMsg[c1].Cmd = Get | 
   GUniMsg[c1].Cmd = GetX) &
  GUniMsg[c1].Cluster = c2 &
  c1 != c2 &
  Clusters[c2].RAC.Cmd = None 
==>
  Clusters[c2].outReq.Cmd := GUniMsg[c1].Cmd;
  Clusters[c2].outReq.Cluster := c1;

  GUniMsg[c1].Cmd := None;
  undefine GUniMsg[c1].Cluster;
  undefine GUniMsg[c1].Data;
end;
end;


ruleset c: CId do
rule "20 Cluster busy, NAck outside req"
  (Clusters[c].outReq.Cmd = Get |
   Clusters[c].outReq.Cmd = GetX) &
  Clusters[c].L2.pending = true
==>
  Clusters[c].inRpy.Cmd := NAck;
  Clusters[c].inRpy.Dest := Clusters[c].outReq.Cluster;
  undefine Clusters[c].inRpy.Data;

  Clusters[c].outReq.Cmd := None;
  undefine Clusters[c].outReq.Cluster;
end;
end;


ruleset c: CId do
rule "21 Cluster reply fwd req by Put"
  Clusters[c].outReq.Cmd = Get &
  Clusters[c].L2.pending = false &
  Clusters[c].L2.State = Shrd
==>
  Clusters[c].inRpy.Cmd := Putt;
  Clusters[c].inRpy.Dest := Clusters[c].outReq.Cluster;
  Clusters[c].inRpy.Data := Clusters[c].L2.Data;

  assert Clusters[c].OnlyCopy = true;
  Clusters[c].OnlyCopy := false;

  Clusters[c].outReq.Cmd := None;
  undefine Clusters[c].outReq.Cluster;
end;
end;


ruleset c: CId do
rule "22 Cluster reply fwd req by PutX1"
  Clusters[c].outReq.Cmd = GetX &
  Clusters[c].L2.pending = false &
  Clusters[c].L2.State = Excl
==>
  Clusters[c].inRpy.Cmd := PutX;
  Clusters[c].inRpy.Dest := Clusters[c].outReq.Cluster;
  Clusters[c].inRpy.Data := Clusters[c].L2.Data;

  assert Clusters[c].OnlyCopy = true;
  Clusters[c].OnlyCopy := false;
  Clusters[c].L2.State := Invld;
  undefine Clusters[c].L2.Data;

  Clusters[c].outReq.Cmd := None;
  undefine Clusters[c].outReq.Cluster;
end;
end;


ruleset c: CId; i: L1Id do
rule "23 Cluster reply fwd req by PutX2"
  Clusters[c].outReq.Cmd = GetX &
  Clusters[c].L2.pending = false &
  Clusters[c].L2.State = Invld &
  Clusters[c].L1s[i].State = Excl
==>
  Clusters[c].inRpy.Cmd := PutX;
  Clusters[c].inRpy.Dest := Clusters[c].outReq.Cluster;
  Clusters[c].inRpy.Data := Clusters[c].L1s[i].Data;

  assert Clusters[c].OnlyCopy = true;
  Clusters[c].OnlyCopy := false;
  Clusters[c].L1s[i].State := Invld;
  undefine Clusters[c].L1s[i].Data;

  Clusters[c].outReq.Cmd := None;
  undefine Clusters[c].outReq.Cluster;
end;
end;


ruleset c: CId do
rule "24 Cluster reply fwd req by PutX3"
  Clusters[c].outReq.Cmd = GetX &
  Clusters[c].L2.pending = false &
  Clusters[c].L2.State = Shrd
==>
  Clusters[c].inRpy.Cmd := PutX;
  Clusters[c].inRpy.Dest := Clusters[c].outReq.Cluster;
  Clusters[c].inRpy.Data := Clusters[c].L2.Data;

  assert Clusters[c].OnlyCopy = true;
  Clusters[c].OnlyCopy := false;
  Clusters[c].L2.State := Invld;
  undefine Clusters[c].L2.Data;

  for i: L1Id do
    Clusters[c].L1s[i].State := Invld;
    undefine Clusters[c].L1s[i].Data;
  end;

  Clusters[c].outReq.Cmd := None;
  undefine Clusters[c].outReq.Cluster;
end;
end;


ruleset c: CId; i: L1Id do
rule "25 Cluster reply fwd req by Put"
  Clusters[c].outReq.Cmd = Get &
  Clusters[c].L2.pending = false &
  Clusters[c].L2.State = Invld &
  Clusters[c].L1s[i].State = Shrd
==>
  Clusters[c].inRpy.Cmd := Putt;
  Clusters[c].inRpy.Dest := Clusters[c].outReq.Cluster;
  Clusters[c].inRpy.Data := Clusters[c].L1s[i].Data;

  assert Clusters[c].OnlyCopy = true;
  Clusters[c].OnlyCopy := false;

  Clusters[c].outReq.Cmd := None;
  undefine Clusters[c].outReq.Cluster;
end;
end;


ruleset c: CId do
rule "26 cluster send Put reply to another cluster"
  Clusters[c].inRpy.Cmd = Putt
==>
var dest: CId;
begin
  dest := Clusters[c].inRpy.Dest;

  GShWbMsg.Cmd := ShWb;
  GShWbMsg.Data := Clusters[c].inRpy.Data;
  GShWbMsg.Cluster := dest;

  GUniMsg[dest].Cmd := Putt;
  GUniMsg[dest].Data := Clusters[c].inRpy.Data;
  undefine GUniMsg[dest].Cluster;

  Clusters[c].inRpy.Cmd := None;
  undefine Clusters[c].inRpy.Dest;
end;
end;


ruleset c: CId do
rule "27 Cluster reply fwded excl req"
  Clusters[c].inRpy.Cmd = PutX
==>
var dest: CId;
begin
  dest := Clusters[c].inRpy.Dest;

  GShWbMsg.Cmd := DxFer;
  undefine GShWbMsg.Data;
  GShWbMsg.Cluster := dest;

  GUniMsg[dest].Cmd := PutX;
  GUniMsg[dest].Data := Clusters[c].inRpy.Data;
  -- GUniMsg[dest].InvCnt := 0;
  for c2: CId do
    GUniMsg[dest].ToInv[c2] := false;
  end;

  Clusters[c].inRpy.Cmd := None;
  undefine Clusters[c].inRpy.Dest;
end;
end;


rule "28 Global dir receive ShWb"
  GShWbMsg.Cmd = ShWb 
==>
var c: CId;
begin
  c := GShWbMsg.Cluster;

  GDir.State := Shrd;

  assert GDir.pending = true;
  GDir.pending := false;
  GDir.Mem := GShWbMsg.Data;
  GDir.ShrSet[c] := true;
  if (! isundefined(GDir.Owner)) then 
    GDir.ShrSet[GDir.Owner] := true;
    undefine GDir.Owner;
  end;

  GShWbMsg.Cmd := None;
  undefine GShWbMsg.Data;
  undefine GShWbMsg.Cluster;
end;


rule "29 Global dir receive DxFer"
  GShWbMsg.Cmd = DxFer
==>
begin
  assert GDir.pending = true;
  GDir.pending := false;

  GDir.Owner := GShWbMsg.Cluster;

  GShWbMsg.Cmd := None;
  undefine GShWbMsg.Data;
  undefine GShWbMsg.Cluster;
end;
 

ruleset c1: CId  do
rule "30 Cluster c1 sends NAck rpy to c2"
  Clusters[c1].inRpy.Cmd = NAck
==>
var c2: CId;
begin
  c2 := Clusters[c1].inRpy.Dest;

  GUniMsg[c2].Cmd := NAck;
  undefine GUniMsg[c2].Data;
  undefine GUniMsg[c2].Cluster;

  Clusters[c1].inRpy.Cmd := None;
  undefine Clusters[c1].inRpy.Dest;

  GShWbMsg.Cmd := NAck;
  undefine GShWbMsg.Cluster;
  undefine GShWbMsg.Data;
end;
end;


ruleset c: CId do
rule "31 Cluster receive NAck reply"
  GUniMsg[c].Cmd = NAck 
==>
  assert Clusters[c].RAC.Cmd != None;
  Clusters[c].RAC.Cmd := None;

  Clusters[c].outRpy.Cmd := NAck;

  GUniMsg[c].Cmd := None;
  Clusters[c].ReqCmd := None;
end;
end;


ruleset c: CId do
rule "32 Cluster receive Put reply"
  GUniMsg[c].Cmd = Putt  
==>
  assert Clusters[c].RAC.Cmd != None;
  Clusters[c].RAC.Cmd := None;

  Clusters[c].outRpy.Cmd := GUniMsg[c].Cmd;
  Clusters[c].outRpy.Data := GUniMsg[c].Data;

  GUniMsg[c].Cmd := None;
  undefine GUniMsg[c].Data;
  Clusters[c].ReqCmd := None;
end;
end;


ruleset c: CId do
rule "33 Cluster receive PutX reply"
  GUniMsg[c].Cmd = PutX 
==>
var cnt: ClusterRange;
begin
  
  assert Clusters[c].RAC.Cmd != None;
 
  cnt := 0;
  for c2: CId do
    Clusters[c].RAC.ToInv[c2] :=
            GUniMsg[c].ToInv[c2] & !Clusters[c].RAC.Inved[c2];
    Clusters[c].RAC.Inved[c2] := false;
    if (Clusters[c].RAC.ToInv[c2]) then
      cnt := cnt + 1;
    end;
  end;

--   if (forall c2: CId do !Clusters[c].RAC.ToInv[c2] end) then
  if (cnt > 0) then
    Clusters[c].RAC.Cmd := None;
  else
      Clusters[c].RAC.Cmd := WINV;
  end;

--  if (GUniMsg[c].InvCnt = 0) then
--    Clusters[c].RAC.Cmd := None;
--  else
--    Clusters[c].RAC.InvCnt := GUniMsg[c].InvCnt - Clusters[c].RAC.InvCnt;
--    if (Clusters[c].RAC.InvCnt > 0) then
--      Clusters[c].RAC.Cmd := WINV;
--    else
--      Clusters[c].RAC.Cmd := None;
--    end;
--  end;

  Clusters[c].outRpy.Cmd := GUniMsg[c].Cmd;
  Clusters[c].outRpy.Data := GUniMsg[c].Data;

  GUniMsg[c].Cmd := None;
  undefine GUniMsg[c].Data;
  Clusters[c].ReqCmd := None;
end;
end;


ruleset c: CId do
rule "34 Cluster receive NAck, reset pending"
  Clusters[c].outRpy.Cmd = NAck
==>
  assert Clusters[c].L2.pending = true;
  Clusters[c].L2.pending := false;

  Clusters[c].outRpy.Cmd := None;
end;
end;


ruleset c: CId do
rule "35 Cluster receive Put reply"
  Clusters[c].outRpy.Cmd = Putt
==>
  assert Clusters[c].L2.pending = true;
  Clusters[c].L2.pending := false;

  Clusters[c].L2.Data := Clusters[c].outRpy.Data;
  Clusters[c].L2.State := Shrd;
  Clusters[c].OnlyCopy := false;

  Clusters[c].outRpy.Cmd := None;
end;
end;


ruleset c: CId do
rule "36 Cluster receive PutX reply"
  Clusters[c].outRpy.Cmd = PutX
==>
  assert Clusters[c].L2.pending = true;
  Clusters[c].L2.pending := false;

  Clusters[c].L2.Data := Clusters[c].outRpy.Data;
  Clusters[c].L2.State := Excl;
  Clusters[c].OnlyCopy := true;

  Clusters[c].outRpy.Cmd := None;
end;
end;


ruleset c: CId do
rule "37 Cluster req excl copy, global dir shrd"
  GUniMsg[c].Cmd = GetX &
  GDir.pending = false &
  GDir.State = Shrd &
  exists i: CId do
    GDir.ShrSet[i] = true
  end
==>
-- var cnt: ClusterRange;
begin
  GUniMsg[c].Cmd := PutX;
  GUniMsg[c].Data := GDir.Mem;
  GDir.State := Excl;
  GDir.Owner := c;

  -- cnt := 0;
  for i: CId do
    if GDir.ShrSet[i] = true then
      GDir.ShrSet[i] := false;

      if (i != c) then
        GInvMsg[i].Cmd := Inv;
        GInvMsg[i].Cluster := c;
        GUniMsg[c].ToInv[i] := true;
        -- cnt := cnt + 1;
      end;
    end;
  end;

  -- GUniMsg[c].InvCnt := cnt;
end;
end;


ruleset c: CId do
rule "38 Cluster receive Inv"
  GInvMsg[c].Cmd = Inv
==>
  GInvMsg[c].Cmd := None;
  Clusters[c].outReq.Cmd := Inv;
  Clusters[c].outReq.Cluster := GInvMsg[c].Cluster;
end;
end;


ruleset c: CId do
rule "38-1 Cluster reply InvAck"
  Clusters[c].inRpy.Cmd = InvAck
==>
  GInvMsg[c].Cmd := InvAck;
  GInvMsg[c].Cluster := Clusters[c].inRpy.Dest;

  Clusters[c].inRpy.Cmd := None;
  undefine Clusters[c].inRpy.Dest;
end;
end;


ruleset c1: CId; c2: CId do
rule "39 Cluster receive InvAck (from c1)"
  GInvMsg[c1].Cmd = InvAck &
  ! isundefined(GInvMsg[c1].Cluster) &
  GInvMsg[c1].Cluster = c2 &
  Clusters[c2].RAC.Cmd != WINV
==>
  -- Clusters[c2].RAC.InvCnt := Clusters[c2].RAC.InvCnt + 1;
  Clusters[c2].RAC.Inved[c1] := true;
  GInvMsg[c1].Cmd := None;
  undefine GInvMsg[c1].Cluster;
end;
end;


ruleset c1: CId; c2: CId do
rule "40 Cluster receive InvAck (from c1)"
  GInvMsg[c1].Cmd = InvAck &
  GInvMsg[c1].Cluster = c2 &
  Clusters[c2].RAC.Cmd = WINV
==>
var cnt: ClusterRange;
begin
  -- Clusters[c2].RAC.InvCnt := Clusters[c2].RAC.InvCnt - 1;
  Clusters[c2].RAC.ToInv[c1] := false;
  --  if Clusters[c2].RAC.InvCnt = 0 then
  --    Clusters[c2].RAC.Cmd := None;
  --  end;
  cnt := 0;
  for c: CId do
    if (Clusters[c2].RAC.ToInv[c]) then
      cnt := cnt + 1;
    end;
  end;
  
  -- if (forall c: CId do !Clusters[c2].RAC.ToInv[c] end) then
  if (cnt = 0) then
    Clusters[c2].RAC.Cmd := None;
  end;

  GInvMsg[c1].Cmd := None;
  undefine GInvMsg[c1].Cluster;
end;
end;


ruleset c: CId do
rule "41 Cluster write back cache copy"
  Clusters[c].L2.State = Excl &
  Clusters[c].L2.pending = false
==>
  Clusters[c].WbReq.Cmd := WB;
  Clusters[c].WbReq.Data := Clusters[c].L2.Data;
  Clusters[c].L2.State := Invld;
  undefine Clusters[c].L2.Data;
  Clusters[c].OnlyCopy := false;
end;
end;


ruleset c: CId do
rule "42 Cluster write back cache copy"
  Clusters[c].WbReq.Cmd = WB 
/* comment the following is our inserted bug */
  &
  Clusters[c].RAC.Cmd = None
==>
  GWbMsg.Cmd := WB;
  GWbMsg.Data := Clusters[c].WbReq.Data;
  GWbMsg.Cluster := c;

  Clusters[c].WbReq.Cmd := None;
  undefine Clusters[c].WbReq.Data;
end;
end;


rule "43 Global dir receive writeback"
  GWbMsg.Cmd = WB
==>
  GDir.Mem := GWbMsg.Data;
  GDir.State := Invld;
  undefine GDir.Owner;

  GWbMsg.Cmd := None;
  undefine GWbMsg.Data;
  undefine GWbMsg.Cluster;
end;


ruleset c: CId do
rule "44 Cluster invalidate itself"
  Clusters[c].outReq.Cmd = Inv
==>
  for i: L1Id do
    Clusters[c].L1s[i].State := Invld;
    undefine Clusters[c].L1s[i].Data;
  end;

  Clusters[c].L2.State := Invld;
  undefine Clusters[c].L2.Data;

  Clusters[c].inRpy.Cmd := InvAck;
  Clusters[c].inRpy.Dest := Clusters[c].outReq.Cluster;
  undefine Clusters[c].inRpy.Data;

  Clusters[c].outReq.Cmd := None;
  undefine Clusters[c].outReq.Cluster;
end;
end;


invariant "I1"
forall c: CId do
  forall i: L1Id do
    forall j: L1Id do
      i != j ->
      ! (Clusters[c].L1s[i].State = Excl & 
	 Clusters[c].L1s[j].State = Excl)
    end &
    ! (Clusters[c].L2.State = Excl &
       Clusters[c].L1s[i].State = Excl)
  end
end;


invariant "I2"
forall c1: CId do
forall c2: CId do
  c1 != c2
->
  forall i: L1Id do
    forall j: L1Id do
      ! (Clusters[c1].L1s[i].State = Excl & 
	 Clusters[c2].L1s[j].State = Excl)
    end &
    ! (Clusters[c1].L2.State = Excl &
       Clusters[c2].L1s[i].State = Excl) &
    ! (Clusters[c1].L2.State = Excl &
       Clusters[c2].L2.State = Excl)
  end
end
end;


invariant "I3"
  GDir.State = Shrd 
->
  GDir.Mem = SysData;


invariant "I4"
forall c: CId do
  forall i: L1Id do
    Clusters[c].L1s[i].State = Excl 
    ->
    Clusters[c].L1s[i].Data = SysData
  end &
  Clusters[c].L2.State = Excl
  ->
  Clusters[c].L2.Data = SysData
end;
