const  ---- Configuration parameters ----
       
  PROC_NUM : 5;

type   ---- Type declarations ----

  PROC : 1 .. PROC_NUM;
  PROC_Id : -1 .. PROC_NUM;
  PROC_MaxId : -2 .. PROC_NUM;

var   ---- State variables ----

  Round : 1 .. 8;
  Estimate : array [PROC] of boolean;
  State : array [PROC] of boolean;
  Coord : array [PROC] of boolean;
  ACoord : array [PROC] of boolean;
  Done : array [PROC] of boolean;
  Request : boolean;
  DecisionValue : array [PROC] of boolean;
  Faulty : array [PROC] of boolean;
  Received : array [PROC] of boolean;
  Nack : array [PROC] of boolean;
  Id : array [PROC] of PROC_Id;
  MaxId : PROC_MaxId;
  TmpEstimate : boolean;
  ProcessReceivedEstimate : array [PROC] of boolean;

---- Initial states ----

ruleset e:boolean; d:boolean; f:boolean; p:boolean; r:boolean; t:boolean do startstate "Init"
  for x : PROC do
    State[x] := false;
    Coord[x] := false;
    ACoord[x] := false;
    Done[x] := false;
    Received[x] := false;
    Nack[x] := false;
    Id[x] := -1;
    --- ???
    Estimate[x] := e;
    DecisionValue[x] := d;
    Faulty[x] := f;
    ProcessReceivedEstimate[x] := p;
  end;
  Round := 1;
  MaxId := -2;
  --- ???
  Request := r;
  TmpEstimate := t;
end end;


-- 1) Decided processes send request to coordinator if their id are greather than maxId

ruleset x : PROC; y : PROC do rule "t1"
  x != y & Round = 1 & Done[x] = false & State[x] = false &
  Coord[y] = true & Id[x] > MaxId
==>
  Done[x] := true;
  MaxId := Id[x];
  TmpEstimate := Estimate[x];
end end;


-- 2) Undecided processes want to send a request, but their id is less or equal than maxId
      
ruleset x : PROC; y : PROC do rule "t2"
  x != y & Round = 1 & Done[x] = false & State[x] = false &
  Coord[y] = true & Id[x] <= MaxId
==>
  Done[x] := true;
end end;


-- 3) An undecided faulty process fails sending a request 
       
ruleset x : PROC; y : PROC do rule "t3"
  x != y & Round = 1 & Done[x] = false & State[x] = false &
  Coord[y] = true & Faulty[x] = true
==>
  Done[x] := true;
end end;

      
-- 4) An undecided coordinator (with id > maxId) sends a request (to himself)
       
ruleset x : PROC do rule "t4"
  Round = 1 & Done[x] = false & State[x] = false &
  Coord[x] = true & Id[x] > MaxId
==>
  Done[x] := true;
  MaxId := Id[x];
  TmpEstimate := Estimate[x];
end end;


-- 5) An undecided coordinator (with id <= maxId) doesn't send a request to himself
  
ruleset x : PROC do rule "t5"
  Round = 1 & Done[x] = false & State[x] = false &
  Coord[x] = true & Id[x] <= MaxId
==>
  Done[x] := true;
end end;


-- 6) Decided processes do nothing
  
ruleset x : PROC do rule "t6"
  Round = 1 & Done[x] = false & State[x] = true
==>
  Done[x] := true;
end end;


-- 7) If all processes have completed the 1st round and the coordinator
--    received a request (i.e. maxId > -2), the coordinator set his estimate
--    to tmpEstimate value and all the processes go to 2nd round 
  
ruleset x : PROC do rule "t7"
  Round = 1 & MaxId > -2 & Done[x] = true & Coord[x] = true &
  forall j : PROC do (Done[j] = true) end
==>
  Round := 2;
  for j : PROC do Done[j] := false end;
  Estimate[x] := TmpEstimate;
end end;


-- 8) ... otherwise (no request have been received by the coordinator)
--    the coordinator is dismissed.
      
ruleset x : PROC do rule "t8"
  Round = 1 & MaxId = -2 & Done[x] = true & Coord[x] = true &
  forall j : PROC do (Done[j] = true) end
==>
  Coord[x] := false;
  ACoord[x] := true;
end end;

      
-- 9) An undecided process receives the estimate from the coordinator.
       
ruleset x : PROC; y : PROC do rule "t9"
  x != y & Round = 2 & Done[x] = false & State[x] = false & Coord[y] = true
==>
  Estimate[x] := Estimate[y];
  Done[x] := true;
  Received[x] := true;
  Id[x] := y;
  ProcessReceivedEstimate[x] := true;
end end;

      
-- 10) A faulty coordinator fails sending an estimate      

ruleset x : PROC; y : PROC do rule "t10"
  x != y & Round = 2 & Done[x] = false & State[x] = false &
  Coord[y] = true & Faulty[y] = true
==>
  Done[x] := true;
end end;

       
-- 11) If the coordinator is undecided sends an estimate to himself

ruleset x : PROC do rule "t11"
  Round = 2 & Done[x] = false & State[x] = false & Coord[x] = true
==>
  Done[x] := true;
  Received[x] := true;
  Id[x] := x;
  ProcessReceivedEstimate[x] := true;
end end;


-- 12) Decided processes do nothing
       
ruleset x : PROC do rule "t12"
  Round = 2 & Done[x] = false & State[x] = true
==>
  Done[x] := true;
end end;


-- 13) Round 2 completed. System goes to round 3.
    
ruleset x : PROC do rule "t13"
  Round = 2 & Done[x] = true & Coord[x] = true &
  forall j : PROC do (Done[j] = true) end
==>
  Round := 3;
  for j : PROC do Done[j] := false end;
end end;


-- 14) If an undecided process didn't received the estimate sends a nack to coord
       
ruleset x : PROC; y : PROC do rule "t14"
  x != y & Round = 3 & Done[x] = false & State[x] = false &
  Coord[y] = true & Received[x] = false
==>
  Done[x] := true;
  Nack[y] := true;
end end;


-- 15) An undecided faulty process that didn't received the estimate
--     fails sending the nack to the coordinator

ruleset x : PROC; y : PROC do rule "t15"
  x != y & Round = 3 & Done[x] = false & State[x] = false &
  Coord[y] = true & Received[x] = false & Faulty[x] = true
==>
  Done[x] := true;
end end;

    
-- 16) An undecided faulty process that didn't received the estimate
--     fails sending the nack to the coordinator

ruleset x : PROC; y : PROC do rule "t16"
  x != y & Round = 3 & Done[x] = false & State[x] = false &
  Coord[y] = true & Received[x] = true
==>
  Done[x] := true;
end end;
                                 
    
-- 17) the coordinator does nothing in this round
                                            
ruleset x : PROC do rule "t17"
  Round = 3 & Done[x] = false & Coord[x] = true
==>
  Done[x] := true;
end end;


-- 18) decided processes do nothing in this round
                                            
ruleset x : PROC; y : PROC do rule "t18"
  x != y & Round = 3 & Done[x] = false & State[x] = true &
  Coord[y] = true
==>
  Done[x] := true;
end end;


-- 19) When all the processes have done, system goes to the 4th round.

ruleset x : PROC do rule "t19"
  Round = 3 & Done[x] = true & Coord[x] = true &
  forall j : PROC do (Done[j] = true) end
==>
  Round := 4;
end end;

        
-- 20) If no nacks have been received, system goes to the 5th round (if the coordinator
--     received one (or more) nack, he is killed by the system)

ruleset x : PROC do rule "t20"
  Round = 4 & Coord[x] = false &
  forall j : PROC do (Nack[j] = false) end
==>
  Round := 5;
  for j : PROC do Done[j] := false end;
end end;

                                                               
-- 21) Coordinator sends a decide to an undecided process
                                            
ruleset x : PROC; y : PROC do rule "t21"
  x != y & Round = 5 & Done[x] = false & State[x] = false &
  Coord[y] = true
==>
  State[x] := true;
  Done[x] := true;
  DecisionValue[x] := Estimate[x];
end end;


-- 22) A faulty coordinator fails sending the message
       
ruleset x : PROC; y : PROC do rule "t22"
  x != y & Round = 5 & Done[x] = false & State[x] = false &
  Coord[y] = true & Faulty[y] = true
==>
  Done[x] := true;
end end;


-- 23) A faulty coordinator sends a decide to himself
       
ruleset x : PROC do rule "t23"
  Round = 5 & Done[x] = false & State[x] = false & Coord[x] = true
==>
  State[x] := true;
  Done[x] := true;
  DecisionValue[x] := Estimate[x];
end end;


-- 24) Coordinator sends a decide to decided processes
--     (but they ignore this message)
 
ruleset x : PROC do rule "t24"
  Round = 5 & Done[x] = false & State[x] = true
==>
  Done[x] := true;
end end;


-- 25) Round n. 5 completed. System goes to round 6.
       
ruleset x : PROC do rule "t25"
  Round = 5 & Done[x] = true & Coord[x] = true &
  forall j : PROC do (Done[j] = true) end
==>
  Round := 6;
  for j : PROC do Done[j] := false end;
end end;


-- 26) Coordinator in office is dismissed.
                      
ruleset x : PROC do rule "t26"
  Round = 6 & Coord[x] = true
==>
  Round := 7;
  Coord[x] := false;
  ACoord[x] := true;
end end;


-- 27) There's no coordinator! (maybe the coordinator crashed)

rule "t27"
  forall j : PROC do (Coord[j] = false) end
==>
  Round := 7;
end;


-- 28) In this round a new process is elected as coordinator of the system.
--     Then the system goes to 1st round.

ruleset x : PROC do rule "t28"
  Round = 7 & Coord[x] = false & ACoord[x] = false &
  forall j : PROC do (j >= x | (j < x & ACoord[j] = true)) end
==>
  Round := 1;
  Coord[x] := true;
  for j : PROC do
    Done[j] := false;
    Received[j] := false;
    Nack[j] := false;
  end;
  MaxId := -2;
end end;



-------------------------------- INVARIANTS ------------------------------

-- Exists only one coordinator in the system 
invariant "I1"
  forall x : PROC do forall y : PROC do
    x != y -> (Coord[x] = true -> Coord[y] = false)
  end end;

-- If 'c' is coordinator, all other process with id < c have already been coordinator
invariant "I2"
  forall x : PROC do forall y : PROC do
    y < x -> (Coord[x] = true -> ACoord[y] = true)
  end end;

-- A coordinator can't have id[] greater than his identificator
invariant "I3"
  forall x : PROC do
    Coord[x] = true -> Id[x] <= x
  end;

-- A process can't have id[] greater than coordinator's identificator
invariant "I4"
  forall x : PROC do forall y : PROC do
    x != y  -> (Coord[x] = true -> Id[y] <= x)
  end end;
       
-- In the first round a process can't have id[] equals to the coordinator's identificator
invariant "I5"
  forall x : PROC do forall y : PROC do
    x != y  -> ((Round = 1 & Coord[x] = true) -> Id[y] != x)
  end end;

-- A correct process can't receive any nack
invariant "I6"
  forall x : PROC do
    Faulty[x] = false -> Nack[x] = false
  end;

-- Coordinators are elected in order by identificator
invariant "I5"
  forall x : PROC do forall y : PROC do
    y > x  -> (Coord[x] = true -> ACoord[x] = false)
  end end;




invariant "LEMMA 2.1"
  forall x : PROC do forall y : PROC do forall z : PROC do
    (x != y & x != z & y != z) ->
    ((State[x] = true & Received[x] = true & Coord[y] = true &
      State[z] = false & Faulty[z] = false) -> Estimate[y] = Estimate[z])
  end end end;
         

invariant "LEMMA 2.2"
  forall x : PROC do forall y : PROC do
    x != y ->
    ((Round > 1 & State[x] = false & Faulty[x] = false &
      ProcessReceivedEstimate[x] = true & Coord[y] = true) -> Estimate[x] = Estimate[y])
  end end;
         

invariant "LEMMA 2.3"
  forall x : PROC do forall y : PROC do
    x != y ->
    ((Coord[x] = true & Faulty[x] = false & Round = 6 &
      State[y] = false) -> Faulty[y] = true)
  end end;
         

invariant "AGREEMENT - complete"
  forall x : PROC do forall y : PROC do
    x != y ->
    ((State[x] = true & Faulty[x] = false &
      State[y] = true & Faulty[y] = false) -> DecisionValue[x] = DecisionValue[y])
  end end;
         

