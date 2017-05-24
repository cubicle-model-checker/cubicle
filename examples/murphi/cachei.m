/* ------------------------------------------------------------------------ */
/* DOCUMENTATION                                                     */
/* ------------------------------------------------------------------------ */
/**@file

   Architecture-level protocol model by Steven German and Geert Janssen
   Steven German  4   June 2004 - original write-up (cachei.m)
   Geert Janssen  4 August 2004 - simplified and improved version
*/

/* ------------------------------------------------------------------------ */
/* CONSTANTS */
/* ------------------------------------------------------------------------ */

/**Constants that determine "size" of the problem. */
const num_nodes: 2; /**<number of processing nodes */
const num_addr:  1; /**<number of memory addresses  */
const num_data:  1; /**<number of data bits per address */

/* ------------------------------------------------------------------------ */
/* TYPES                                             */
/* ------------------------------------------------------------------------ */

/**The communication channel ids. */
const channel1: 1;
const channel2: 2;
const channel3: 3;

/**Message types. */
type opcode: enum {
  op_invalid,-- clear
  read_shared,
  read_exclusive,
  req_upgrade,
  invalidate,
  invalidate_ack,
  grant_shared,
  grant_upgrade,
  grant_exclusive
};

/**Memory access message types. */
type request_opcode: enum {
  req_read_shared,-- clear
  req_read_exclusive,
  req_req_upgrade
};

/**Cache states. */
type cache_state: enum {
  cache_invalid,-- clear
  cache_shared,
  cache_exclusive
};

/**Address range. */
type addr_type: 0..num_addr-1; -- clear 0

/**Memory content at an address. */
type data_type: array[0..num_data-1] of boolean; -- clear [false,...]

/**A cache line. */
type cache_record:
record
  state: cache_state; -- clear cache_invalid
  data:  data_type; -- clear [false,...]
end;

/**Node id range. */
type node_id: 0..num_nodes-1; -- clear 0

/**Channel ids. */
type channel_id: 1..3; -- clear 1

/**A message. */
type message_type:
record
  source: node_id; /**<originator, clear 0 */
  dest:   node_id; /**<destination, clear 0 */
  op:     opcode; /**<message type, clear op_invalid */
  addr:   addr_type; /**<address involved, clear 0 */
  data:   data_type; /**<data value, clear [false,...] */
end;

/**Buffer for a message. */
type message_buf_type:
record
  msg:   message_type; -- clear see message_type
  valid: boolean; -- clear false
end;

/**Status of a request message. */
type status_type: enum {
  inactive,-- clear
  pending,
  completed
};

type addr_request_type:
record
  --   addr: addr_type; NOTE requests are indexed by address
  home:   node_id; -- clear 0
  op:     opcode; -- clear op_invalid
  data:   data_type; -- clear [false,...]
  status: status_type; -- clear inactive
end;

type line_dir_type: array[node_id] of cache_state; -- clear [cache_invalid,..]

type node_bool_array: array[node_id] of boolean; -- clear [false,...]

type home_request_type:
record
  source: node_id; -- clear 0
  op:     opcode; -- clear op_invalid
  data:   data_type; -- clear [false,...]
  invalidate_list: node_bool_array; -- clear [false,...]
  status: status_type; -- clear inactive
end;

type node_type:
record
  memory:          array[addr_type] of data_type;
  cache:           array[addr_type] of cache_record;
  directory:       array[addr_type] of line_dir_type;
  local_requests:  array[addr_type] of boolean;
  home_requests:   array[addr_type] of home_request_type;
  remote_requests: array[addr_type] of addr_request_type;
  inchan:          array[channel_id] of message_buf_type;
  outchan:         array[channel_id] of message_buf_type;
end;

/* ------------------------------------------------------------------------ */
/* VARIABLES */
/* ------------------------------------------------------------------------ */

/**Global state of the system. */
var node: array[node_id] of node_type;

/* ------------------------------------------------------------------------ */
/* FUNCTIONS */
/* ------------------------------------------------------------------------ */

/**Returns the id of the node that controls this memory address. */
function home_node(a: addr_type): node_id;
begin
  return a = 0 ? 0 : 1;
end;

/**Casts a requests code into a more general message op code. */
function req_opcode(req: request_opcode): opcode;
begin
switch req
case req_read_shared:    return read_shared;
case req_read_exclusive: return read_exclusive;
case req_req_upgrade:    return req_upgrade;
endswitch;
end;

/**Returns smallest node id indexing a true entry in ‘a’. */
function first_node_in_vector(a: node_bool_array): node_id;
begin
for i: node_id do
  if a[i] then
  return i;
endif;
endfor; end;

/**Expresses the required invariant of the system:
   1. Can have at most 1 node having exclusive access to a certain address.
   2. If there’s a node with exclusive access, no other may have shared access.
*/
function check_invariants(): boolean;
var n_exclusive, n_shared: 0..num_nodes;
begin
for addr: addr_type do
  n_exclusive := 0;
  n_shared := 0;
  for n: node_id do
    switch node[n].cache[addr].state
      case cache_invalid:   -- do nothing
      case cache_shared:    n_shared    := n_shared + 1;
      case cache_exclusive: n_exclusive := n_exclusive + 1;
    endswitch;
  endfor;
  if n_exclusive > 1 then
    put "VIOLATION:\n\t[check_invariants]: two or more exclusive caches\n";
    return false;
  elsif n_exclusive > 0 & n_shared != 0 then
    put "VIOLATION:\n\t[check_invariants]: exclusive and shared caches\n";
    return false;
  endif;
endfor;
return true;
end;

/* Print opcode. Useful in debugging. */
procedure put_op_name(op:opcode);
begin
switch op
case op_invalid: put "invalid";
case read_shared: put "shared";
case read_exclusive: put "exclusive";
case req_upgrade: put "upgrade";
case invalidate: put "invalidate";
case invalidate_ack: put "invalidate_ack";
case grant_shared: put "grant_shared";
case grant_upgrade: put "grant_upgrade";
case grant_exclusive: put "grant_exclusive";
endswitch;
end;

/* ------------------------------------------------------------------------ */
/* START STATE(S)                                                           */
/* ------------------------------------------------------------------------ */

/**Start state of the system; all data takes on its "smallest" value. */
startstate
  clear node;
end;

/* ------------------------------------------------------------------------ */
/* RULES      */
/* ------------------------------------------------------------------------ */

/************************************/
/* Message transfer between nodes   */
/************************************/
ruleset source: node_id; ch: channel_id do
  alias outchan: node[source].outchan[ch];
  dest:    outchan.msg.dest;
  inchan:  node[dest].inchan[ch] do
--
rule "Transfer message from ‘source’ via ‘ch’"
-- must have valid message to transfer at source:
  outchan.valid
-- must have empty message input buffer available at destination:
& !inchan.valid  ==>

begin
  assert source = outchan.msg.source "message must come from source";
  assert outchan.msg.op != op_invalid "message type must be valid";
  inchan := outchan;
  -- now inchan.valid = true
  clear outchan;
  --outchan.valid := false; (implied by clear outchan, GJ04)
endrule;
endalias; endruleset;


/************************************/
/* Node activities in "client" mode */
/************************************/
ruleset client: node_id; req: request_opcode; addr: addr_type do
  alias cache_state: node[client].cache[addr].state;
        outchan:     node[client].outchan[channel1];
local_request_for_addr: node[client].local_requests[addr];
home:        home_node(addr) do
--
rule "‘client’ generates new ‘req’ for ‘addr’"
-- can’t ask for same address if prior request hasn’t been completed:
  !local_request_for_addr
-- can only ask for what we don’t already have:
& ((req = req_read_shared    & cache_state = cache_invalid) |
   (req = req_read_exclusive & cache_state = cache_invalid) |
   (req = req_req_upgrade    & cache_state = cache_shared))
-- must have an empty output channel message buffer:
& !outchan.valid ==>
begin
  put ">> client ";
  put client;
  put " issues ";
  put_op_name(req_opcode(req));
  put " request for addr ";
  put addr;
  put "\n";

  alias msg: outchan.msg do
    -- Prepare the request message:
    msg.source := client;
    msg.dest := home_node(addr);
    msg.op := req_opcode(req);
    msg.addr := addr;
    outchan.valid := true;
    -- Assure at most 1 request at a time:
    local_request_for_addr := true;
  endalias;
endrule;
endalias; endruleset;


ruleset client: node_id do
  alias inchan:  node[client].inchan[channel2];
  inmsg:   inchan.msg;
  addr:    inmsg.addr;
  request: node[client].remote_requests[addr] do
--
rule "‘client’ accepts invalidate request"
-- must have valid data in the input message buffer:
  inchan.valid
-- only processing invalidate type of messages:
& inmsg.op = invalidate
-- must be a unique request:
& request.status = inactive ==>
begin
  assert inmsg.source = home_node(addr) "message source must be addr home";
  -- this indeed can happen for upgrade requests:
  --  assert !node[client].local_requests[addr]
  --  "client gets invalidation while has request pending";
  request.home   := inmsg.source;
  request.op     := inmsg.op /*= invalidate*/;
  /*request.data   := don’t care on input/filled in when ack;*/
  request.status := pending;
  clear inchan;
endrule;
endalias; endruleset;


ruleset client: node_id; addr: addr_type do
  alias request: node[client].remote_requests[addr] do
  --
  rule "‘client’ processes invalidate request for ‘addr’"
  -- must have a pending invalidation request:
  request.status = pending
  & request.op = invalidate ==>
begin
  put "<< client ";
  put client;
  put " invalidates cache for addr ";
  put addr;
  put "\n";

  alias cache_line: node[client].cache[addr] do
    -- currently cached data is saved in request message:
    request.data := cache_line.data;
    clear cache_line;
    -- Here: cache_line.state = cache_invalid
    request.status := completed;
  endalias;
endrule;
endalias; endruleset;


ruleset client: node_id; addr: addr_type do
  alias request: node[client].remote_requests[addr];
  outchan: node[client].outchan[channel3] do
--

rule "‘client’ prepares invalidate ack for ‘addr’"
  -- just completed a invalidation action:
  request.status = completed
& request.op = invalidate
-- have an empty output message buffer available:
& !outchan.valid ==>
begin
  put ">> client ";
  put client;
  put " prepares invalidate ack for addr ";
  put addr;
  put "\n";
  assert request.home = home_node(addr) "dest must addr home";

  alias msg: outchan.msg do
    msg.op     := invalidate_ack;
    msg.source := client;
    msg.dest   := request.home;
    msg.data   := request.data;
    msg.addr   := addr;
    outchan.valid := true;
    clear request;
  endalias;
endrule;
endalias; endruleset;



ruleset client: node_id do
  alias inchan: node[client].inchan[channel2];
        msg:    inchan.msg;
        op:     msg.op;
        addr:   msg.addr;
        home:   home_node(addr);
        data:   msg.data do
--


rule "‘client’ receives reply from home"
-- have valid data in message input buffer:
  inchan.valid
-- message concerns grant:
  & (op = grant_shared | op = grant_upgrade | op = grant_exclusive) ==>
begin
assert msg.source = home "source must match addr home";
alias cache_line:    node[client].cache[addr];
      local_request_for_addr: node[client].local_requests[addr];
      state:         node[home].directory[addr][client] do
-- update the cache, unless the request was handled locally by
-- home = client

  put "<< client ";
  put client;
  put " receives ";
  put_op_name(op);
  put " for addr ";
  put addr;

  switch op
  case grant_shared:
    cache_line.data  := msg.data;
    cache_line.state := cache_shared;
  case grant_upgrade:
    -- data in cache is still valid.
    cache_line.state := cache_exclusive;
  case grant_exclusive:
    cache_line.data  := msg.data;
    cache_line.state := cache_exclusive;
  endswitch;
  assert state = cache_line.state
  "home directory record must reflect actual client state";
  -- indicate we can start issuing new requests:
  assert local_request_for_addr "must have local_request true";
  local_request_for_addr := false;
  clear inchan;
endalias;
endrule;
endalias; endruleset;



/**********************************/
/* Node activities in "home" mode */
/**********************************/
ruleset home: node_id do
  alias inchan:  node[home].inchan[channel1];
        msg:     inchan.msg;
        valid:   inchan.valid;
        addr:    msg.addr;
        request: node[home].home_requests[addr] do
--


rule "‘home’ accepts a request message"
-- have valid message input buffer:
  valid
-- not handling another request for this address yet:
& request.status = inactive ==>
var b, invalidations: boolean;
var k: node_id;
var count: 0..num_nodes;
begin
alias op:         msg.op;
      directory:  node[home].directory[addr];
      source:     msg.source;
      cache_line: node[home].cache[addr];
      memory:     node[home].memory[addr] do

put "<< home ";
put home;
put " accepts ";
put_op_name(op);
put " request for ";
put addr;

-- In case of an upgrade request that got its cached data invalidated
-- by another request, we simply treat that upgrade as an exclusive:
if op = req_upgrade & directory[source] = cache_invalid then
  op := read_exclusive;
endif;

request.source := source;
request.op := op;

-- Now we decide how to process the request.

-- 1. If request is shared and cached shared locally,
-- just read from home cache, update directory, and send grant.
if op = read_shared & directory[home] = cache_shared then
  put "protocol rule 1: send shared from home cache\n";
  assert !exists n:node_id do directory[n] = cache_exclusive endexists
  "1. no exclusive cache";
  assert source != home "1. source cannot be home";
  -- get data from my/home cache:
  request.data   := cache_line.data;
  request.status := completed;

-- 2. If request is shared and not cached locally and directory shows
-- no exclusive copy, read from memory, send shared copy.
elsif op = read_shared & directory[home] = cache_invalid
    & !exists n:node_id do directory[n] = cache_exclusive endexists then
  put "protocol rule 2: send shared from memory\n";
  -- get data from memory:
  request.data   := memory;
  request.status := completed;


-- 5. If request is shared and there is an exclusive copy
-- then invalidate copy and get data from that cache.
-- home could be exclusive!
elsif op = read_shared &
exists n:node_id do directory[n] = cache_exclusive endexists then
    put "protocol rule 5: invalidate exclusive copy\n";
    -- determine who needs to be invalidated:
    count := 0;
    for n:node_id do
      b := directory[n] != cache_invalid;
      if b then
        count := count + 1;
        k := n;
      endif;
      request.invalidate_list[n] := b;
    endfor;
    assert count = 1 "5. single non-invalid";
    assert directory[k] = cache_exclusive "5. must be exclusive";
    -- mark status of request as pending (must first do invalidation):
    put "protocol rule 5: pending...1 invalidation needed\n";
    request.status := pending;


-- 6a. If request is upgrade and there are any other shared copies
-- invalidate local+remote copies, send data exclusive to requestor.
elsif (op = req_upgrade) then
  put "protocol rule 6a: upgrade request, invalidate any shared copies\n";
  assert directory[source] = node[source].cache[addr].state
    "6a. directory record must reflect actual source state";
  assert directory[source] = cache_shared
    "6a. directory must reflect source shared";
  -- see whether others (!= source) must be invalidated (no exclusive!):
  invalidations := false;
  for n: node_id do
    b := directory[n] != cache_invalid & n != source;
    invalidations := b | invalidations;
    request.invalidate_list[n] := b;
  endfor;
  -- A true upgrade: (shared) data in cache is still assumed valid.
  if invalidations then
    put "protocol rule 6a: pending...invalidations needed\n";
    request.status := pending;
  else
    request.status := completed;
  endif;


-- 6b. If request is exclusive and there are any cached copies
-- invalidate local+remote copies, send data exclusive to requestor.
elsif (op = read_exclusive) then
  put "protocol rule 6b: exclusive request, invalidate any copies\n";
  assert directory[source] = cache_invalid "6b. requestor must have invalid";
  -- determine if any and who needs to be invalidated
  -- source must be cache_invalid already
  invalidations := false;
  for n: node_id do
    b := directory[n] != cache_invalid;
    invalidations := b | invalidations;
    request.invalidate_list[n] := b;
  endfor;
  if invalidations then
    put "protocol rule 6b: pending...invalidations needed\n";
    -- data comes from a node that gets invalidated.
    request.status := pending;
  else
    put "protocol rule 6b: send exclusive from memory\n";
    request.data   := memory;
    request.status := completed;
  endif;

-- 7. If not one of the above cases, error.
else
  error "undefined case";
endif;

-- clear the request message
  clear inchan;

  endalias;
endrule;
endalias; endruleset;


ruleset home: node_id; addr: addr_type do
  alias request: node[home].home_requests[addr];
out:     node[home].outchan[channel2];
outmsg:  out.msg do
--

rule "‘home’ prepares invalidate for ‘addr’"
-- request is still pending:
  request.status = pending
-- we must have something to invalidate:
& exists n:node_id do request.invalidate_list[n] endexists
-- we have an empty message output buffer available:
& !out.valid  ==>
var dest: node_id;
begin
  outmsg.addr   := addr;
  outmsg.op     := invalidate;
  outmsg.source := home;
  dest := first_node_in_vector(request.invalidate_list);
  outmsg.dest   := dest;
  out.valid := true;
  request.invalidate_list[dest] := false;
endrule;
endalias; endruleset;


ruleset home: node_id do
alias inchan: node[home].inchan[channel3];
      inmsg: inchan.msg;
      addr: inmsg.addr;
      request: node[home].home_requests[addr];
      source: inmsg.source;
      directory: node[home].directory[addr] do
--

rule "‘home’ processes invalidate ack"
-- we have a valid message input buffer:
  inchan.valid
-- request is still pending:
& request.status = pending
-- message acknowledges an earlier invalidate request:
& inmsg.op = invalidate_ack ==>
begin

  put "<< home ";
  put home;
  put " processes invalidate ack for ";
  put addr;

  -- if invalidating exclusive cache, save data in request and memory
  if directory[source] = cache_exclusive then
    -- write message data back to memory:
    node[home].memory[addr] := inmsg.data;
  endif;
  /* Even if just shared must get data to requestor GJ04 */
  -- same data will be send to requestor:
  request.data := inmsg.data;
  
  assert node[source].cache[addr].state = cache_invalid
    "source must have invalid cache";
  directory[source] := cache_invalid;

  clear inchan;
  -- try to mark request as completed:

  switch request.op
  case read_shared:
    -- just invalidated an exclusive; done.
    request.status := completed;
   case req_upgrade:
     if forall n: node_id do
       n != request.source -> directory[n] = cache_invalid endforall then
       request.status := completed;
     endif;
    case read_exclusive:
      if forall n: node_id do directory[n] = cache_invalid endforall then
        request.status := completed;
      endif;
      else error "unexpected request opcode";
  endswitch;
endrule;
endalias; endruleset;


ruleset home: node_id; addr: addr_type do
  alias request: node[home].home_requests[addr];
        outchan: node[home].outchan[channel2];
        msg:     outchan.msg do
--

rule "‘home’ sends grant for ‘addr’"
  request.status = completed
& !outchan.valid ==>
begin
  msg.source := home;
  msg.dest   := request.source;
  switch request.op
  case read_shared:    msg.op := grant_shared;
    node[home].directory[addr][request.source] := cache_shared;
  case req_upgrade:    msg.op := grant_upgrade;
    node[home].directory[addr][request.source] := cache_exclusive;
  case read_exclusive: msg.op := grant_exclusive;
    node[home].directory[addr][request.source] := cache_exclusive;
  endswitch;

  msg.data := request.data;
  msg.addr := addr;
  clear request;
  outchan.valid := true;
endrule;
endalias; endruleset;

/* ------------------------------------------------------------------------ */
/* CHECKS      */
/* ------------------------------------------------------------------------ */

invariant check_invariants();
